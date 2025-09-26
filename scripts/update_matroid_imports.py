#!/usr/bin/env python3
"""
Update Matroid.lean import list to include every .lean file under the Matroid/ directory.

Behavior:
- Treat existing lines of the form `import Matroid.xxx` and `-- import Matroid.xxx` as entries already present.
- Discover all `.lean` files recursively under the `Matroid/` directory and map each to a module name `Matroid.<path.with.dots>`.
- For any discovered module missing from `Matroid.lean`, add an active `import Matroid.xxx` line.
- Re-write `Matroid.lean` as a list of import lines sorted alphabetically by module name (commented state preserved for previously-present entries).
- By default, ignore modules matching any regex in `.matroidignore` located next to this script; pass `--all` to include everything.
- With `--uncomment`, test each commented import (`-- import Matroid.xxx`) by running `lake env lean` on the corresponding file. If the file compiles successfully (no output), uncomment the import.

Usage:
    python scripts/update_matroid_imports.py [--root <repo_root>] [--dry-run] [--comment] [--uncomment] [--workers <num>] [--all]

Defaults assume this script is located at `<repo_root>/scripts/`.
"""
from __future__ import annotations

import argparse
import os
import re
import subprocess
import sys
from concurrent.futures import ThreadPoolExecutor, as_completed
from pathlib import Path
from typing import Dict, Iterable, List, Set, Tuple

IMPORT_RE = re.compile(r"^\s*(--\s*)?import\s+(Matroid\.[\w\.'-]+)\s*$")


def load_ignore_patterns(ignore_file: Path) -> List[re.Pattern[str]]:
    patterns: List[re.Pattern[str]] = []
    if not ignore_file.exists():
        return patterns
    for raw in ignore_file.read_text(encoding='utf-8').splitlines():
        line = raw.strip()
        if not line or line.startswith('#'):
            continue
        try:
            patterns.append(re.compile(line))
        except re.error as e:
            raise SystemExit(f"Invalid regex in {ignore_file}: {line}\n  {e}")
    return patterns


def filter_modules_with_ignore(modules: Set[str], patterns: List[re.Pattern[str]]) -> Set[str]:
    if not patterns:
        return modules
    kept: Set[str] = set()
    for m in modules:
        if any(p.search(m) for p in patterns):
            continue
        kept.add(m)
    return kept


def discover_matroid_modules(matroid_dir: Path) -> Set[str]:
    modules: Set[str] = set()
    for root, dirs, files in os.walk(matroid_dir):
        # Skip hidden directories like .git or .lake
        dirs[:] = [d for d in dirs if not d.startswith('.')]
        for fn in files:
            if not fn.endswith('.lean'):
                continue
            # Skip aux/compiled artifacts
            if fn.endswith('.olean'):
                continue
            rel = Path(root, fn).relative_to(matroid_dir)
            # Drop extension and convert path separators to dots
            mod_parts = rel.with_suffix('').parts
            # Build module path as Matroid.<...>
            module = 'Matroid.' + '.'.join(mod_parts)
            modules.add(module)
    return modules


def parse_existing_imports(matroid_lean_path: Path) -> Tuple[List[str], Dict[str, str]]:
    """
    Returns:
    - all_lines: raw lines from the file (for potential preservation if needed)
    - by_module: mapping from module name (Matroid.xxx) to its existing line, which may be commented or not
    """
    if not matroid_lean_path.exists():
        return [], {}
    text = matroid_lean_path.read_text(encoding='utf-8')
    all_lines = text.splitlines()
    by_module: Dict[str, str] = {}
    for line in all_lines:
        m = IMPORT_RE.match(line)
        if m:
            # m.group(1) is optional comment marker '-- '
            module = m.group(2)
            # Preserve the original exact line (with comment if present)
            by_module[module] = line.rstrip()
    return all_lines, by_module


def merge_and_sort_imports(existing: Dict[str, str], discovered: Iterable[str], *, comment: bool = False, uncomment: bool = False, root: Path = None, verbose: bool = False, workers: int = 8) -> Tuple[List[Tuple[str, str]], List[str]]:
    out: List[Tuple[str, str]] = []
    uncommented_modules: List[str] = []
    
    # Collect all commented imports that need testing
    # IMPORTANT: Only test modules that are in the filtered discovery set.
    # This ensures ignored modules (via .matroidignore) are never tested or uncommented.
    commented_imports_to_test = []
    for mod in discovered:
        if mod in existing:
            existing_line = existing[mod]
            if uncomment and existing_line.strip().startswith('-- import'):
                commented_imports_to_test.append(mod)
    
    # Test all commented imports in parallel
    test_results = {}
    if commented_imports_to_test and root:
        test_results = test_lean_files_parallel(commented_imports_to_test, root, workers, verbose)
    
    # Process discovered modules
    for mod in discovered:
        if mod in existing:
            existing_line = existing[mod]
            # Check if this is a commented import and we're in uncomment mode
            if uncomment and existing_line.strip().startswith('-- import'):
                if test_results.get(mod, False):
                    # Uncomment this import
                    uncommented_line = existing_line.replace('-- import', 'import', 1)
                    out.append((mod, uncommented_line))
                    uncommented_modules.append(mod)
                else:
                    # Keep as commented
                    out.append((mod, existing_line))
            else:
                out.append((mod, existing_line))
        else:
            if comment:
                out.append((mod, f"-- import {mod}"))
            else:
                out.append((mod, f"import {mod}"))
    
    # Also include any existing modules that are NOT in discovered (to preserve them),
    # though typically Matroid.lean should correspond exactly to discovered under Matroid/.
    for mod, line in existing.items():
        if mod not in {m for m, _ in out}:
            # Never attempt to uncomment modules that are outside the filtered discovery set
            # (e.g., ignored by .matroidignore). Simply preserve them as-is.
            out.append((mod, line))
    
    # Sort purely by module name
    out.sort(key=lambda t: t[0])
    
    return out, uncommented_modules


def test_lean_file(module_name: str, root: Path, verbose: bool = False) -> bool:
    """
    Test a lean file by running `lake env lean` on it.
    Returns True if the file compiles successfully (no output), False otherwise.
    """
    if verbose:
        print(f"  Testing {module_name}...", end=' ', flush=True)
    
    # Convert module name to file path
    # Matroid.xxx.yyy -> Matroid/xxx/yyy.lean
    module_parts = module_name.split('.')[1:]  # Remove 'Matroid' prefix
    file_path = root / 'Matroid' / Path(*module_parts).with_suffix('.lean')
    
    if not file_path.exists():
        if verbose:
            print("✗ (file not found)")
        return False
    
    try:
        # Run lake env lean on the file
        result = subprocess.run(
            ['lake', 'env', 'lean', str(file_path)],
            cwd=root,
            capture_output=True,
            text=True,
            timeout=30  # 30 second timeout
        )
        # Return True if no output (successful compilation)
        success = result.returncode == 0 and not result.stdout.strip() and not result.stderr.strip()
        if verbose:
            print("✓" if success else "✗")
        return success
    except (subprocess.TimeoutExpired, subprocess.CalledProcessError, FileNotFoundError):
        if verbose:
            print("✗ (timeout/error)")
        return False


def test_lean_files_parallel(module_names: List[str], root: Path, workers: int = 8, verbose: bool = False) -> Dict[str, bool]:
    """
    Test multiple lean files in parallel.
    Returns a dictionary mapping module names to their test results.
    """
    if not module_names:
        return {}
    
    if verbose:
        print(f"Testing {len(module_names)} files with {workers} parallel workers...")
    
    results = {}
    
    with ThreadPoolExecutor(max_workers=workers) as executor:
        # Submit all tasks
        future_to_module = {
            executor.submit(test_lean_file, module_name, root, verbose=False): module_name
            for module_name in module_names
        }
        
        # Collect results as they complete
        for future in as_completed(future_to_module):
            module_name = future_to_module[future]
            try:
                result = future.result()
                results[module_name] = result
                if verbose:
                    status = "✓" if result else "✗"
                    print(f"  {status} {module_name}")
            except Exception as e:
                results[module_name] = False
                if verbose:
                    print(f"  ✗ {module_name} (error: {e})")
    
    return results


def build_new_file_content(sorted_imports: List[Tuple[str, str]]) -> str:
    lines = [line for _, line in sorted_imports]
    # Ensure trailing newline
    return '\n'.join(lines) + '\n'


def main() -> int:
    parser = argparse.ArgumentParser(description='Update Matroid.lean with imports for all files under Matroid/.')
    parser.add_argument('--root', type=str, default=None, help='Repository root path (default: parent of this script directory).')
    parser.add_argument('--matroid-dir', type=str, default=None, help='Path to Matroid/ directory (default: <root>/Matroid).')
    parser.add_argument('--matroid-file', type=str, default=None, help='Path to Matroid.lean (default: <root>/Matroid.lean).')
    parser.add_argument('--dry-run', action='store_true', help='Do not modify files; show summary and diff-like preview.')
    parser.add_argument('--comment', action='store_true', help='Write newly added modules as commented imports (`-- import ...`).')
    parser.add_argument('--uncomment', action='store_true', help='Test commented imports and uncomment those that compile successfully.')
    parser.add_argument('--workers', type=int, default=8, help='Number of parallel workers for compilation testing (default: 8).')
    parser.add_argument('--all', action='store_true', help='Do not apply ignore rules from .matroidignore (in scripts/); include all modules discovered.')
    parser.add_argument('--yes', '-y', action='store_true', help='Proceed without interactive confirmation (useful for CI).')

    args = parser.parse_args()

    script_path = Path(__file__).resolve()
    default_root = script_path.parent.parent
    root = Path(args.root) if args.root else default_root
    matroid_dir = Path(args.matroid_dir) if args.matroid_dir else root / 'Matroid'
    matroid_file = Path(args.matroid_file) if args.matroid_file else root / 'Matroid.lean'

    if not matroid_dir.is_dir():
        raise SystemExit(f"Matroid directory not found: {matroid_dir}")
    
    # Validate uncomment mode
    if args.uncomment and not matroid_file.exists():
        raise SystemExit(f"Cannot use --uncomment mode: {matroid_file} does not exist")

    discovered = discover_matroid_modules(matroid_dir)
    # Apply ignore file unless --all is given
    ignore_file = script_path.parent / '.matroidignore'
    ignore_patterns = [] if args.all else load_ignore_patterns(ignore_file)
    discovered_filtered = filter_modules_with_ignore(discovered, ignore_patterns) if ignore_patterns else discovered
    _, existing_map = parse_existing_imports(matroid_file)

    # Show initial information
    print(f"Root: {root}")
    print(f"Discovered modules: {len(discovered)}")
    if not args.all and ignore_patterns:
        ignored_count = len(discovered) - len(discovered_filtered)
        print(f"Ignored by patterns: {ignored_count}")
    print(f"Using modules: {len(discovered_filtered)}")
    print(f"Existing entries: {len(existing_map)}")

    # If in uncomment mode, show what we're about to test
    if args.uncomment:
        commented_imports = [mod for mod, line in existing_map.items() if line.strip().startswith('-- import')]
        print(f"Commented imports to test: {len(commented_imports)}")
        if commented_imports:
            print("Testing commented imports...")

    merged, uncommented_modules = merge_and_sort_imports(existing_map, discovered_filtered, comment=args.comment, uncomment=args.uncomment, root=root, verbose=args.uncomment, workers=args.workers)
    new_content = build_new_file_content(merged)

    current_text = matroid_file.read_text(encoding='utf-8') if matroid_file.exists() else ''

    # Function to print the same summary as dry-run
    def print_summary():
        existing_modules = set(existing_map.keys())
        missing = sorted(discovered_filtered - existing_modules)
        extra = sorted(existing_modules - discovered_filtered)
        
        if args.uncomment:
            if uncommented_modules:
                print(f"\nSuccessfully uncommented {len(uncommented_modules)} imports:")
                for mod in uncommented_modules:
                    print(f"  ✓ {mod}")
            commented_imports = [mod for mod, line in existing_map.items() if line.strip().startswith('-- import')]
            failed_count = len(commented_imports) - len(uncommented_modules)
            if failed_count > 0:
                print(f"Failed to uncomment {failed_count} imports (compilation errors)")
        else:
            print(f"Missing entries to add: {len(missing)}")
            for m in missing[:50]:
                prefix = "-- import" if args.comment else "import"
                print(f"+ {prefix} {m}")
            if len(missing) > 50:
                print(f"... and {len(missing) - 50} more")
        
        if extra:
            print(f"Note: {len(extra)} entries exist in Matroid.lean but not found under Matroid/ or are excluded by ignore rules (will be preserved):")
            for m in extra[:20]:
                print(f"  keep: {m}")
            if len(extra) > 20:
                print(f"  ... and {len(extra) - 20} more")
        changed = (current_text != new_content)
        print("\nWould modify Matroid.lean:", "yes" if changed else "no")
        return missing, changed

    if args.dry_run:
        print_summary()
        return 0

    # Non-dry-run: show summary, prompt, and proceed if confirmed
    missing, changed = print_summary()
    if not changed:
        # No changes to apply
        return 0
    if not args.yes:
        try:
            resp = input("Proceed with these changes? Type 'y' or 'yes' to continue: ").strip().lower()
        except EOFError:
            resp = ''
        if resp not in {'y', 'yes'}:
            print('Aborted by user.')
            return 1
    # Write only if content actually changed
    matroid_file.write_text(new_content, encoding='utf-8')
    if args.uncomment and uncommented_modules:
        print(f"Updated {matroid_file} with {len(merged)} import lines ({len(uncommented_modules)} uncommented).")
    else:
        print(f"Updated {matroid_file} with {len(merged)} import lines.")

    return 0


if __name__ == '__main__':
    raise SystemExit(main())

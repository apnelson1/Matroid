#!/usr/bin/env python3
import os
import re
import subprocess

# Configuration
MATHLIB_PATH = ".lake/packages/mathlib"
TARGET_DIR = "."

# Support complete, single-line imports with ordinary ASCII module names.
IMPORT_RE = re.compile(
    r"\s*(?P<command>(?P<public>public\s+)?(?P<meta>meta\s+)?import\s+"
    r"(?P<all>all\s+)?(?P<name>[A-Za-z_][A-Za-z0-9_']*"
    r"(?:\.[A-Za-z_][A-Za-z0-9_']*)*))\s*"
)

def header_imports(lines):
    """Yield (line index, match, trailing comment depth, module mode).

    Mask nested comments without changing offsets into the original lines.
    Stop at the first body command or unsupported import layout.
    """
    depth = 0
    is_module = False
    for index, line in enumerate(lines):
        code = list(line)
        pos = 0
        while pos < len(line):
            if line.startswith("/-", pos):
                depth += 1
                code[pos:pos + 2] = "  "
                pos += 2
            elif depth and line.startswith("-/", pos):
                depth -= 1
                code[pos:pos + 2] = "  "
                pos += 2
            elif not depth and line.startswith("--", pos):
                code[pos:] = " " * (len(line) - pos)
                break
            else:
                if depth:
                    code[pos] = " "
                pos += 1
        code = "".join(code)
        if code.strip() == "module":
            is_module = True
            continue
        if not code.strip() or code.strip() == "prelude":
            continue
        match = IMPORT_RE.fullmatch(code)
        if not match:
            break
        yield index, match, depth, is_module

def find_lean_files(root_dir):
    lean_files = []
    for root, dirs, files in os.walk(root_dir):
        # Skip .lake and hidden directories
        dirs[:] = [d for d in dirs if not d.startswith('.')]
        
        for file in files:
            if file.endswith(".lean"):
                lean_files.append(os.path.join(root, file))
    return lean_files

def get_imports(file_path):
    """
    Returns a list of (line_index, import_name, full_line_content)
    """
    imports = []
    try:
        with open(file_path, 'r', encoding='utf-8', newline='') as f:
            lines = f.readlines()
            for i, match, _, _ in header_imports(lines):
                imports.append((i, match["name"], lines[i]))
    except Exception as e:
        print(f"Error reading {file_path}: {e}")
    return imports

def resolve_mathlib_import(import_name):
    # import_name: Mathlib.Data.Set.Basic
    parts = import_name.split('.')
    rel_path = os.path.join(*parts) + ".lean"
    full_path = os.path.join(MATHLIB_PATH, rel_path)
    
    if os.path.exists(full_path):
        return full_path
    return None

def get_transitive_imports(lean_file_path, source_import, is_module):
    """Replace one import step, respecting visibility along both import edges.

    Ordinary imports see only public dependencies. `all` and `public` compose
    by conjunction; `meta` propagates along either visible import edge.
    Legacy files ignore module-system restrictions and use plain imports.
    """
    imports = []
    try:
        with open(lean_file_path, 'r', encoding='utf-8') as f:
            for _, dependency, _, dependency_is_module in header_imports(f):
                public = not dependency_is_module or bool(dependency["public"])
                if is_module and not source_import["all"] and not public:
                    continue
                modifiers = ""
                all_modifier = ""
                if is_module:
                    if source_import["public"] and public:
                        modifiers += "public "
                    if source_import["meta"] or dependency["meta"]:
                        modifiers += "meta "
                    if source_import["all"] and dependency["all"]:
                        all_modifier = "all "
                imports.append(f"{modifiers}import {all_modifier}{dependency['name']}")
    except Exception as e:
        # A failed read must not turn into a successful test of a partial list.
        raise RuntimeError(f"Error reading imported file {lean_file_path}") from e
    return imports

def check_compilation(file_path):
    try:
        result = subprocess.run(
            ["lake", "env", "lean", file_path],
            stdout=subprocess.DEVNULL,
            stderr=subprocess.DEVNULL
        )
        return result.returncode == 0
    except Exception as e:
        print(f"Error running compiler: {e}")
        return False

def process_file(file_path):
    print(f"Processing {file_path}...")
    
    with open(file_path, 'r', encoding='utf-8', newline='') as f:
        original_lines = f.readlines()
        
    current_lines = list(original_lines)
    imports_to_check = header_imports(original_lines)
    
    # Filter for Mathlib imports
    mathlib_imports = [x for x in imports_to_check
                      if x[1]["name"] == "Mathlib" or x[1]["name"].startswith("Mathlib.")]
    
    changes_made = False
    
    for line_idx, match, depth, is_module in mathlib_imports:
        import_name = match["name"]
        if depth:
            print(f"  Skipping {import_name}: trailing multiline block comment")
            continue
        # Check if already marked
        if "-- inefficient" in current_lines[line_idx]:
             continue

        imported_file_path = resolve_mathlib_import(import_name)
        if not imported_file_path:
            continue
            
        transitive = get_transitive_imports(imported_file_path, match, is_module)
        
        # Prepare test content
        test_lines = list(current_lines)
        line = current_lines[line_idx]
        newline = "\r\n" if line.endswith("\r\n") else "\n"
        start, end = match.span("command")
        test_lines[line_idx] = line[:start] + newline.join(transitive) + line[end:]
        
        # Write test content
        try:
            with open(file_path, 'w', encoding='utf-8', newline='') as f:
                f.writelines(test_lines)

            print(f"  Testing {import_name}...")
            if check_compilation(file_path):
                print(f"  -> Inefficient: {import_name}")
                body = line.rstrip('\r\n')
                current_lines[line_idx] = body + " -- inefficient import" + line[len(body):]
                changes_made = True
        finally:
            # Restore even if the compiler is interrupted.
            with open(file_path, 'w', encoding='utf-8', newline='') as f:
                f.writelines(current_lines)
            
    if changes_made:
        print(f"Updated {file_path}")

if __name__ == "__main__":
    lean_files = find_lean_files(TARGET_DIR)
    print(f"Found {len(lean_files)} lean files.")
    for f in lean_files:
        process_file(f)


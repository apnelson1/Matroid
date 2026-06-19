#!/usr/bin/env python3
"""Analyze Lean build logs: per-module self times and import critical paths.

Lake prints self compile time per module, e.g.:
  ✔ [3209/3211] Built Matroid.Graph.Matching.Konigs (14s)

The critical path to a module M is the wall-clock lower bound with unlimited
parallelism:
  crit(M) = self(M) + max(crit(dep) for dep in direct Matroid imports of M)

Usage (from repo root):
  lake clean Matroid   # or: lc Matroid
  lake build Matroid 2>&1 | tee /tmp/build.log
  uv run scripts/analyze_compile_times.py /tmp/build.log

  uv run scripts/analyze_compile_times.py --build Matroid
  uv run scripts/analyze_compile_times.py --prefix Matroid.Graph /tmp/build.log
  uv run scripts/analyze_compile_times.py --module Matroid.Graph.Walk.Basic /tmp/build.log
  uv run scripts/analyze_compile_times.py --top 20 --chains 5 /tmp/build.log

Reads log from a file path or stdin when no path is given.
"""

from __future__ import annotations

import argparse
import glob
import re
import subprocess
import sys
from collections import defaultdict
from dataclasses import dataclass
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
BUILT_RE = re.compile(r"Built (Matroid\.[^\s]+) \(([0-9.]+)s\)")


@dataclass(frozen=True)
class CriticalPath:
    total: float
    modules: tuple[str, ...]


def parse_build_log(text: str) -> dict[str, float]:
    times: dict[str, float] = {}
    for mod, secs in BUILT_RE.findall(text):
        times[mod] = float(secs)
    return times


def parse_imports(root: Path, prefix: str = "Matroid.") -> dict[str, set[str]]:
    imports: dict[str, set[str]] = defaultdict(set)
    paths = [root / "Matroid.lean", *map(Path, glob.glob(str(root / "Matroid/**/*.lean"), recursive=True))]
    for path in paths:
        if not path.is_file():
            continue
        rel = path.relative_to(root).as_posix()
        mod = rel.removesuffix(".lean").replace("/", ".")
        for line in path.read_text(encoding="utf-8").splitlines():
            line = line.strip()
            if line.startswith("import ") and line.split()[1].startswith(prefix):
                imports[mod].add(line.split()[1])
    return imports


def critical_path(
    mod: str,
    times: dict[str, float],
    imports: dict[str, set[str]],
    memo: dict[str, CriticalPath],
    prefix: str,
) -> CriticalPath:
    if mod in memo:
        return memo[mod]
    self_t = times.get(mod, 0.0)
    deps = sorted(d for d in imports.get(mod, ()) if d.startswith(prefix))
    if not deps:
        result = CriticalPath(self_t, (mod,))
    else:
        best = max(
            (critical_path(d, times, imports, memo, prefix) for d in deps),
            key=lambda cp: cp.total,
        )
        result = CriticalPath(best.total + self_t, best.modules + (mod,))
    memo[mod] = result
    return result


def fmt_secs(secs: float) -> str:
    return f"{secs:5.1f}s"


def print_module_table(
    times: dict[str, float],
    imports: dict[str, set[str]],
    prefix: str,
    top: int,
    filter_prefix: str | None,
) -> None:
    mods = [m for m in times if m.startswith(filter_prefix or prefix)]
    rows = sorted(
        ((times[m], critical_path(m, times, imports, {}, prefix).total, m) for m in mods),
        reverse=True,
    )
    shown = rows[:top] if top else rows
    label = filter_prefix or prefix
    print(f"\n=== Top {len(shown)} modules by self time ({label}) ===")
    print(f"{'self':>7}  {'crit':>7}  module")
    for self_t, crit_t, mod in shown:
        print(f"{fmt_secs(self_t):>7}  {fmt_secs(crit_t):>7}  {mod}")


def print_chains(
    times: dict[str, float],
    imports: dict[str, set[str]],
    prefix: str,
    count: int,
    filter_prefix: str | None,
) -> None:
    mods = [m for m in times if m.startswith(filter_prefix or prefix)]
    memo: dict[str, CriticalPath] = {}
    paths = sorted(
        (critical_path(m, times, imports, memo, prefix) for m in mods),
        key=lambda cp: cp.total,
        reverse=True,
    )
    seen: set[tuple[str, ...]] = set()
    print(f"\n=== Longest critical paths ({count} distinct chains) ===")
    printed = 0
    for cp in paths:
        if cp.modules in seen:
            continue
        seen.add(cp.modules)
        printed += 1
        if printed > count:
            break
        leaf = cp.modules[-1]
        print(f"\n  {fmt_secs(cp.total)}  ({len(cp.modules)} modules)  →  {leaf}")
        for mod in cp.modules:
            print(f"    {fmt_secs(times.get(mod, 0.0))}  {mod}")


def print_module_detail(
    mod: str,
    times: dict[str, float],
    imports: dict[str, set[str]],
    prefix: str,
) -> None:
    memo: dict[str, CriticalPath] = {}
    cp = critical_path(mod, times, imports, memo, prefix)
    self_t = times.get(mod)
    print(f"\n=== {mod} ===")
    if self_t is None:
        print("  (no self time in log — module may not have been rebuilt)")
    else:
        print(f"  self: {fmt_secs(self_t)}   critical: {fmt_secs(cp.total)}")
    deps = sorted(d for d in imports.get(mod, ()) if d.startswith(prefix))
    if deps:
        print("  direct import branches:")
        for dep in deps:
            dep_cp = critical_path(dep, times, imports, memo, prefix)
            print(f"    {fmt_secs(dep_cp.total)}  {dep}")
    print("  critical path:")
    for m in cp.modules:
        print(f"    {fmt_secs(times.get(m, 0.0))}  {m}")


def print_root_imports(
    times: dict[str, float],
    imports: dict[str, set[str]],
    prefix: str,
    root: str,
    top: int,
) -> None:
    root_deps = sorted(d for d in imports.get(root, ()) if d.startswith(prefix) and d in times)
    if not root_deps:
        return
    memo: dict[str, CriticalPath] = {}
    rows = sorted(
        ((critical_path(m, times, imports, memo, prefix).total, times[m], m) for m in root_deps),
        reverse=True,
    )
    print(f"\n=== Slowest critical paths among {root} imports (top {top}) ===")
    for crit_t, self_t, mod in rows[:top]:
        print(f"  crit {fmt_secs(crit_t)}  self {fmt_secs(self_t)}  {mod}")


def run_build(target: str, root: Path) -> str:
    print(f"Running: lake build {target}", file=sys.stderr)
    proc = subprocess.run(
        ["lake", "build", target],
        cwd=root,
        capture_output=True,
        text=True,
        check=False,
    )
    out = proc.stdout + proc.stderr
    if proc.returncode != 0:
        print(out, file=sys.stderr)
        raise SystemExit(proc.returncode)
    return out


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument("log", nargs="?", help="build log file (default: stdin)")
    parser.add_argument("--root", type=Path, default=ROOT, help="repo root")
    parser.add_argument("--prefix", default="Matroid.", help="module prefix for import graph")
    parser.add_argument("--filter", dest="filter_prefix", help="only show modules with this prefix")
    parser.add_argument("--module", "-m", action="append", default=[], help="detail view for module(s)")
    parser.add_argument("--top", type=int, default=30, help="rows in self-time table (0 = all)")
    parser.add_argument("--chains", type=int, default=10, help="number of distinct critical paths")
    parser.add_argument("--root-module", default="Matroid", help="entry module for import ranking")
    parser.add_argument("--build", metavar="TARGET", help="run `lake build TARGET` and analyze output")
    args = parser.parse_args()

    if args.build:
        log_text = run_build(args.build, args.root)
    elif args.log:
        log_text = Path(args.log).read_text(encoding="utf-8")
    elif not sys.stdin.isatty():
        log_text = sys.stdin.read()
    else:
        parser.error("provide a log file, pipe build output, or use --build")

    times = parse_build_log(log_text)
    if not times:
        raise SystemExit("no 'Built Matroid.* (Xs)' lines found in log")

    imports = parse_imports(args.root, prefix=args.prefix)
    filter_prefix = args.filter_prefix or args.prefix

    print(f"Modules timed: {len(times)}")
    if args.build or args.log:
        pass
    print(f"Import graph: {len(imports)} modules under {args.prefix!r}")

    memo: dict[str, CriticalPath] = {}
    longest_mod = max(times, key=lambda m: critical_path(m, times, imports, memo, args.prefix).total)
    longest = critical_path(longest_mod, times, imports, memo, args.prefix)
    print(f"Longest critical path: {fmt_secs(longest.total)}  →  {longest_mod}")

    if args.module:
        detail_memo: dict[str, CriticalPath] = {}
        for mod in args.module:
            print_module_detail(mod, times, imports, args.prefix)
        return

    print_module_table(times, imports, args.prefix, args.top, filter_prefix)
    print_chains(times, imports, args.prefix, args.chains, filter_prefix)
    print_root_imports(times, imports, args.prefix, args.root_module, args.top)


if __name__ == "__main__":
    main()

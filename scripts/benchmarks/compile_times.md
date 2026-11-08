# Compile-time analysis

Parses a Lake build log and reports per-module **self times** plus **critical import paths** (the longest chain of dependencies that bounds wall-clock compile time with unlimited parallelism).

What it does:

- Extracts `Built Matroid.* (Xs)` lines from a build log.
- Scans `Matroid.lean` and `Matroid/**/*.lean` for direct `import Matroid.*` edges.
- Computes `crit(M) = self(M) + max(crit(dep))` over direct imports.
- Prints a self-time ranking, the longest critical paths, and slowest branches among `Matroid.lean` imports.

### Usage

For meaningful self times, rebuild Matroid modules first (Mathlib can stay cached):

```bash
lake clean Matroid
lake build Matroid 2>&1 | tee /tmp/build.log
uv run --no-project python scripts/benchmarks/analyze_compile_times.py /tmp/build.log
```

Or run the build from the script (clean first with `lake clean Matroid`):

```bash
lake clean Matroid && uv run --no-project python scripts/benchmarks/analyze_compile_times.py --build Matroid
```

Graph-only view:

```bash
uv run --no-project python scripts/benchmarks/analyze_compile_times.py --filter Matroid.GraphTheory.Graph --top 40 /tmp/build.log
```

Detail one module (shows each direct import branch and the winning critical path):

```bash
uv run --no-project python scripts/benchmarks/analyze_compile_times.py -m Matroid.GraphTheory.Graph.Walk.Basic /tmp/build.log
```

Options:

- `--prefix`: module prefix for the import graph (default `Matroid.`).
- `--filter`: restrict tables/chains to modules matching this prefix.
- `--top N`: rows in the self-time table (default 30; `0` = all).
- `--chains N`: number of distinct critical paths to print (default 10).
- `--root-module`: entry module for ranking direct imports (default `Matroid`).
- `--build TARGET`: run `lake build TARGET` and analyze stdout/stderr.

Notes:

- The current import parser recognizes plain `import` lines and omits `public import` lines.
  Its critical paths for module-format sources are therefore incomplete; per-module build times
  can still be read from the log.
- Self times come from Lake; critical paths use only **direct** `Matroid.*` imports (not Mathlib).
- If a module is not in the log, it was not rebuilt (cached) — run `lake clean Matroid` (or `lc Matroid`) before rebuilding for fresh numbers.
- Pipe or `tee` the build log; the script also reads stdin when no file path is given.

---


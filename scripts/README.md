# Repository tools

Run commands below from the repository root. Each tool lives with its tests and supporting
files.

| Folder | Purpose | Main tools |
| --- | --- | --- |
| [imports](imports/README.md) | Import lists, import minimization, and Lean module headers | `update_matroid_imports.py`, `detect_inefficient_imports.py`, `Modulize.lean` |
| [benchmarks](benchmarks/README.md) | Definition benchmarks and compile-time analysis | `benchmark_lean.py`, `analyze_compile_times.py` |
| [cache](cache) | Public Lake-cache registration | `register_lake_cache.sh` |

Common commands:

```sh
uv run --no-project python scripts/imports/update_matroid_imports.py --dry-run
uv run --no-project python scripts/benchmarks/analyze_compile_times.py build.log
bash scripts/cache/register_lake_cache.sh --help
```

The import minimizer and module-header converter edit source files when run normally.

For challenge/solution verification, Lean/Lake provides `lake comparator`. Consult
`lake comparator --help` for its configuration and guarantees.

## Tests

Run all script regression tests, including their Lean and native-execution checks:

```sh
uv run --no-project --with tomlkit python -m unittest \
  scripts.benchmarks.test_benchmark_lean \
  scripts.imports.test_detect_inefficient_imports \
  scripts.cache.test_register_lake_cache -v
```

For one tool, supply only its test module, for example `scripts.benchmarks.test_benchmark_lean`.
Cache tests use temporary configuration files and leave the user's Lake configuration alone.

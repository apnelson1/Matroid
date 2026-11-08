# Benchmarks

Measure executable evaluation, literal `by rfl` elaboration, and synchronous kernel checking
with a reusable Lean fixture. Each run preserves sources, hashes, raw measurements, and logs
in a fresh directory. Failed or incomplete runs produce no summary.

```sh
uv run --no-project python scripts/benchmarks/benchmark_lean.py \
  scripts/benchmarks/benchmark_lean_example.lean \
  --output ../benchmarks/definition-runs/example-1
```

See [Benchmark Lean definitions](benchmark_lean.md) for the fixture format, native execution,
measurement limits, and the regression-test command.

[Compile-time analysis](compile_times.md) covers build-log timings and import critical paths.

# Benchmark Lean definitions

Run executable cases and concrete `by rfl` proofs from one Lean fixture.
The runner records executable evaluation, proof elaboration, and kernel checking separately.
It uses Python's standard library and the current Lake project's Lean toolchain.
The process controls require a POSIX system.

From the repository root, run the example with a new output directory:

```sh
uv run --no-project python scripts/benchmarks/benchmark_lean.py \
  scripts/benchmarks/benchmark_lean_example.lean \
  --output ../benchmarks/definition-runs/example-1
```

The example compares two list reversals. It checks each complete executable result and
proves each concrete equality using literal `by rfl`. The output contains a validated
measurement grid and a summary for each case and stage. Reusing `example-1` fails without
changing its files. Choose another directory for the next run.

## Write a fixture

Copy [benchmark_lean_example.lean](benchmark_lean_example.lean). Import `LeanDefinitionBench`
and your candidate definitions. Build project dependencies with Lake before benchmarking.
The runner compiles its helper into the run directory, leaving the library source unchanged.

Define executable cases with `LeanDefinitionBench.EvalCase`:

| Field | Supply |
| --- | --- |
| `name` | A unique case name identifying the candidate and workload. |
| `Input`, `Output` | The input and result types. |
| `prepare` | An `IO Input` action that prepares the input before the clock starts. |
| `run` | An `Input → IO Output` action containing the computation to time. |
| `check` | An `Output → IO Unit` action that checks correctness after the clock stops and throws on failure. |

End the fixture with `def main : IO Unit := LeanDefinitionBench.runEval cases`.
Case order rotates between rounds. Each round prepares an input for each candidate.
Warmup rounds execute the same checks and remain in the raw evidence, outside the summary.

Specify ownership through `prepare`. Returning a retained value gives shared input.
The example's `prepare := pure (List.range 256)` can retain its already constructed list.
To construct fresh input on each call, put construction in an `IO` function with a runtime
parameter and prevent compiler specialization where needed. Inspect generated code before
claiming a particular ownership or allocation pattern.

Force the intended work inside `run`. Returning a thunk or a lazy sequence can move work
into `check`, outside the measured interval. The helper calls `run` through a function
marked `noinline`, but it cannot prevent optimization inside a candidate.
For very cheap operations, time a batch inside `run` and include its size in the case name.
The reported nanoseconds describe one case invocation, without automatic batch normalization.

Declare proof cases with the following command:

```lean
#bench_rfl [
  "baseline" => baseline input = expected,
  "candidate" => candidate input = expected]
```

Use unique names across all proof commands. Define concrete inputs and expected results
before the command. The helper elaborates the goals before timing. For each trial, it
elaborates literal `by rfl` with fresh elaborator caches and checks the resulting theorem
synchronously in the kernel. It uses the same starting kernel environment for each trial.
An invalid goal, failed proof, or disabled kernel checking fails the run.

## Select repetitions and preserve the sources

```sh
uv run --no-project python scripts/benchmarks/benchmark_lean.py MyExperiment.lean \
  --project . --output ../benchmarks/definition-runs/experiment-1 \
  --trials 12 --warmups 3 --timeout 120 \
  --source Matroid/GraphTheory/Walk/Defs.lean \
  --source Matroid/GraphTheory/Walk/Operations.lean
```

Repeat `--source` for every candidate or dependency file needed to identify the experiment.
The runner automatically snapshots the fixture, helper, Python runner, toolchain file,
and Lake manifest when present. It does not recursively snapshot imported source or build
dependencies. Source hashes alone do not prove that an imported compiled module is current.

Use `--stage eval` for execution only or `--stage proof` for elaboration and kernel checking.
The default runs both. `--cpu N` pins the runner and its subprocesses to an available CPU.
`--memory-mb`, `--heartbeats`, and `--max-rec-depth` control the Lean invocations.
`--timeout` bounds each subprocess, including helper compilation. A timeout kills its
process group and preserves available output. Use `--help` for defaults.

Each fresh output directory contains:

- `sources/` with the snapshotted files.
- `metadata.json` with source hashes, UTC timestamps, toolchain, machine information,
  arguments, commands, process statuses, and failures.
- `proof.log.json` and `eval.log.json` for the requested measurement processes.
- `raw.jsonl` with warmup and measured rows, case order, and process validity.
- `summary.json` with measured medians, inclusive quartiles, and ranges in nanoseconds.

The runner writes a summary only after every requested process succeeds, its emitted
measurement grid is complete, and the snapshotted files still match their hashes.
Failed and partial runs keep their logs and diagnostic rows, exit unsuccessfully, and
produce no summary. Initialization and subprocess startup are outside the measured
intervals. Command durations in metadata include that overhead and are diagnostic.

## Run a compiled native fixture

The default `eval` stage runs `lake env lean --run`. It measures Lean's executable
evaluator. Native execution uses a separately compiled fixture passed through
`--native-executable`. Those rows use the distinct stage name `native`.

For the standalone example, compile the helper and fixture in a fresh build directory:

```sh
bench_build_dir=../benchmarks/definition-runs/native-build-1
mkdir -p "$bench_build_dir"
export LEAN_PATH="$(realpath "$bench_build_dir")${LEAN_PATH:+:$LEAN_PATH}"
lake env lean -R scripts/benchmarks -o "$bench_build_dir/LeanDefinitionBench.olean" \
  -c "$bench_build_dir/helper.c" scripts/benchmarks/LeanDefinitionBench.lean
LEAN_BENCH_STAGE=eval lake env lean -R scripts/benchmarks \
  -c "$bench_build_dir/example.c" scripts/benchmarks/benchmark_lean_example.lean
lake env leanc -O3 "$bench_build_dir/helper.c" "$bench_build_dir/example.c" \
  -o "$bench_build_dir/example"
uv run --no-project python scripts/benchmarks/benchmark_lean.py \
  scripts/benchmarks/benchmark_lean_example.lean --stage eval \
  --native-executable "$bench_build_dir/example" \
  --output ../benchmarks/definition-runs/native-1
```

Fixtures importing project definitions also need their native dependencies linked.
Build those executables through the project's native build targets. Pass an executable
built from the fixture and helper being measured. The runner records the binary's hash
and checks for drift, but it does not establish a source-to-binary correspondence or
apply Lean's memory and heartbeat options to the native process.

## Check the runner

```sh
uv run --no-project python -m unittest scripts.benchmarks.test_benchmark_lean -v
```

The tests include real Lean evaluation and proofs, a compiled native example, incorrect
results, failed proofs, partial grids, malformed rows, source drift, timeouts, and existing
output preservation. Their low repetition counts check functionality. They do not
establish a performance ranking.

Choose workload sizes, ownership, and labels for the intended consumers. Assess absolute
costs and uncertainty before selecting a definition. Concrete `rfl` timings do not measure
symbolic proof ergonomics. The runner reports measurements and does not select winners.

The original Walk experiments remain in the
[benchmark archive](../../../benchmarks/walk-operations-2026-11-07/README.md).
Their raw results and conclusions were preserved during extraction of this tool.

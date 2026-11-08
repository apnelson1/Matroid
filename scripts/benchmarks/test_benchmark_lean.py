"""Run with: uv run --no-project python -m unittest discover -s scripts -t . -p test_benchmark_lean.py -v

From the Matroid reference checkout. Repetition counts in these tests are
functionality smoke checks. They are not comparative performance evidence.
"""

from __future__ import annotations

import hashlib
import json
import os
from pathlib import Path
import signal
import subprocess
import sys
import tempfile
import textwrap
import unittest


REPO = Path(__file__).resolve().parents[2]
SCRIPTS = Path(__file__).resolve().parent
RUNNER = SCRIPTS / "benchmark_lean.py"
EXAMPLE = SCRIPTS / "benchmark_lean_example.lean"
HELPER = SCRIPTS / "LeanDefinitionBench.lean"

FAKE_LAKE = textwrap.dedent("""\
    #!/usr/bin/env python3
    import json
    import os
    import subprocess
    import sys

    spec = {}
    spec_path = os.environ.get("BENCH_TEST_SPEC")
    if spec_path:
        with open(spec_path, encoding="utf-8") as stream:
            spec = json.load(stream)
    args = sys.argv[1:]

    def finish(code, stderr=""):
        if stderr:
            sys.stderr.write(stderr)
            sys.stderr.flush()
        raise SystemExit(code)

    if args[:3] == ["env", "lean", "--version"]:
        print(spec.get("version_text", "Lean (test double)"))
        finish(spec.get("version_exit", 0), spec.get("version_stderr", ""))

    if any(arg.endswith("LeanDefinitionBench.lean") for arg in args):
        if "-o" in args:
            olean = args[args.index("-o") + 1]
            open(olean, "wb").close()
        finish(spec.get("helper_exit", 0), spec.get("helper_stderr", ""))

    group = os.environ.get("LEAN_BENCH_STAGE", "")
    step = spec.get("steps", {}).get(group, spec.get("measure", {}))
    if step.get("mutate_source"):
        with open(step["mutate_source"], "w", encoding="utf-8") as stream:
            stream.write("changed during benchmark\\n")
    for line in step.get("lines", []):
        print(line, flush=True)
    if step.get("spawn_sleeper"):
        os.environ["BENCH_TEST_SLEEPER_LINE"] = step.get(
            "sleeper_line", "LEAN_BENCH partial-token")
        os.environ["BENCH_TEST_SLEEP"] = str(step.get("sleep", 30))
        child = subprocess.Popen([
            sys.executable, "-c",
            "import os, time; print(os.environ['BENCH_TEST_SLEEPER_LINE'], flush=True); "
            "time.sleep(int(os.environ['BENCH_TEST_SLEEP']))",
        ])
        child.wait()
    elif step.get("sleep"):
        import time
        time.sleep(step["sleep"])
    finish(step.get("exit", 0), step.get("stderr", ""))
    """)


def measurement(case="a", stage="eval", trial=0, position=0, phase="measure", wall_ns=1, **extra):
    row = {
        "case": case,
        "stage": stage,
        "trial": trial,
        "position": position,
        "phase": phase,
        "wall_ns": wall_ns,
    }
    row.update(extra)
    return "LEAN_BENCH " + json.dumps(row)


def grid_lines(stage, cases, values, warmups, warmup_wall=999999):
    lines = []
    for trial in range(warmups + len(next(iter(values.values())))):
        phase = "warmup" if trial < warmups else "measure"
        for position, name in enumerate(cases):
            wall = warmup_wall if phase == "warmup" else values[name][trial - warmups]
            lines.append(measurement(
                case=name, stage=stage, trial=trial, position=position,
                phase=phase, wall_ns=wall))
    return lines


def run_runner(args, env, timeout):
    process = subprocess.Popen(
        [sys.executable, str(RUNNER), *args],
        cwd=REPO,
        env=env,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        text=True,
        start_new_session=True,
    )
    try:
        stdout, stderr = process.communicate(timeout=timeout)
    except subprocess.TimeoutExpired:
        os.killpg(process.pid, signal.SIGKILL)
        stdout, stderr = process.communicate()
        raise AssertionError(f"runner exceeded {timeout}s\n{stderr}\n{stdout}")
    return process.returncode, stdout, stderr


class WorkspaceTest(unittest.TestCase):
    def setUp(self):
        temporary = tempfile.TemporaryDirectory(
            prefix="benchmark-lean-", dir=SCRIPTS)
        self.addCleanup(temporary.cleanup)
        self.workspace = Path(temporary.name)

    def output_dir(self, name):
        return self.workspace / name

    def assert_no_summary(self, code, stdout, stderr, output):
        self.assertNotEqual(code, 0, stderr + stdout)
        self.assertFalse((output / "summary.json").exists(), stderr)
        self.assertTrue((output / "metadata.json").is_file(), stderr)
        metadata = json.loads((output / "metadata.json").read_text())
        self.assertEqual(metadata["status"], "failed", metadata)
        self.assertTrue(metadata["failures"], metadata)
        return metadata

    def assert_snapshots(self, output, metadata):
        self.assertTrue(metadata["sources"], metadata)
        for source in metadata["sources"]:
            saved = output / source["saved"]
            data = saved.read_bytes()
            self.assertEqual(hashlib.sha256(data).hexdigest(), source["sha256"], source["path"])
            self.assertEqual(data, Path(source["path"]).read_bytes(), source["path"])


class OrchestratorTests(WorkspaceTest):
    def setUp(self):
        super().setUp()
        self.bin = self.workspace / "bin"
        self.bin.mkdir()
        lake = self.bin / "lake"
        lake.write_text(FAKE_LAKE)
        lake.chmod(0o755)
        self.fixture = self.workspace / "fixture.lean"
        self.fixture.write_text("-- orchestrator fixture\n")
        self.extra = self.workspace / "extra.txt"
        self.extra.write_text("snapshot me\n")

    def env_for(self, spec):
        spec_path = self.workspace / f"spec-{len(list(self.workspace.glob('spec-*.json')))}.json"
        spec_path.write_text(json.dumps(spec))
        env = os.environ.copy()
        env["PATH"] = str(self.bin) + os.pathsep + env.get("PATH", "")
        env["BENCH_TEST_SPEC"] = str(spec_path)
        return env

    def invoke(self, output, spec, extra_args=(), timeout=20):
        code, stdout, stderr = run_runner(
            [str(self.fixture), "--output", str(output), "--project", str(REPO),
             "--source", str(self.extra), *extra_args],
            self.env_for(spec),
            timeout,
        )
        return code, stdout, stderr

    def test_summary_is_deterministic_and_excludes_warmups(self):
        values = {"a": [10, 20, 30, 40], "b": [100, 200, 300, 400]}
        lines = ["info: not a measurement", *grid_lines("eval", ["a", "b"], values, warmups=1)]
        spec = {"measure": {"lines": lines}}
        first = self.output_dir("summary-a")
        second = self.output_dir("summary-b")
        code, stdout, stderr = self.invoke(
            first, spec, ["--stage", "eval", "--trials", "4", "--warmups", "1"])
        self.assertEqual(code, 0, stderr + stdout)
        code, stdout, stderr = self.invoke(
            second, {"measure": {"lines": list(reversed(lines))}},
            ["--stage", "eval", "--trials", "4", "--warmups", "1"])
        self.assertEqual(code, 0, stderr + stdout)

        summary_bytes = (first / "summary.json").read_bytes()
        self.assertEqual(summary_bytes, (second / "summary.json").read_bytes())
        summary = json.loads(summary_bytes)
        self.assertEqual(summary, [
            {"stage": "eval", "case": "a", "trials": 4, "unit": "ns",
             "median_ns": 25.0, "min_ns": 10, "max_ns": 40, "q1_ns": 17.5, "q3_ns": 32.5},
            {"stage": "eval", "case": "b", "trials": 4, "unit": "ns",
             "median_ns": 250.0, "min_ns": 100, "max_ns": 400, "q1_ns": 175.0, "q3_ns": 325.0},
        ])
        raw = (first / "raw.jsonl").read_text()
        self.assertIn("999999", raw)
        self.assertNotIn("999999", summary_bytes.decode())
        metadata = json.loads((first / "metadata.json").read_text())
        self.assertEqual(metadata["status"], "passed")
        self.assert_snapshots(first, metadata)
        self.assertTrue(any(source["path"] == str(self.extra) for source in metadata["sources"]))

        before = summary_bytes
        code, stdout, stderr = self.invoke(
            first, spec, ["--stage", "eval", "--trials", "4", "--warmups", "1"])
        self.assertNotEqual(code, 0, stdout)
        self.assertIn("already exists", stderr)
        self.assertEqual((first / "summary.json").read_bytes(), before)

    def test_single_measurement_quartiles(self):
        output = self.output_dir("one")
        spec = {"measure": {"lines": [measurement(wall_ns=7)]}}
        code, stdout, stderr = self.invoke(
            output, spec, ["--stage", "eval", "--trials", "1", "--warmups", "0"])
        self.assertEqual(code, 0, stderr + stdout)
        summary = json.loads((output / "summary.json").read_text())
        self.assertEqual(summary, [
            {"stage": "eval", "case": "a", "trials": 1, "unit": "ns",
             "median_ns": 7, "min_ns": 7, "max_ns": 7, "q1_ns": 7, "q3_ns": 7},
        ])

    def test_rejected_rows_write_no_summary(self):
        one = measurement()
        cases = {
            "duplicate": ([one, one], ["--stage", "eval", "--trials", "1", "--warmups", "0"], "duplicate measurement"),
            "incomplete": ([one], ["--stage", "eval", "--trials", "2", "--warmups", "0"], "incomplete measurement grid"),
            "missing_kernel": (
                [measurement(stage="elab")],
                ["--stage", "proof", "--trials", "1", "--warmups", "0"],
                "incomplete measurement grid",
            ),
            "malformed": (["LEAN_BENCH {"], ["--stage", "eval", "--trials", "1", "--warmups", "0"], None),
            "bool_wall": (
                ['LEAN_BENCH {"case":"a","stage":"eval","trial":0,"position":0,"phase":"measure","wall_ns":true}'],
                ["--stage", "eval", "--trials", "1", "--warmups", "0"],
                "invalid wall_ns",
            ),
            "negative_wall": (
                [measurement(wall_ns=-1)],
                ["--stage", "eval", "--trials", "1", "--warmups", "0"],
                "invalid wall_ns",
            ),
            "wrong_phase": (
                [measurement(phase="warmup")],
                ["--stage", "eval", "--trials", "1", "--warmups", "0"],
                "incorrect measurement phase",
            ),
            "unexpected_stage": (
                [measurement(stage="other")],
                ["--stage", "eval", "--trials", "1", "--warmups", "0"],
                "unexpected measurement stage",
            ),
            "no_rows": ([], ["--stage", "eval", "--trials", "1", "--warmups", "0"], "no measurements emitted"),
            "trial_past_end": (
                [measurement(trial=2)],
                ["--stage", "eval", "--trials", "1", "--warmups", "0"],
                "unexpected trial index",
            ),
            "empty_case": (
                [measurement(case="")],
                ["--stage", "eval", "--trials", "1", "--warmups", "0"],
                "measurement has no case name",
            ),
            "missing_position": (
                ['LEAN_BENCH {"case":"a","stage":"eval","trial":0,"phase":"measure","wall_ns":1}'],
                ["--stage", "eval", "--trials", "1", "--warmups", "0"],
                "invalid position",
            ),
            "chatter_does_not_complete_grid": (
                ["not a row", one],
                ["--stage", "eval", "--trials", "2", "--warmups", "0"],
                "incomplete measurement grid",
            ),
        }
        for name, (lines, args, error) in cases.items():
            with self.subTest(name=name):
                output = self.output_dir(name)
                code, stdout, stderr = self.invoke(output, {"measure": {"lines": lines}}, args)
                metadata = self.assert_no_summary(code, stdout, stderr, output)
                blob = json.dumps(metadata["failures"])
                if error is not None:
                    self.assertIn(error, blob, metadata)
                log_name = "proof" if "proof" in args else "eval"
                log = json.loads((output / f"{log_name}.log.json").read_text())
                self.assertEqual(log["status"], "passed", log)
                self.assertIn("\n".join(lines), log["stdout"])
                if lines and lines[0].startswith("LEAN_BENCH ") and name != "malformed":
                    self.assertTrue((output / "raw.jsonl").read_text().strip(), log)
                if name == "malformed":
                    self.assertIn("LEAN_BENCH {", log["stdout"])

    def test_failed_process_with_complete_grid_writes_no_summary(self):
        output = self.output_dir("process-fail")
        code, stdout, stderr = self.invoke(
            output,
            {"measure": {"lines": [measurement(), measurement(case="b", position=1)],
                         "exit": 1, "stderr": "process failed after rows\n"}},
            ["--stage", "eval", "--trials", "1", "--warmups", "0"],
        )
        metadata = self.assert_no_summary(code, stdout, stderr, output)
        self.assertIn("process failed after rows",
                      (output / "eval.log.json").read_text())
        raw = [json.loads(line) for line in (output / "raw.jsonl").read_text().splitlines()]
        self.assertEqual(len(raw), 2)
        self.assertTrue(all(item["process_success"] is False for item in raw))
        self.assertTrue(any(item["status"] == "failed" for item in metadata["failures"]))

    def test_helper_failure_writes_no_summary(self):
        output = self.output_dir("helper-fail")
        code, stdout, stderr = self.invoke(
            output,
            {"helper_exit": 1, "helper_stderr": "helper broke\n",
             "measure": {"lines": [measurement()]}},
            ["--stage", "eval", "--trials", "1", "--warmups", "0"],
        )
        metadata = self.assert_no_summary(code, stdout, stderr, output)
        self.assertFalse((output / "eval.log.json").exists())
        self.assertIn("helper broke", (output / "helper.log.json").read_text())
        self.assertTrue(any(item["step"] == "helper" for item in metadata["failures"]))

    def test_source_drift_writes_no_summary(self):
        output = self.output_dir("source-drift")
        before = self.extra.read_bytes()
        code, stdout, stderr = self.invoke(
            output,
            {"measure": {"lines": [measurement()], "mutate_source": str(self.extra)}},
            ["--stage", "eval", "--trials", "1", "--warmups", "0"],
        )
        metadata = self.assert_no_summary(code, stdout, stderr, output)
        self.assertIn({"step": "source_drift", "path": str(self.extra)}, metadata["failures"])
        snapshot = next(source for source in metadata["sources"] if source["path"] == str(self.extra))
        self.assertEqual((output / snapshot["saved"]).read_bytes(), before)
        self.assertNotEqual(self.extra.read_bytes(), before)

    def test_timeout_kills_group_and_writes_no_summary(self):
        output = self.output_dir("timeout")
        line = measurement(case="slow", wall_ns=5)
        code, stdout, stderr = self.invoke(
            output,
            {"measure": {"spawn_sleeper": True, "sleeper_line": line, "sleep": 30}},
            ["--stage", "eval", "--trials", "1", "--warmups", "0", "--timeout", "1"],
        )
        metadata = self.assert_no_summary(code, stdout, stderr, output)
        timed_out = [item for item in metadata["commands"] if item["status"] == "timeout"]
        self.assertEqual(len(timed_out), 1, metadata["commands"])
        self.assertLess(timed_out[0]["elapsed_ns"], 8_000_000_000, timed_out)
        self.assertLess(timed_out[0]["returncode"], 0, timed_out)
        self.assertIn("--run", timed_out[0]["command"])
        log = json.loads((output / "eval.log.json").read_text())
        self.assertEqual(log["status"], "timeout")
        self.assertIn(line, log["stdout"])
        self.assertLess(log["returncode"], 0)
        raw = [json.loads(item) for item in (output / "raw.jsonl").read_text().splitlines()]
        self.assertEqual(len(raw), 1)
        self.assertEqual(raw[0]["row"]["case"], "slow")
        self.assertFalse(raw[0]["process_success"])

    def test_existing_output_is_not_overwritten(self):
        output = self.output_dir("existing")
        output.mkdir()
        sentinel = output / "sentinel.txt"
        sentinel.write_bytes(b"keep-this-evidence\n")
        before = {path.relative_to(output): path.read_bytes() for path in output.rglob("*") if path.is_file()}
        code, stdout, stderr = run_runner(
            [str(EXAMPLE), "--output", str(output), "--project", str(REPO)],
            os.environ.copy(),
            20,
        )
        self.assertNotEqual(code, 0, stdout)
        self.assertIn("already exists", stderr)
        after = {path.relative_to(output): path.read_bytes() for path in output.rglob("*") if path.is_file()}
        self.assertEqual(after, before)
        self.assertFalse((output / "summary.json").exists())
        self.assertFalse((output / "metadata.json").exists())


class LeanTests(WorkspaceTest):
    def write_fixture(self, name, source):
        path = self.workspace / name
        path.write_text(textwrap.dedent(source))
        return path

    def invoke(self, fixture, output, args, timeout=180):
        return run_runner(
            [str(fixture), "--output", str(output), "--project", str(REPO), *args],
            os.environ.copy(),
            timeout + 60,
        )

    def test_example_eval_elab_and_kernel(self):
        output = self.output_dir("example")
        code, stdout, stderr = self.invoke(
            EXAMPLE, output,
            ["--stage", "both", "--trials", "1", "--warmups", "1", "--timeout", "180"],
        )
        self.assertEqual(code, 0, stderr + stdout)
        metadata = json.loads((output / "metadata.json").read_text())
        self.assertEqual(metadata["status"], "passed")
        self.assertEqual(metadata["failures"], [])
        self.assertTrue(metadata["lean_version"].startswith("Lean"))
        self.assert_snapshots(output, metadata)
        commands = metadata["commands"]
        proof = next(item for item in commands if item["command"][-1] == str(EXAMPLE))
        evaluated = next(item for item in commands if "--run" in item["command"])
        self.assertEqual(proof["status"], "passed")
        self.assertEqual(evaluated["status"], "passed")
        for command in (proof["command"], evaluated["command"]):
            self.assertIn("-DElab.async=false", command)
            self.assertIn("-Ddebug.skipKernelTC=false", command)

        raw = [json.loads(line) for line in (output / "raw.jsonl").read_text().splitlines()]
        self.assertEqual(len(raw), 12, raw)
        self.assertTrue(all(item["process_success"] for item in raw))
        by_key = {}
        for item in raw:
            row = item["row"]
            by_key[row["stage"], row["case"], row["trial"]] = row
            self.assertGreaterEqual(row["wall_ns"], 0)
        cases = {"slow", "accumulator"}
        self.assertEqual({row["row"]["case"] for row in raw}, cases)
        for case in cases:
            for trial, position in ((0, 0), (1, 1)) if case == "slow" else ((0, 1), (1, 0)):
                for stage in ("elab", "kernel"):
                    row = by_key[stage, case, trial]
                    self.assertEqual(row["position"], position, row)
                    self.assertEqual(row["phase"], "warmup" if trial == 0 else "measure")
                    self.assertGreater(row["heartbeats"], 0, row)
                eval_row = by_key["eval", case, trial]
                self.assertEqual(eval_row["position"], position, eval_row)
                self.assertNotIn("heartbeats", eval_row)
        summary = json.loads((output / "summary.json").read_text())
        self.assertEqual(
            [(item["stage"], item["case"]) for item in summary],
            [(stage, case) for stage in ("elab", "eval", "kernel") for case in ("accumulator", "slow")],
        )
        self.assertTrue(all(item["trials"] == 1 and item["unit"] == "ns" for item in summary))
        self.assertTrue(all(item["min_ns"] <= item["median_ns"] <= item["max_ns"] for item in summary))

    def test_native_executable(self):
        build = self.workspace / "native-build"
        build.mkdir()
        env = os.environ.copy()
        env["LEAN_PATH"] = str(build) + os.pathsep + env.get("LEAN_PATH", "")
        env["LEAN_BENCH_STAGE"] = "eval"
        commands = [
            ["lake", "env", "lean", "-R", str(SCRIPTS), "-o", str(build / "LeanDefinitionBench.olean"),
             "-c", str(build / "helper.c"), str(HELPER)],
            ["lake", "env", "lean", "-R", str(SCRIPTS), "-c", str(build / "example.c"), str(EXAMPLE)],
            ["lake", "env", "leanc", "-O3", str(build / "helper.c"), str(build / "example.c"),
             "-o", str(build / "example")],
        ]
        for command in commands:
            result = subprocess.run(command, cwd=REPO, env=env, capture_output=True, text=True, timeout=180)
            self.assertEqual(result.returncode, 0, result.stderr + result.stdout)
        output = self.output_dir("native")
        code, stdout, stderr = self.invoke(
            EXAMPLE, output,
            ["--stage", "eval", "--native-executable", str(build / "example"),
             "--trials", "1", "--warmups", "0", "--timeout", "180"],
        )
        self.assertEqual(code, 0, stderr + stdout)
        metadata = json.loads((output / "metadata.json").read_text())
        self.assertEqual(metadata["runtime"], "native")
        self.assertEqual(metadata["native_executable_sha256"],
                         hashlib.sha256((build / "example").read_bytes()).hexdigest())
        summary = json.loads((output / "summary.json").read_text())
        self.assertEqual({item["stage"] for item in summary}, {"native"})
        self.assertEqual({item["case"] for item in summary}, {"slow", "accumulator"})

    def test_wrong_executable_result(self):
        fixture = self.write_fixture("bad_result.lean", """
            import LeanDefinitionBench
            open LeanDefinitionBench

            def executableCases : Array EvalCase := #[{
              name := "bad"
              Input := Unit
              Output := Nat
              prepare := pure ()
              run := fun _ => pure 1
              check := fun result => do
                unless result == 0 do
                  throw <| IO.userError "bad: incorrect result"
            }]

            def main : IO Unit := runEval executableCases
            """)
        output = self.output_dir("bad-result")
        code, stdout, stderr = self.invoke(
            fixture, output, ["--stage", "eval", "--trials", "1", "--warmups", "0", "--timeout", "180"])
        metadata = self.assert_no_summary(code, stdout, stderr, output)
        log = json.loads((output / "eval.log.json").read_text())
        self.assertEqual(log["status"], "failed")
        self.assertIn("bad: incorrect result", log["stderr"])
        self.assertTrue(any(item["status"] == "failed" for item in metadata["failures"]))
        self.assertFalse((output / "summary.json").exists())

    def test_non_rfl_goal(self):
        fixture = self.write_fixture("non_rfl.lean", """
            import LeanDefinitionBench

            #bench_rfl ["false" => (1 : Nat) = 2]

            def main : IO Unit := pure ()
            """)
        output = self.output_dir("non-rfl")
        code, stdout, stderr = self.invoke(
            fixture, output, ["--stage", "proof", "--trials", "1", "--warmups", "0", "--timeout", "180"])
        self.assert_no_summary(code, stdout, stderr, output)
        log = json.loads((output / "proof.log.json").read_text())
        self.assertEqual(log["status"], "failed")
        self.assertIn("Tactic `rfl` failed", log["stdout"])
        self.assertIn("not definitionally equal", log["stdout"])
        self.assertFalse((output / "summary.json").exists())

    def test_partial_run_writes_no_summary(self):
        fixture = self.write_fixture("partial.lean", """
            import LeanDefinitionBench
            open LeanDefinitionBench

            #bench_rfl ["one" => (1 : Nat) = 1]

            def executableCases : Array EvalCase := #[{
              name := "bad"
              Input := Unit
              Output := Nat
              prepare := pure ()
              run := fun _ => pure 1
              check := fun result => do
                unless result == 0 do
                  throw <| IO.userError "bad: incorrect result"
            }]

            def main : IO Unit := runEval executableCases
            """)
        output = self.output_dir("partial")
        code, stdout, stderr = self.invoke(
            fixture, output, ["--stage", "both", "--trials", "1", "--warmups", "0", "--timeout", "180"])
        metadata = self.assert_no_summary(code, stdout, stderr, output)
        proof = next(item for item in metadata["commands"]
                     if item["command"][-1] == str(fixture) and "--run" not in item["command"])
        evaluated = next(item for item in metadata["commands"] if "--run" in item["command"])
        self.assertEqual(proof["status"], "passed", metadata)
        self.assertEqual(evaluated["status"], "failed", metadata)
        raw = [json.loads(line) for line in (output / "raw.jsonl").read_text().splitlines()]
        self.assertTrue(any(item["row"]["stage"] == "elab" and item["process_success"] for item in raw))
        self.assertTrue(any(item["row"]["stage"] == "kernel" and item["process_success"] for item in raw))
        self.assertFalse(any(item["row"]["stage"] == "eval" for item in raw))
        self.assertIn("bad: incorrect result", (output / "eval.log.json").read_text())
        self.assertFalse((output / "summary.json").exists())


if __name__ == "__main__":
    unittest.main()

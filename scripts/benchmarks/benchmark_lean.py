#!/usr/bin/env python3
"""Benchmark executable Lean cases and actual rfl elaboration and kernel checking.

Run with uv. Each invocation creates a new evidence directory and refuses to
overwrite an old run. A summary is written only when the requested stages
succeed, the measurement grid is complete, and the snapshotted sources are
unchanged.
"""

from __future__ import annotations

import argparse
from datetime import datetime, timezone
import hashlib
import json
import os
from pathlib import Path
import platform
import signal
import statistics
import subprocess
import sys
import time


HERE = Path(__file__).resolve().parent
PREFIX = "LEAN_BENCH "


def digest(path: Path) -> str:
    with path.open("rb") as stream:
        return hashlib.file_digest(stream, "sha256").hexdigest()


def positive(text: str) -> int:
    value = int(text)
    if value < 1:
        raise argparse.ArgumentTypeError("must be positive")
    return value


def nonnegative(text: str) -> int:
    value = int(text)
    if value < 0:
        raise argparse.ArgumentTypeError("must be nonnegative")
    return value


def run_command(command: list[str], project: Path, env: dict[str, str], timeout: int,
                log: Path) -> dict:
    """Bound a process and its descendants, retaining partial output on failure."""
    start = time.monotonic_ns()
    process = subprocess.Popen(command, cwd=project, env=env, stdout=subprocess.PIPE,
                               stderr=subprocess.PIPE, start_new_session=True)
    status = "passed"
    try:
        stdout, stderr = process.communicate(timeout=timeout)
    except (subprocess.TimeoutExpired, KeyboardInterrupt) as error:
        os.killpg(process.pid, signal.SIGKILL)
        stdout, stderr = process.communicate()
        status = "timeout" if isinstance(error, subprocess.TimeoutExpired) else "interrupted"
    if process.returncode and status == "passed":
        status = "failed"
    result = dict(command=command, status=status, returncode=process.returncode,
                  elapsed_ns=time.monotonic_ns() - start,
                  stdout=stdout.decode(errors="replace"), stderr=stderr.decode(errors="replace"))
    log.write_text(json.dumps(result, indent=2) + "\n")
    return result


def parse_rows(output: str, stages: set[str], warmups: int, trials: int) -> list[dict]:
    rows = []
    seen = set()
    for line in output.splitlines():
        if not line.startswith(PREFIX):
            continue
        row = json.loads(line[len(PREFIX):])
        if not isinstance(row, dict) or row.get("stage") not in stages:
            raise ValueError("unexpected measurement stage")
        if not isinstance(row.get("case"), str) or not row["case"]:
            raise ValueError("measurement has no case name")
        for key in ["wall_ns", "trial", "position"]:
            if type(row.get(key)) is not int or row[key] < 0:
                raise ValueError(f"invalid {key}")
        if row["trial"] >= warmups + trials:
            raise ValueError("unexpected trial index")
        phase = "warmup" if row["trial"] < warmups else "measure"
        if row.get("phase") != phase:
            raise ValueError("incorrect measurement phase")
        key = row["stage"], row["case"], row["trial"]
        if key in seen:
            raise ValueError(f"duplicate measurement: {key}")
        seen.add(key)
        rows.append(row)
    if not rows:
        raise ValueError("no measurements emitted")
    names = {row["case"] for row in rows}
    expected = {(stage, name, trial) for stage in stages for name in names
                for trial in range(warmups + trials)}
    if seen != expected:
        raise ValueError("incomplete measurement grid")
    return rows


def summarize(rows: list[dict]) -> list[dict]:
    result = []
    keys = sorted({(row["stage"], row["case"]) for row in rows})
    for stage, name in keys:
        values = sorted(row["wall_ns"] for row in rows
                        if row["stage"] == stage and row["case"] == name
                        and row["phase"] == "measure")
        quartiles = statistics.quantiles(values, n=4, method="inclusive") if len(values) > 1 else values * 3
        result.append(dict(stage=stage, case=name, trials=len(values), unit="ns",
                           median_ns=statistics.median(values), min_ns=min(values), max_ns=max(values),
                           q1_ns=quartiles[0], q3_ns=quartiles[2]))
    return result


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("fixture", type=Path, help="Lean file using LeanDefinitionBench")
    parser.add_argument("--output", type=Path, required=True, help="new evidence directory")
    parser.add_argument("--project", type=Path, default=Path.cwd(), help="Lake project, default cwd")
    parser.add_argument("--stage", choices=["both", "eval", "proof"], default="both")
    parser.add_argument("--trials", type=positive, default=7)
    parser.add_argument("--warmups", type=nonnegative, default=2)
    parser.add_argument("--timeout", type=positive, default=60, help="seconds per subprocess")
    parser.add_argument("--memory-mb", type=positive, default=4096, help="Lean memory limit")
    parser.add_argument("--heartbeats", type=nonnegative, default=0)
    parser.add_argument("--max-rec-depth", type=positive, default=100000)
    parser.add_argument("--cpu", type=nonnegative, help="pin subprocesses to this permitted CPU")
    parser.add_argument("--source", action="append", type=Path, default=[],
                        help="also snapshot a definition/dependency file; repeat as needed")
    parser.add_argument("--native-executable", type=Path,
                        help="run this already compiled fixture instead of Lean's executable evaluator")
    args = parser.parse_args()
    project, fixture, output = args.project.resolve(), args.fixture.resolve(), args.output.resolve()
    helper = HERE / "LeanDefinitionBench.lean"
    native = args.native_executable.resolve() if args.native_executable else None
    if not any((project / name).is_file() for name in ["lakefile.toml", "lakefile.lean"]):
        parser.error("--project must be a Lake project")
    sources = list(dict.fromkeys([fixture, helper, Path(__file__).resolve(),
                                 *[p.resolve() for p in args.source],
                                 *[project / name for name in ["lean-toolchain", "lake-manifest.json"]
                                   if (project / name).is_file()]]))
    if any(not path.is_file() for path in sources):
        parser.error("fixture, helper, and --source paths must be existing files")
    if native and (not native.is_file() or not os.access(native, os.X_OK) or args.stage == "proof"):
        parser.error("--native-executable needs an executable file and an eval stage")
    if output.exists():
        parser.error("output already exists; choose a new directory to preserve the earlier evidence")
    if args.cpu is not None:
        if not hasattr(os, "sched_getaffinity") or args.cpu not in os.sched_getaffinity(0):
            parser.error("--cpu is not available in this process's CPU affinity")
        os.sched_setaffinity(0, {args.cpu})
    output.mkdir(parents=True)
    (output / "sources").mkdir()
    (output / "build").mkdir()
    snapshots = []
    for index, source in enumerate(sources):
        data = source.read_bytes()
        saved = output / "sources" / f"{index}-{source.name}"
        saved.write_bytes(data)
        snapshots.append(dict(path=str(source), saved=str(saved.relative_to(output)),
                              sha256=hashlib.sha256(data).hexdigest()))
    metadata = dict(status="running", started_utc=datetime.now(timezone.utc).isoformat(),
                    arguments={key: str(value) if isinstance(value, Path) else
                        [str(p) for p in value] if isinstance(value, list) else value
                        for key, value in vars(args).items()},
                    project=str(project), fixture=str(fixture), sources=snapshots,
                    platform=platform.platform(), python=sys.version, cpu_count=os.cpu_count(),
                    affinity=sorted(os.sched_getaffinity(0)) if hasattr(os, "sched_getaffinity") else None,
                    load_average=list(os.getloadavg()) if hasattr(os, "getloadavg") else None,
                    runtime="native" if native else "lean-executable-evaluator",
                    native_executable_sha256=digest(native) if native else None,
                    commands=[], failures=[])
    metadata_path = output / "metadata.json"

    def save_metadata() -> None:
        metadata_path.write_text(json.dumps(metadata, indent=2) + "\n")

    save_metadata()
    env = os.environ.copy()
    env.update(LEAN_PATH=str(output / "build") + os.pathsep + env.get("LEAN_PATH", ""),
               LEAN_BENCH_TRIALS=str(args.trials), LEAN_BENCH_WARMUPS=str(args.warmups))
    raw = []

    def run(name: str, command: list[str]) -> dict:
        result = run_command(command, project, env, args.timeout, output / f"{name}.log.json")
        metadata["commands"].append({key: result[key] for key in
                                      ["command", "status", "returncode", "elapsed_ns"]})
        if result["status"] != "passed":
            metadata["failures"].append(dict(step=name, status=result["status"]))
            print(f"{name}: {result['status']}; see {output / (name + '.log.json')}", file=sys.stderr)
        save_metadata()
        return result

    try:
        version = run("version", ["lake", "env", "lean", "--version"])
        metadata["lean_version"] = version["stdout"].strip()
        copied_helper = output / "build/LeanDefinitionBench.lean"
        copied_helper.write_bytes(helper.read_bytes())
        built = run("helper", ["lake", "env", "lean", "-R", str(copied_helper.parent),
                               "-o", str(copied_helper.with_suffix(".olean")), str(copied_helper)])
        if built["status"] != "passed":
            metadata["status"] = "failed"
            return 1
        lean = ["lake", "env", "lean", "-j1", "-s32768", f"-M{args.memory_mb}",
                f"-DmaxHeartbeats={args.heartbeats}", f"-DmaxRecDepth={args.max_rec_depth}",
                "-DElab.async=false", "-Ddebug.skipKernelTC=false"]
        groups = ["proof", "eval"] if args.stage == "both" else [args.stage]
        for group in groups:
            env["LEAN_BENCH_STAGE"] = group
            env["LEAN_BENCH_RUNTIME"] = "native" if native else "eval"
            command = [*lean, str(fixture)] if group == "proof" else (
                [str(native)] if native else [*lean, "--run", str(fixture)])
            result = run(group, command)
            try:
                stages = {"elab", "kernel"} if group == "proof" else {"native" if native else "eval"}
                rows = parse_rows(result["stdout"], stages, args.warmups, args.trials)
            except (ValueError, TypeError) as error:
                metadata["failures"].append(dict(step=group, status="invalid_measurements", error=str(error)))
                # Retain partial measurements as diagnostic evidence, never as a successful summary.
                rows = []
                for line in result["stdout"].splitlines():
                    if line.startswith(PREFIX):
                        try:
                            rows.append(json.loads(line[len(PREFIX):]))
                        except ValueError:
                            pass
            valid = result["status"] == "passed" and not any(
                failure["step"] == group for failure in metadata["failures"])
            raw.extend(dict(row=row, process_success=valid, group=group) for row in rows)
            (output / "raw.jsonl").write_text("".join(json.dumps(row) + "\n" for row in raw))
            if result["status"] == "interrupted":
                break
        for source in snapshots:
            if not Path(source["path"]).is_file() or digest(Path(source["path"])) != source["sha256"]:
                metadata["failures"].append(dict(step="source_drift", path=source["path"]))
        if native and digest(native) != metadata["native_executable_sha256"]:
            metadata["failures"].append(dict(step="source_drift", path=str(native)))
        if metadata["failures"]:
            metadata["status"] = "failed"
            print(f"Run failed; evidence retained at {output}", file=sys.stderr)
            return 1
        summary = summarize([item["row"] for item in raw])
        (output / "summary.json").write_text(json.dumps(summary, indent=2) + "\n")
        metadata["status"] = "passed"
        print(f"Validated {len(raw)} rows across {len(summary)} case/stage combinations. Evidence: {output}")
        return 0
    except (OSError, KeyboardInterrupt) as error:
        metadata["status"] = "failed"
        metadata["failures"].append(dict(step="runner", error=str(error)))
        print(f"Run failed: {error}. Evidence: {output}", file=sys.stderr)
        return 1
    finally:
        metadata["finished_utc"] = datetime.now(timezone.utc).isoformat()
        save_metadata()


if __name__ == "__main__":
    raise SystemExit(main())

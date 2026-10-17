#!/usr/bin/env python3
"""Checked loaded-runtime comparisons with explicit Infera backend selection.

Program loading, one checked warmup and final output are outside each engine's
clock interval. Infera's machine-cache clock includes event projection and its
Reference comparison; Prolog clocks include findall and independent checks.
These are equivalent-workload comparisons, not isolated VM dispatch timings.
"""

import argparse
import ast
import hashlib
import json
import math
import os
from pathlib import Path
import platform
import re
import shutil
import statistics
import subprocess
import sys
import tempfile

ROOT = Path(__file__).resolve().parents[1]
CASES = ("controls-arithmetic", "controls-once", "controls-not", "controls-if",
         "controls", "core-nrev", "core-loop", "core-fib", "core-queens")
ENGINES = ("infera-bytecode", "infera-interpreted", "swipl", "scryer")
RESULT = "INFERA_RUNTIME_RESULT:"
CPU = "INFERA_RUNTIME_CPU_SECONDS:"
WALL = "INFERA_RUNTIME_WALL_SECONDS:"
MARKER = "INFERA_RUNTIME_OK:"
MIN_GATE_BATCH_CPU_SECONDS = 0.05


class RuntimeErrorChecked(Exception):
    pass


def positive_count(value):
    count = int(value)
    if not 0 < count <= 1000000:
        raise argparse.ArgumentTypeError("must be an integer between 1 and 1000000")
    return count


def positive_seconds(value):
    seconds = float(value)
    if not math.isfinite(seconds) or seconds <= 0:
        raise argparse.ArgumentTypeError("must be a finite positive number")
    return seconds


def executable(value):
    path = Path(shutil.which(value) or value).expanduser().resolve()
    if not path.is_file() or not os.access(path, os.X_OK):
        raise RuntimeErrorChecked("executable not found: " + str(path))
    return str(path)


def one_line(prefix, stdout):
    values = [line.lstrip()[len(prefix):] for line in stdout.splitlines() if line.lstrip().startswith(prefix)]
    if len(values) != 1:
        raise RuntimeErrorChecked("expected exactly one " + prefix + " line")
    return values[0]


def validate_result(case, answers):
    if type(answers) is not list or len(answers) != 1:
        raise RuntimeErrorChecked("expected exactly one fully collected answer")
    value = answers[0]
    expected = {"core-loop": 90000, "core-fib": 75025}.get(case, 45150)
    if case == "core-nrev":
        valid = (type(value) is list and all(type(x) is int for x in value)
                 and value == list(range(30, 0, -1)))
    elif case == "core-queens":
        valid = (type(value) is list and all(type(x) is int for x in value)
                 and sorted(value) == list(range(1, 9))
                 and all(abs(a - b) != j - i for i, a in enumerate(value)
                         for j, b in enumerate(value) if i < j))
    else:
        valid = type(value) is int and value == expected
    if not valid:
        raise RuntimeErrorChecked("independent result model failed for " + case)


def timing(value, name):
    try:
        seconds = float(value)
    except ValueError as error:
        raise RuntimeErrorChecked("invalid " + name + " timing") from error
    if not math.isfinite(seconds) or seconds <= 0:
        raise RuntimeErrorChecked(name + " duration is below timer resolution; increase --batch")
    return seconds


def gate_ready_timing(samples):
    # Positive millisecond samples remain descriptive; they cannot establish
    # a near-2x default migration without a sufficiently long timed batch.
    return bool(samples) and all(
        math.isfinite(item["cpu_seconds"])
        and item["cpu_seconds"] >= MIN_GATE_BATCH_CPU_SECONDS for item in samples)


def prolog_goal(engine, case, batch):
    # SWI's documented runtime/walltime counters are integer milliseconds.
    # Scryer 0.10.0 lacks statistics/2; verified library(time):time/1 prints
    # batch CPU to three decimals. It exposes no loaded wall clock here.
    batch_goal = "runtime_batch(" + str(batch) + ",'" + case + "')"
    if engine == "swipl":
        timed = ("statistics(runtime,[C0,_]),statistics(walltime,[W0,_]),"
                 + batch_goal + ","
                 "statistics(runtime,[C1,_]),statistics(walltime,[W1,_]),"
                 "Cpu is (C1-C0)/1000,Wall is (W1-W0)/1000,")
        clock_output = ("write('" + CPU + "'),write(Cpu),nl,"
                        "write('" + WALL + "'),write(Wall),nl,")
        setup = ""
    else:
        timed = "time(" + batch_goal + "),"
        clock_output = ""
        setup = "use_module(library(time)),"
    return (setup + "runtime_checked('" + case + "',_)," + timed
            + "runtime_checked('" + case + "',Results),"
            "write('" + RESULT + "'),write(Results),nl,"
            + clock_output + "write('" + MARKER + case + "'),nl,halt")


def read_prolog(case, stdout, engine):
    if one_line(MARKER, stdout) != case:
        raise RuntimeErrorChecked("incorrect completion marker")
    try:
        answers = ast.literal_eval(one_line(RESULT, stdout))
    except (ValueError, SyntaxError, RecursionError) as error:
        raise RuntimeErrorChecked("malformed Prolog result") from error
    validate_result(case, answers)
    if engine == "scryer":
        cpu = re.findall(r"^% CPU time: ([0-9]+(?:\.[0-9]+)?)s, [0-9]+(?:_[0-9]+)* inferences\s*$",
                         stdout, flags=re.MULTILINE)
        if len(cpu) != 1:
            raise RuntimeErrorChecked("expected exactly one Scryer loaded CPU timing")
        return {"cpu_seconds": timing(cpu[0], "CPU"), "wall_seconds": None,
                "result": answers}
    return {"cpu_seconds": timing(one_line(CPU, stdout), "CPU"),
            "wall_seconds": timing(one_line(WALL, stdout), "wall"), "result": answers}


def sample(engine, binary, case, args, source):
    if engine.startswith("infera-"):
        backend = engine[len("infera-"):]
        command = [binary, "--engine", backend, "--phase", "warm", "--case", case,
                   "--batch", str(args.batch), "--timeout", str(args.timeout)]
        completed = subprocess.run(command, cwd=ROOT, capture_output=True, text=True,
                                   timeout=args.timeout * 4 + 15)
        if completed.returncode:
            raise RuntimeErrorChecked("runner exited with status " + str(completed.returncode)
                                      + ": " + (completed.stderr or completed.stdout)[-1500:])
        try:
            row = json.loads(completed.stdout)
        except (ValueError, RecursionError) as error:
            raise RuntimeErrorChecked("malformed machine-cache JSON") from error
        if (row.get("status") != "ok" or row.get("engine") != backend
                or row.get("phase") != "warm" or row.get("case") != case
                or row.get("batch_queries") != args.batch or row.get("verified_answers") != 1
                or not all(row.get(key) is True for key in
                           ("fully_drained", "oracle_checked", "independent_checked", "fresh_query_state"))):
            raise RuntimeErrorChecked("machine-cache semantic or backend gate failed")
        return {"cpu_seconds": timing(str(row["cpu_seconds"]), "CPU"),
                "wall_seconds": timing(str(row["wall_seconds"]), "wall"),
                "command": command, "machine_cache": row}
    with tempfile.TemporaryDirectory(prefix="infera-runtime-compare-") as directory:
        path = Path(directory) / "runtime.pl"
        path.write_text(source, encoding="utf-8")
        goal = prolog_goal(engine, case, args.batch)
        if engine == "swipl":
            command = [binary, "-q", "-g", goal, "-t", "halt", str(path)]
        else:
            command = [binary, "-f", "--no-add-history", "-g", goal, str(path)]
        completed = subprocess.run(command, cwd=directory, input="", capture_output=True,
                                   text=True, timeout=args.timeout)
        if completed.returncode:
            raise RuntimeErrorChecked("engine exited with status " + str(completed.returncode)
                                      + ": " + (completed.stderr or completed.stdout)[-1500:])
        if re.search(r"\b(?:error|exception)\s*[:(]", completed.stderr + completed.stdout, re.I):
            raise RuntimeErrorChecked("engine reported an error: " + completed.stderr[-1500:])
        result = read_prolog(case, completed.stdout, engine)
        result["command"] = command
        result["stdout"] = completed.stdout
        result["stderr"] = completed.stderr
        return result


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--engine", action="append", choices=ENGINES,
                        help="repeat to select engines; default: explicit Infera bytecode, SWI and Scryer")
    parser.add_argument("--case", action="append", choices=CASES)
    parser.add_argument("--infera-runner", help="built machine-cache executable pathname")
    parser.add_argument("--swipl", default=os.environ.get("SWIPL_BIN", "swipl"))
    parser.add_argument("--scryer", default=os.environ.get("SCRYER_BIN", "scryer-prolog"))
    parser.add_argument("--batch", type=positive_count,
                        help="queries per sample; default: 100 for controls, 1 for core cases")
    parser.add_argument("--runs", type=positive_count, default=3)
    parser.add_argument("--timeout", type=positive_seconds, default=120)
    args = parser.parse_args(argv)
    engines = list(dict.fromkeys(args.engine or ("infera-bytecode", "swipl", "scryer")))
    cases = list(dict.fromkeys(args.case or CASES))
    try:
        binaries = {}
        for engine in engines:
            value = args.infera_runner if engine.startswith("infera-") else getattr(args, engine)
            if not value:
                raise RuntimeErrorChecked("--infera-runner is required for explicit Infera backends")
            binaries[engine] = executable(value)
        binary_hashes = {engine: hashlib.sha256(Path(path).read_bytes()).hexdigest()
                         for engine, path in binaries.items()}
        paths = [ROOT / "bench" / name for name in
                 ("bench.pl", "bench.nprolog", "runtime-compare.pl", "machine-cache.hs", "runtime-compare.py")]
        sources = {str(path.relative_to(ROOT)): path.read_bytes() for path in paths}
        hashes = {path: hashlib.sha256(contents).hexdigest() for path, contents in sources.items()}
        source = sources["bench/bench.pl"].decode() + "\n" + sources["bench/runtime-compare.pl"].decode()
    except (OSError, RuntimeErrorChecked) as error:
        parser.exit(1, "runtime comparison: " + str(error) + "\n")
    failed = False
    requested_batch = args.batch
    for case in cases:
        args.batch = requested_batch or (100 if case.startswith("controls") else 1)
        samples = {engine: [] for engine in engines}
        errors = {}
        # Alternate full engine order each round to expose monotonic host drift.
        for index in range(args.runs):
            order = engines if index % 2 == 0 else list(reversed(engines))
            for engine in order:
                if engine in errors:
                    continue
                try:
                    result = sample(engine, binaries[engine], case, args, source)
                    result["round"] = index
                    result["engine_order"] = order
                    samples[engine].append(result)
                except (OSError, subprocess.TimeoutExpired, RuntimeErrorChecked, KeyError) as error:
                    errors[engine] = str(error)
                    failed = True
        for engine in engines:
            row = {"engine": engine, "case": case, "binary": binaries[engine],
                   "binary_sha256": binary_hashes[engine],
                   "status": "error" if engine in errors else "ok", "runs": args.runs,
                   "batch_queries": args.batch, "warmup_queries_per_process": 1,
                   "scope": "loaded runtime; fresh process and one checked warmup per sample; timed solve+drain+validation",
                   "startup_included": False, "output_included": False,
                   "cpu_clock": ("GHC getCPUTime" if engine.startswith("infera-") else
                                 "statistics(runtime) milliseconds" if engine == "swipl" else
                                 "library(time):time/1; three-decimal seconds"),
                   "wall_clock": ("GHC monotonic clock" if engine.startswith("infera-") else
                                  "statistics(walltime) milliseconds" if engine == "swipl" else None),
                   "infera_overhead": "full event projection plus Reference ordered-stream comparison",
                   "prolog_overhead": "findall plus independent model check per query; final answer output outside timing",
                   "source_sha256": hashes, "platform": platform.platform(),
                   "minimum_gate_batch_cpu_seconds": MIN_GATE_BATCH_CPU_SECONDS,
                   "comparison_timing_sufficient": engine not in errors and gate_ready_timing(samples[engine]),
                   "samples": samples[engine] if engine not in errors else [],
                   "timeout_seconds": args.timeout}
            if engine in errors:
                row["error"] = errors[engine]
            else:
                for clock in ("cpu", "wall"):
                    raw_values = [item[clock + "_seconds"] for item in samples[engine]]
                    values = ([value / args.batch for value in raw_values]
                              if all(value is not None for value in raw_values) else None)
                    row["per_query_" + clock + "_samples_seconds"] = values
                    row["median_per_query_" + clock + "_seconds"] = statistics.median(values) if values else None
            print(json.dumps(row), flush=True)
    return 1 if failed else 0


if __name__ == "__main__":
    sys.exit(main())

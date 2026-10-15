#!/usr/bin/env python3
"""Validated CLI benchmarks for the two-stage engine roadmap.

Every warmup and timed run must exit successfully and produce one correct
result and completion marker. Timings include process startup and loading.
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
import time

ROOT = Path(__file__).resolve().parent.parent
BENCH = ROOT / "bench"
CASES = ("nrev", "loop", "fib", "queens")
RESULT = "INFERA_BENCH_RESULT:"
MARKER = "INFERA_BENCH_OK:"
ERROR = re.compile(r"\b(?:error|exception):|search depth limit", re.IGNORECASE)
FALSE = re.compile(r"^\s*(?:>\s*)?(?:false\.|fail\.)\s*$", re.MULTILINE)


class BenchmarkError(Exception):
    pass


def valid_count(value):
    count = int(value)
    if count < 0:
        raise argparse.ArgumentTypeError("must be nonnegative")
    return count


def valid_timeout(value):
    seconds = float(value)
    if not math.isfinite(seconds) or seconds <= 0:
        raise argparse.ArgumentTypeError("must be a finite positive number")
    return seconds


def executable(value):
    # A binary is one pathname, never a shell command. Resolve it before
    # switching to the isolated working directory used by each benchmark.
    found = shutil.which(value)
    path = Path(found or value).expanduser().resolve()
    if not path.is_file() or not os.access(path, os.X_OK):
        raise BenchmarkError("executable not found or not executable: " + str(path))
    return str(path)


def infera_binary(value):
    if value:
        return executable(value)
    cabal = shutil.which("cabal")
    if cabal:
        try:
            result = subprocess.run([cabal, "list-bin", "exe:infera"], cwd=ROOT,
                capture_output=True, text=True, timeout=15)
        except (OSError, subprocess.TimeoutExpired):
            result = None
        if result is not None and result.returncode == 0 and result.stdout.strip():
            return executable(result.stdout.strip())
    installed = shutil.which("infera")
    if installed:
        return executable(installed)
    raise BenchmarkError("build Infera first or set INFERA_BIN/--binary")


def selected_engines(args):
    names = list(dict.fromkeys(args.engine or ["infera", "swipl", "scryer"]))
    result = []
    for name in names:
        if name == "infera":
            result.append((name, infera_binary(args.binary or os.environ.get("INFERA_BIN"))))
        else:
            command = "swipl" if name == "swipl" else "scryer-prolog"
            override = os.environ.get("SWIPL_BIN" if name == "swipl" else "SCRYER_BIN")
            found = override or shutil.which(command)
            if found:
                result.append((name, executable(found)))
            elif args.engine:
                raise BenchmarkError("requested engine is unavailable: " + name)
    return result


def goals(case):
    infera = {
        "nrev": "bench_nrev 3000, range 1 30 L, nrev L Result",
        "loop": "loop 90000, Result = 90000",
        "fib": "fib 25 Result",
        "queens": "queens 8 Result",
    }[case]
    prolog = {
        "nrev": "bench_nrev(3000),range(1,30,L),nrev(L,Result)",
        "loop": "loop(90000),Result=90000",
        "fib": "fib(25,Result)",
        "queens": "queens(8,Result)",
    }[case]
    infera = 'once (' + infera + '), write "' + RESULT + '", writeln Result, writeln "' + MARKER + case + '"'
    prolog = "once((" + prolog + ")),write('" + RESULT + "'),write(Result),nl,write('" + MARKER + case + "'),nl"
    return infera, prolog


def validate(case, stdout, stderr):
    if ERROR.search(stdout) or ERROR.search(stderr) or FALSE.search(stdout):
        raise BenchmarkError("engine reported an error, failure or exhausted search")
    lines = stdout.splitlines()
    markers = [line for line in lines if line.startswith(MARKER)]
    if markers != [MARKER + case]:
        raise BenchmarkError("missing, duplicated or incorrect completion marker")
    results = [line[len(RESULT):] for line in lines if line.startswith(RESULT)]
    if len(results) != 1:
        raise BenchmarkError("expected exactly one result line")
    try:
        value = ast.literal_eval(results[0])
    except (ValueError, SyntaxError, RecursionError) as error:
        raise BenchmarkError("malformed result") from error
    if case in ("fib", "loop"):
        expected = 75025 if case == "fib" else 90000
        if type(value) is not int or value != expected:
            raise BenchmarkError("incorrect " + case + " result")
    elif case == "nrev":
        if type(value) is not list or any(type(x) is not int for x in value) or value != list(range(30, 0, -1)):
            raise BenchmarkError("incorrect reverse result")
    elif (type(value) is not list or len(value) != 8 or
            any(type(x) is not int for x in value) or sorted(value) != list(range(1, 9)) or
            any(abs(a-b) == j-i for i, a in enumerate(value) for j, b in enumerate(value) if i < j)):
        raise BenchmarkError("incorrect queens result")


def sample(case, engine, binary, args, directory, source, goal):
    suffix = ".nprolog" if engine == "infera" else ".pl"
    path = Path(directory) / (case + suffix)
    if engine == "infera":
        path.write_text(source + "\n> " + goal + "?\n", encoding="utf-8")
        command = [binary, str(path), "+RTS", "-N1", "-RTS"]
        input_text = ":q\n"
    else:
        path.write_text(source, encoding="utf-8")
        if engine == "swipl":
            command = [binary, "-q", "-g", goal + ",halt", "-t", "halt", str(path)]
        else:
            command = [binary, "-g", goal + ",halt", str(path)]
        input_text = ""
    environment = os.environ.copy()
    environment.update(INFERA_BENCH_CASE=case, INFERA_BENCH_ENGINE=engine, NO_COLOR="1")
    start = time.perf_counter()
    result = subprocess.run(command, input=input_text, cwd=directory,
        env=environment, capture_output=True, text=True, timeout=args.timeout)
    seconds = time.perf_counter() - start
    if result.returncode:
        diagnostic = (result.stderr or result.stdout).strip()[-1000:]
        raise BenchmarkError("engine exited with status " + str(result.returncode) +
            (": " + diagnostic if diagnostic else ""))
    validate(case, result.stdout, result.stderr)
    return seconds


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--binary", help="Infera executable pathname (or INFERA_BIN)")
    parser.add_argument("--engine", action="append", choices=("infera", "swipl", "scryer"),
        help="repeat to select engines; default: Infera and installed comparison engines")
    parser.add_argument("--case", action="append", choices=CASES, help="repeat to select workloads")
    parser.add_argument("--runs", type=valid_count, default=3, help="validated timed runs (default: 3)")
    parser.add_argument("--warmup", type=valid_count, default=1, help="validated unreported warmups (default: 1)")
    parser.add_argument("--timeout", type=valid_timeout, default=30, help="seconds per process (default: 30)")
    parser.add_argument("--json", action="store_true", help="emit one JSON object per engine/workload")
    args = parser.parse_args(argv)
    if args.runs == 0:
        parser.error("--runs must be positive")
    try:
        engines = selected_engines(args)
        sources = {"infera": (BENCH / "bench.nprolog").read_text(encoding="utf-8"),
                   "prolog": (BENCH / "bench.pl").read_text(encoding="utf-8")}
    except (BenchmarkError, OSError) as error:
        parser.exit(1, "benchmark: " + str(error) + "\n")
    cases = list(dict.fromkeys(args.case or CASES))
    metadata = {"platform": platform.platform(), "machine": platform.machine(),
                "python": platform.python_version(), "cpu_count": os.cpu_count(),
                "infera_rts": ["-N1"], "timing": "CLI startup, load, solve and output"}
    failed = False
    if not args.json:
        print("workload     engine    median seconds (validated samples)", flush=True)
    for case in cases:
        infera_goal, prolog_goal = goals(case)
        for engine, binary in engines:
            source = sources["infera" if engine == "infera" else "prolog"]
            goal = infera_goal if engine == "infera" else prolog_goal
            row = {"case": case, "engine": engine, "binary": binary,
                   "runs": args.runs, "warmup_runs": args.warmup,
                   "timeout_seconds": args.timeout, "status": "ok",
                   "workload_sha256": hashlib.sha256((source + "\n" + goal).encode()).hexdigest(),
                   "environment": metadata}
            samples = []
            try:
                with tempfile.TemporaryDirectory(prefix="infera-engine-bench-") as directory:
                    for number in range(args.warmup + args.runs):
                        seconds = sample(case, engine, binary, args, directory, source, goal)
                        if number >= args.warmup:
                            samples.append(seconds)
            except subprocess.TimeoutExpired:
                row.update(status="timeout", error="process exceeded the timeout")
            except (BenchmarkError, OSError, UnicodeError) as error:
                row.update(status="error", error=str(error))
            if row["status"] == "ok":
                row.update(samples_seconds=samples, median_seconds=statistics.median(samples),
                           min_seconds=min(samples), max_seconds=max(samples))
            else:
                failed = True
                row.update(samples_seconds=[])
            if args.json:
                print(json.dumps(row), flush=True)
            elif row["status"] == "ok":
                print(f"{case:12} {engine:9} {row['median_seconds']:.6f} " +
                    "(" + ", ".join(f"{s:.6f}" for s in samples) + ")", flush=True)
            else:
                print(f"{case:12} {engine:9} FAILED: {row['error']}", flush=True)
    return 1 if failed else 0


if __name__ == "__main__":
    sys.exit(main())

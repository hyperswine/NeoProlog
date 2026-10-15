"""Repeatable CLI benchmarks; timings are reports, never correctness gates.

python3 test/bench.py BINARY [--runs 3] [--timeout 10]
Use --breadboard FILE to benchmark a saved version of that model.
"""
import argparse
import ast
import json
from pathlib import Path
import statistics
import re
import subprocess
import tempfile
import time

parser = argparse.ArgumentParser(description=__doc__)
parser.add_argument("binary", type=Path)
parser.add_argument("--runs", type=int, default=3)
parser.add_argument("--timeout", type=float, default=10)
parser.add_argument("--breadboard", type=Path)
parser.add_argument("--case", action="append", help="Run only the named case; repeatable")
args = parser.parse_args()
if args.runs < 1 or args.timeout <= 0:
    parser.error("runs and timeout must be positive")
binary = args.binary.resolve()
root = Path(__file__).resolve().parent.parent
def without_entry_queries(source):
    # These shipped models use one-line entry queries. Benchmark just the
    # requested goal, rather than also running every report in the model.
    return "\n".join(line for line in source.splitlines() if not line.lstrip().startswith(">"))


mines = without_entry_queries((root / "examples/minesweeper.nprolog").read_text())
breadboard = without_entry_queries((args.breadboard or root / "examples/breadboard.nprolog").read_text())
cases = {
    "mine-setup-16": (mines, "once (minefield_constraints 16 16 50 [window 2 2 2] _ _)"),
    "mine-seeded-10": (mines, "once (minefield_seed 10 10 50 [window 2 2 2] 42 Grid)"),
    "mine-ordinary-16": (mines, "once (minefield 16 16 50 [window 2 2 2] Grid)"),
    "mine-seeded-16": (mines, "once (minefield_seed 16 16 50 [window 2 2 2] 42 Grid)"),
}
for circuit in ["rc", "div", "tri"]:
    cases["breadboard-" + circuit] = (breadboard,
        "comps " + circuit + " Cs, nets Cs Ns, best Cs Ns Wired P Cost")
for count in [100, 200]:
    graph = "\n".join("edge " + str(i) + " " + str(i+1) + "." for i in range(count))
    graph += "\npath X Y <- edge X Y.\npath X Z <- path X Y, edge Y Z.\n"
    cases["path-" + str(count)] = (graph, "findall Y (path 0 Y) Ys")
graph = "\n".join("edge " + str(i) + " " + str(i+1) + "." for i in range(100))
graph += "\npath X Y <- edge X Y.\npath X Z <- path X Y, edge Y Z.\n"
cases["path-all-100"] = (graph, "findall (pair X Y) (path X Y) Pairs")
wide_board = breadboard.replace("windows [win 7 11, win 5 13, win 3 15, win 1 16].",
    "windows [win 1 16].")
wide_board += '\ncomp wide r1 r "1k" a b.\ncomp wide r2 r "1k" c d.\ncomp wide r3 r "1k" e f.\n'
cases["breadboard-wide"] = (wide_board,
    "comps wide Cs, nets Cs Ns, best Cs Ns Wired P Cost")
unknown = set(args.case or []) - cases.keys()
if unknown:
    parser.error("unknown case(s): " + ", ".join(sorted(unknown)))


def validate(name, stdout):
    if "false." in stdout:
        raise ValueError("benchmark goal failed")
    if name.startswith("mine-") and name != "mine-setup-16":
        match = re.search(r"Grid\s*=\s*(\[\[.*?\]\])", stdout)
        if not match:
            raise ValueError("missing grid")
        grid = ast.literal_eval(match.group(1))
        size = 10 if name == "mine-seeded-10" else 16
        if len(grid) != size or any(len(row) != size for row in grid):
            raise ValueError("incorrect grid dimensions")
        if any(cell not in (0, 1) for row in grid for cell in row) or sum(map(sum, grid)) != 50:
            raise ValueError("incorrect bomb count or cell values")
        if any(sum(grid[y+dy][x+dx] for dy in range(2) for dx in range(2)) > 2
               for y in range(size-1) for x in range(size-1)):
            raise ValueError("window cap violated")
    elif name.startswith("path-") and name != "path-all-100":
        match = re.search(r"Ys\s*=\s*(\[[^]]*\])", stdout)
        if not match or ast.literal_eval(match.group(1)) != list(range(1, int(name.split("-")[1])+1)):
            raise ValueError("incorrect path answers")
    elif name == "path-all-100":
        pairs = re.findall(r"pair\s+(\d+)\s+(\d+)", stdout)
        if len(pairs) != 5050 or {(int(a), int(b)) for a, b in pairs} != {
                (a, b) for a in range(100) for b in range(a+1, 101)}:
            raise ValueError("incorrect all-pairs closure")
    elif name.startswith("breadboard-"):
        if not re.search(r"Cost\s*=\s*\d+", stdout):
            raise ValueError("missing ground optimum")

errors_found = False
with tempfile.TemporaryDirectory(prefix="infera-bench-") as directory:
    for name, (source, goal) in cases.items():
        if args.case and name not in args.case:
            continue
        target = Path(directory) / (name + ".nprolog")
        target.write_text(source + "\n> " + goal + "?\n")
        samples = []
        status = "ok"
        for _ in range(args.runs):
            start = time.perf_counter()
            try:
                result = subprocess.run([str(binary), str(target), "+RTS", "-N1", "-RTS"],
                    input=":quit\n", capture_output=True, text=True, timeout=args.timeout, cwd=directory)
            except subprocess.TimeoutExpired:
                status = "timeout"
                break
            if result.returncode or "Error:" in result.stdout or "Search depth limit" in result.stdout:
                status = "error"
                print(json.dumps({"case": name, "status": status,
                    "stdout": result.stdout[-1500:], "stderr": result.stderr[-1500:]}), flush=True)
                break
            try:
                validate(name, result.stdout)
            except (ValueError, SyntaxError) as error:
                status = "error"
                print(json.dumps({"case": name, "status": status,
                    "validation": str(error), "stdout": result.stdout[-1500:]}), flush=True)
                break
            samples.append(time.perf_counter() - start)
        if status != "error":
            print(json.dumps({"case": name, "status": status,
                "samples_seconds": [round(value, 6) for value in samples],
                "median_seconds": round(statistics.median(samples), 6) if samples else None,
                "timeout_seconds": args.timeout if status == "timeout" else None}), flush=True)
        else:
            errors_found = True
if errors_found:
    raise SystemExit(1)

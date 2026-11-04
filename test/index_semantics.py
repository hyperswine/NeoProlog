"""Clause selection keeps Prolog's answers, and loading fact tables is linear.

Answers for `q/2` are SWI-Prolog 10.0.0's for the same clauses (solution
order and count): bound and unbound first arguments, variable heads
interleaved with keyed ones, compound and list keys, a body-guarded clause,
cut and if-then-else. The dynamic part checks that the argument index
follows assert and retract (Infera's own semantics: dynamic changes inside
findall are undone on backtracking, unlike SWI). Every query runs with the
JIT on and off.

Load time: determinism inference used to compare every pair of clauses,
and the loader appended items one at a time, so 2000 facts took ~0.9 s to
load and 4000 took ~3.4 s. Loading 4x the facts must now take well under
16x the time.
"""
import os
from pathlib import Path
import subprocess
import sys
import tempfile
import time

binary = str(Path(sys.argv[1]).resolve())

PROGRAM = """q 1 a.
q X b.
q 2 c.
q (f 1) d.
q 1 e.
q [] f.
q [_ | _] g.
q X h <- X = 2.
e : dynamic.
setup : unsafe.
setup <- assert (e 1 a), assert (e X b), assert (e 2 c), assert (e 1 d).
"""

QUERIES = [
    # SWI-Prolog 10.0.0
    ("findall (A - B) (q A B) L", "L = [1 - a, A - b, 2 - c, f 1 - d, 1 - e, [] - f, [_0 | _1] - g, 2 - h]"),
    ("findall B (q 1 B) L", "L = [a, b, e]"),
    ("findall B (q 2 B) L", "L = [b, c, h]"),
    ("findall B (q (f 1) B) L", "L = [b, d]"),
    ("findall B (q (f 2) B) L", "L = [b]"),
    ("findall B (q [x] B) L", "L = [b, g]"),
    ("findall B (q zz B) L", "L = [b]"),
    ("findall B (q 1 B, !) L", "L = [a]"),
    ("findall B ((q 1 B -> true ; B = none)) L", "L = [a]"),
    ("findall B ((q 9 B -> true ; B = none)) L", "L = [b]"),
    ("findall X (q X c) L", "L = [2]"),
    # the index follows assert and retract
    ("setup, findall V (e 1 V) L1, findall V (e 2 V) L2", "L1 = [a, b, d], L2 = [b, c]"),
    ("setup, retract (e 1 a), findall V (e 1 V) L", "L = [b, d]"),
    ("setup, assert (e 3 q), findall V (e 3 V) L", "L = [b, q]"),
    ("setup, assert (e 0 first), findall (K - V) (e K V) L", "L = [1 - a, K - b, 2 - c, 1 - d, 0 - first]"),
]


def run(source, query, jit):
    with tempfile.TemporaryDirectory(prefix="infera-index-") as tmp:
        target = Path(tmp) / "main.nprolog"
        target.write_text(source + "> " + query + "?\n")
        start = time.perf_counter()
        result = subprocess.run([binary, str(target)], cwd=tmp, env=dict(os.environ, INFERA_JIT=jit),
                                stdin=subprocess.DEVNULL, capture_output=True, text=True, timeout=120)
        elapsed = time.perf_counter() - start
        lines = result.stdout.splitlines()
        index = next(i for i, line in enumerate(lines) if line.startswith("Loaded "))
        return lines[index + 2].strip(), elapsed


failures = []
for jit in ("1", "0"):
    for query, expected in QUERIES:
        answer, _ = run(PROGRAM, query, jit)
        if answer != expected:
            failures.append("JIT=%s %s: got %r, want %r" % (jit, query, answer, expected))


def facts(n):
    return "".join("fact %d a%d c%d.\n" % (i, i, i % 7) for i in range(n))


def load_time(n):
    best = None
    for _ in range(3):
        answer, seconds = run(facts(n), "fact %d A C" % (n - 1), "1")
        if answer != "A = a%d, C = c%d" % (n - 1, (n - 1) % 7):
            failures.append("fact table %d: %r" % (n, answer))
        best = seconds if best is None else min(best, seconds)
    return best


small, large = load_time(1000), load_time(4000)
ratio = large / max(small, 1e-3)
print("load 1000 facts %.3fs, 4000 facts %.3fs, ratio %.1f" % (small, large, ratio))
if ratio > 10:
    failures.append("loading 4x the facts took %.1fx the time" % ratio)

if failures:
    print("\n".join(failures))
    sys.exit(1)
print("index semantics: ok")

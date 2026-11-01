"""Default tabling skips deterministic counter-driven loops, and only them.

See docs/2026-11-01-AUTO-TABLING-COST.md for the criterion. Checks, with the
JIT on and off: counter loops run untabled and fast; fib/tak-style recursion
stays tabled (memoised); an explicit `table` still forces tabling; a counter
loop whose clauses are not exclusive keeps tabling (and its deduplicated
answers) and gets the `perf-tabled-counter-loop` hint.
"""
import json
import os
from pathlib import Path
import subprocess
import sys
import tempfile
import time

binary = str(Path(sys.argv[1]).resolve())

NREV = """app [] L L.
app [H | T] L [H | R] <- app T L R.
nrev [] [].
nrev [H | T] R <- nrev T RT, app RT [H] R.
range N N [N].
range I N [I | T] <- I < N, I1 is I + 1, range I1 N T.
bench_nrev 0.
bench_nrev K <- K > 0, range 1 30 L, nrev L R, K1 is K - 1, bench_nrev K1.
count 0 A A.
count N A R <- N > 0, A1 is A + 1, N1 is N - 1, count N1 A1 R.
fib 0 0.
fib 1 1.
fib N F <- N > 1, N1 is N - 1, N2 is N - 2, fib N1 F1, fib N2 F2, F is F1 + F2.
dup 0 a.
dup 0 a.
dup N X <- N > 0, N1 is N - 1, dup N1 X.
"""


def run(source, query, jit, timeout=120):
    with tempfile.TemporaryDirectory(prefix="infera-autotable-") as tmp:
        target = Path(tmp) / "main.nprolog"
        target.write_text(source + "> " + query + "\n")
        start = time.perf_counter()
        result = subprocess.run([binary, str(target)], cwd=tmp, env=dict(os.environ, INFERA_JIT=jit),
                                stdin=subprocess.DEVNULL, capture_output=True, text=True, timeout=timeout)
        elapsed = time.perf_counter() - start
        lines = result.stdout.splitlines()
        index = next(i for i, line in enumerate(lines) if line.startswith("Loaded "))
        return lines[index + 2].strip(), elapsed


def tabled(source, name):
    with tempfile.TemporaryDirectory(prefix="infera-autotable-") as tmp:
        target = Path(tmp) / "main.nprolog"
        target.write_text(source)
        result = subprocess.run([binary, str(target)], cwd=tmp, input=":sig %s\n" % name,
                                capture_output=True, text=True, timeout=60)
        line = next(l for l in result.stdout.splitlines() if "tabled:" in l)
        return "tabled: yes" in line


assert not tabled(NREV, "bench_nrev"), "counter loop must not be tabled by default"
assert not tabled(NREV, "count"), "accumulating counter loop must not be tabled by default"
assert tabled(NREV, "fib"), "fib must stay tabled"
assert tabled(NREV, "dup"), "non-exclusive counter loop must stay tabled"
assert tabled(NREV + "bench_nrev : table.\n", "bench_nrev"), "explicit table must force tabling"

for jit in ("1", "0"):
    answer, seconds = run(NREV, "bench_nrev 30000, count 200000 0 R?", jit)
    assert answer == "R = 200000", answer
    # Tabled, this took more than 60 s; untabled about 0.4 s (JIT) / 3 s (no JIT).
    assert seconds < 30, ("bench_nrev 30000", jit, seconds)
    answer, seconds = run(NREV, "fib 90 F?", jit, timeout=30)
    assert answer == "F = 2880067194370816120", answer  # only reachable when memoised
    assert seconds < 10, ("fib 90", jit, seconds)
    answer, _ = run(NREV, "findall X (dup 2 X) L?", jit)
    assert answer == "L = [a]", answer  # tabled answers stay deduplicated
    print("autotable jit=%s ok" % jit)

with tempfile.TemporaryDirectory(prefix="infera-autotable-") as tmp:
    target = Path(tmp) / "main.nprolog"
    target.write_text(NREV)
    rows = json.loads(subprocess.run([binary, "check", "--json", str(target)], cwd=tmp,
                                     capture_output=True, text=True, timeout=60).stdout)
    hints = [d for d in rows if d["code"] == "perf-tabled-counter-loop"]
    assert len(hints) == 1 and "dup" in hints[0]["message"], rows
    target.write_text(NREV + "dup : table.\n")
    rows = json.loads(subprocess.run([binary, "check", "--json", str(target)], cwd=tmp,
                                     capture_output=True, text=True, timeout=60).stdout)
    assert not [d for d in rows if d["code"] == "perf-tabled-counter-loop"], rows
print("autotable: ok")

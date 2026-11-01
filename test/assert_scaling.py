"""assert/1 must scale linearly: n asserts followed by one scan of the facts.

Dynamic facts used to be appended with `old ++ [new]`, a lazily left-nested
chain that cost O(n) per fact to force, so 100k asserts took minutes.
"""
from pathlib import Path
import subprocess
import sys
import tempfile
import time

binary = str(Path(sys.argv[1]).resolve())

PROGRAM = """<- notable.
fact : dynamic.
fill : unsafe.
fill 0.
fill N <- N > 0, assert (fact N), N1 is N - 1, fill N1.
sum [] S S.
sum [X | Xs] A S <- A1 is A + X, sum Xs A1 S.
bench : unsafe.
bench N R <- fill N, findall X (fact X) L, sum L 0 R.
"""


def run(n):
    with tempfile.TemporaryDirectory(prefix="infera-assert-") as tmp:
        target = Path(tmp) / "main.nprolog"
        target.write_text(PROGRAM + "> bench %d R?\n" % n)
        start = time.perf_counter()
        result = subprocess.run([binary, str(target)], cwd=tmp, stdin=subprocess.DEVNULL,
                                capture_output=True, text=True, timeout=120)
        elapsed = time.perf_counter() - start
        assert "R = %d" % (n * (n + 1) // 2) in result.stdout, result.stdout[-500:]
        return elapsed


small, large = run(20000), run(200000)
print("assert scaling: 20k %.3fs, 200k %.3fs" % (small, large))
# Linear growth is ~10x; the quadratic version was ~100x (and minutes at 200k).
assert large < 30 * max(small, 0.02), (small, large)

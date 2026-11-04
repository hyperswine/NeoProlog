"""Long list builds and tree inserts must scale linearly-ish.

Two regressions this guards, each measured as a time ratio between a size
and four times that size, with the JIT on and off:

- a JIT kernel that runs out of allocation budget bails out, and every
  re-entry under the same heap limit used to bail again after redoing the
  whole remaining span (a 100000-element list build took ~9 s, 40 ms
  without the JIT);
- the occurs check re-walked the untouched subtree on every head binding of
  a tree insert, making repeated inserts quadratic.

Linear work gives a ratio near 4; the regressions gave 12-900.
"""
import os
from pathlib import Path
import subprocess
import sys
import tempfile
import time

binary = str(Path(sys.argv[1]).resolve())

PROGRAM = """<- notable.
mkl 0 [].
mkl N [N | T] <- N > 0, N1 is N - 1, mkl N1 T.
len [] A A.
len [_ | T] A N <- A1 is A + 1, len T A1 N.
ins K V t (t K V t t).
ins K V (t K0 V0 L R) (t K0 V0 L1 R) <- K < K0, ins K V L L1.
ins K V (t K0 V0 L R) (t K0 V0 L R1) <- K > K0, ins K V R R1.
ins K V (t K _ L R) (t K V L R).
build 0 _ T T.
build N S T0 T <- N > 0, X is (S * 7919 + 13) % 100003, ins X N T0 T1, N1 is N - 1, build N1 X T1 T.
tlist N K <- mkl N L, len L 0 K.
ttree N K <- build N 1 t T, K = N.
"""

CASES = [("tlist", 50000, 200000), ("ttree", 5000, 20000)]
LIMIT = 10.0


def run(query, jit):
    env = dict(os.environ, INFERA_JIT=jit)
    with tempfile.TemporaryDirectory(prefix="infera-unify-scaling-") as tmp:
        target = Path(tmp) / "main.nprolog"
        target.write_text(PROGRAM + "> " + query + "\n")
        start = time.perf_counter()
        result = subprocess.run([binary, str(target)], cwd=tmp, env=env, stdin=subprocess.DEVNULL,
                                capture_output=True, text=True, timeout=600)
        return time.perf_counter() - start, result.stdout


failures = []
for jit in ("1", "0"):
    for name, small, large in CASES:
        times = []
        for n in (small, large):
            best = None
            for _ in range(3):
                dt, out = run("%s %d K?" % (name, n), jit)
                if "K = %d" % n not in out:
                    failures.append("%s %d (JIT=%s): no answer K = %d" % (name, n, jit, n))
                best = dt if best is None else min(best, dt)
            times.append(best)
        ratio = times[1] / max(times[0], 1e-3)
        print("%s JIT=%s: %d -> %.3fs, %d -> %.3fs, ratio %.1f" % (name, jit, small, times[0], large, times[1], ratio))
        if ratio > LIMIT:
            failures.append("%s (JIT=%s): ratio %.1f > %.1f" % (name, jit, ratio, LIMIT))

if failures:
    print("\n".join(failures))
    sys.exit(1)
print("unify scaling: ok")

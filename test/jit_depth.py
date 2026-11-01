"""JIT and interpreter must agree on the resolution depth limit.

Depth is continuation depth: a last call does not deepen it, so tail loops
run unbounded in the interpreter and must also run unbounded in native
kernels. Non-tail recursion still exhausts at the same point in both.
"""
import os
from pathlib import Path
import subprocess
import sys
import tempfile

binary = str(Path(sys.argv[1]).resolve())

PROGRAM = """<- notable.
loop 0.
loop N <- N > 0, N1 is N - 1, loop N1.
app [] L L.
app [H | T] L [H | R] <- app T L R.
range N N [N].
range I N [I | T] <- I < N, I1 is I + 1, range I1 N T.
nrev [] [].
nrev [H | T] R <- nrev T RT, app RT [H] R.
len [] 0.
len [_ | T] N <- len T M, N is M + 1.
deepnrev 0 L R <- nrev L R.
deepnrev N L R <- N > 0, N1 is N - 1, deepnrev N1 L R, true.
tapp K <- range 1 150000 L, app L [x] M, len [a, b] K.
tnrev N K <- range 1 N L, nrev L R, len R K.
tlen N K <- range 1 N L, len L K.
tdeep D K <- range 1 400 L, deepnrev D L R, len R K.
"""

QUERIES = [
    ("loop 99999?", "true."),
    ("loop 100000?", "true."),
    ("loop 150000?", "true."),
    ("loop 1000000?", "true."),
    ("tapp K?", "K = 2"),
    ("tnrev 300 K?", "K = 300"),
    # Non-tail recursion is bounded by the same limit in both modes, including
    # the native nrev kernel entered close to the limit.
    ("tlen 99990 K?", None),
    ("tlen 100001 K?", None),
] + [("tdeep %d K?" % n, None) for n in range(99560, 99640, 8)]


def answers(jit):
    env = dict(os.environ, INFERA_JIT=jit)
    with tempfile.TemporaryDirectory(prefix="infera-jit-depth-") as tmp:
        out = []
        for query, _ in QUERIES:
            target = Path(tmp) / "main.nprolog"
            target.write_text(PROGRAM + "> " + query + "\n")
            result = subprocess.run([binary, str(target)], cwd=tmp, env=env, stdin=subprocess.DEVNULL,
                                    capture_output=True, text=True, timeout=600)
            lines = result.stdout.splitlines()
            index = next(i for i, line in enumerate(lines) if line.startswith("Loaded "))
            out.append(lines[index + 2].strip())
        return out


on, off = answers("1"), answers("0")
for (query, expected), a, b in zip(QUERIES, on, off):
    assert a == b, (query, "jit", a, "interpreter", b)
    assert expected is None or a == expected, (query, a, expected)
    print(query, "->", a)
assert len(set(on[-10:])) == 2, on[-10:]  # the deepnrev sweep crosses the limit
print("jit depth: %d queries agree" % len(QUERIES))

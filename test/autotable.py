"""Default tabling skips deterministic counter-driven loops and distinct-answer
counter generators (between/3 shape), and only them.

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


# Nondeterministic counter generators (between/3 shape) whose answers are
# provably distinct and finite are not tabled either; see the criterion in
# docs/2026-11-01-AUTO-TABLING-COST.md. Tabled, findall over btw 1 400 took
# about 10 s; untabled it takes milliseconds.
GEN = """btw L H L <- L <= H.
btw L H X <- L < H, L1 is L + 1, btw L1 H X.
dn H L H <- H >= L.
dn H L X <- H > L, H1 is H - 1, dn H1 L X.
cg L H a <- L <= H.
cg L H X <- L < H, L1 is L + 1, cg L1 H X.
nat N N.
nat N X <- N1 is N + 1, nat N1 X.
mv L H L <- L <= H.
mv L H X <- L < H, L1 is L + 1, H1 is H + 1, mv L1 H1 X.
d2 L H L <- L <= H.
d2 L H L <- L >= H.
d2 L H X <- L < H, L1 is L + 1, d2 L1 H X.
len [] A A.
len [_ | T] A N <- A1 is A + 1, len T A1 N.
sum [] A A.
sum [X | T] A S <- A1 is A + X, sum T A1 S.
"""

assert not tabled(GEN, "btw"), "between-style generator must not be tabled by default"
assert not tabled(GEN, "dn"), "counting-down generator must not be tabled by default"
# Must stay tabled: the answer does not carry the counter, so untabled it
# would repeat `a` (cg); no bounding guard (nat); the bound moves with the
# counter (mv); two base clauses can give the same answer (d2).
for name in ("cg", "nat", "mv", "d2"):
    assert tabled(GEN, name), name + " must stay tabled"
assert tabled(GEN + "btw : table.\n", "btw"), "explicit table must force tabling"

# Answers as SWI-Prolog gives them for the same programs (SWI-Prolog 10.0.0).
SWI = [
    ("findall X (btw 1 10 X) L?", "L = [1, 2, 3, 4, 5, 6, 7, 8, 9, 10]"),
    ("findall X (btw 5 3 X) L?", "L = []"),
    ("findall X (dn 10 1 X) L?", "L = [10, 9, 8, 7, 6, 5, 4, 3, 2, 1]"),
    ("findall Y (btw 1 4 X, btw 1 X Y) L?", "L = [1, 1, 2, 1, 2, 3, 1, 2, 3, 4]"),
    ("findall X (btw (-3) 2 X) L?", "L = [-3, -2, -1, 0, 1, 2]"),
    ("findall X (btw 1 2000 X) L, len L 0 N, sum L 0 S?", "L = [", ),
    ("findall X (cg 1 3 X) L?", "L = [a]"),
]

for jit in ("1", "0"):
    for query, expected in SWI:
        answer, _ = run(GEN, query, jit)
        if query.startswith("findall X (btw 1 2000"):
            assert answer.endswith("N = 2000, S = 2001000"), answer
        else:
            assert answer == expected, (query, answer)
    for n in (400, 2000):
        answer, seconds = run(GEN, "findall X (btw 1 %d X) L, len L 0 N?" % n, jit)
        assert answer.endswith("N = %d" % n), answer
        assert seconds < 5, ("btw", n, jit, seconds)
    print("autotable generators jit=%s ok" % jit)

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

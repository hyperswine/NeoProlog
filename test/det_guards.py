"""Comparison guards exclude a later clause that repeats a head variable.

`ins K V (t K0 V0 L R) _ <- K < K0, ...`, `... <- K > K0, ...` and a later
`ins K V (t K _ L R) _` cannot both succeed: identical keys compare equal.
Determinism inference now sees that, so `ins/4` is semidet and commits
after its first solution (a 30000-key tree build used to keep a choice
point per level). A repeated variable in an *earlier* clause than the
comparison (`range N N [N]` before `range I N _ <- I < N`) still does not
count, because committing would hide the comparison's error for terms it
cannot compare. Answers are SWI-Prolog 10.0.0's; every query runs with the
JIT on and off.
"""
import os
from pathlib import Path
import subprocess
import sys
import tempfile

binary = str(Path(sys.argv[1]).resolve())

PROGRAM = """ins K V t (t K V t t).
ins K V (t K0 V0 L R) (t K0 V0 L1 R) <- K < K0, ins K V L L1.
ins K V (t K0 V0 L R) (t K0 V0 L R1) <- K > K0, ins K V R R1.
ins K V (t K _ L R) (t K V L R).
look K (t K V _ _) V.
look K (t K0 _ L _) V <- K < K0, look K L V.
look K (t K0 _ _ R) V <- K > K0, look K R V.
range N N [N].
range I N [I | T] <- I < N, I1 is I + 1, range I1 N T.
build [] T T.
build [K - V | Ps] T0 T <- ins K V T0 T1, build Ps T1 T.
"""

QUERIES = [
    ("build [3 - a, 1 - b, 5 - c, 1 - d, 4 - e] t T", "T = t 3 a (t 1 d t t) (t 5 c (t 4 e t t) t)"),
    ("build [3 - a, 1 - b] t T, findall V (look 1 T V) L", "T = t 3 a (t 1 b t t) t, L = [b]"),
    ("findall T (ins 2 x (t 2 y t t) T) L", "L = [t 2 x t t]"),
    ("findall T (ins 1 x (t 2 y t t) T) L", "L = [t 2 y (t 1 x t t) t]"),
    ("findall T (ins K x (t 2 y t t) T) L", None),  # unbound key: same as before (error)
    ("findall L (range 1 3 L) Ls", "Ls = [[1, 2, 3]]"),
    ("findall L (range 3 3 L) Ls", "Ls = [[3]]"),
]

SIGS = {"ins": "semidet", "look": "nondet", "range": "nondet"}


def run(query, jit):
    with tempfile.TemporaryDirectory(prefix="infera-det-guards-") as tmp:
        target = Path(tmp) / "main.nprolog"
        target.write_text(PROGRAM + "> " + query + "?\n")
        result = subprocess.run([binary, str(target)], cwd=tmp, env=dict(os.environ, INFERA_JIT=jit),
                                stdin=subprocess.DEVNULL, capture_output=True, text=True, timeout=60)
        lines = (result.stdout + result.stderr).splitlines()
        index = next(i for i, line in enumerate(lines) if line.startswith("Loaded "))
        return lines[index + 2].strip()


def det(name):
    with tempfile.TemporaryDirectory(prefix="infera-det-guards-") as tmp:
        target = Path(tmp) / "main.nprolog"
        target.write_text(PROGRAM)
        out = subprocess.run([binary, str(target)], cwd=tmp, input=":sig %s\n" % name,
                             capture_output=True, text=True, timeout=60).stdout
        line = next(l for l in out.splitlines() if "inferred:" in l)
        return line.split(":", 2)[2].split()[0]


failures = []
for name, want in SIGS.items():
    got = det(name)
    if got != want:
        failures.append("%s inferred %s, want %s" % (name, got, want))
for query, expected in QUERIES:
    answers = [run(query, jit) for jit in ("1", "0")]
    if answers[0] != answers[1]:
        failures.append("JIT on/off differ for %s: %r" % (query, answers))
    if expected is None:
        if not answers[0].startswith("Error"):
            failures.append("%s: expected an error, got %r" % (query, answers[0]))
    elif answers[0] != expected:
        failures.append("%s: got %r, want %r" % (query, answers[0], expected))

if failures:
    print("\n".join(failures))
    sys.exit(1)
print("det guards: ok")

"""If-then-else with a single simple test decides it without a choice point.

`(X == 0 -> ... ; ...)`, `!=`, `=` between ground terms and arithmetic
comparisons on the fast path no longer push a choice point, a scope and a
counter. Everything else (non-ground `=`, unbound `!=`, errors) takes the
general path. Answers match SWI-Prolog 10.0.0 for the same clauses (ite
over ==, =, < and >, cut in the then branch, an inner generator, and
instantiation and type errors). Every query runs with the JIT on and off.
"""
import os
from pathlib import Path
import subprocess
import sys
import tempfile

binary = str(Path(sys.argv[1]).resolve())

PROGRAM = 't1 X R <- (X == 0 -> R = zero ; R = other).\nt2 X R <- (X != a -> R = nota ; R = isa).\nt3 X R <- (X = f 1 -> R = yes ; R = no).\nt4 X R <- (X < 3 -> R = small ; X > 5 -> R = big ; R = mid).\nt5 X R <- member2 X [1, 2, 3], (X >= 2 -> R = X ; fail).\nmember2 X [X | _].\nmember2 X [_ | T] <- member2 X T.\nt6 : unsafe.\nt6 X R <- (X == 1 -> ! , R = cut ; R = nocut).\nt6 _ late.\nt7 R <- (Y = 1 -> R = Y ; R = unbound).\nt8 R <- (Z < 1 -> R = a ; R = b).\n'

QUERIES = [('findall R (t1 0 R) L', 'L = [zero]'), ('findall R (t1 1.0 R) L', 'L = [other]'), ('findall R (t1 0.0 R) L', 'L = [other]'), ('findall R (t2 b R) L', 'L = [nota]'), ('findall R (t2 a R) L', 'L = [isa]'), ('findall R (t3 (f 1) R) L', 'L = [yes]'), ('findall R (t3 (f 2) R) L', 'L = [no]'), ('findall R (t3 Q R) L', 'L = [yes]'), ('findall R (t4 1 R) L', 'L = [small]'), ('findall R (t4 4 R) L', 'L = [mid]'), ('findall R (t4 9 R) L', 'L = [big]'), ('findall R (t4 4.5 R) L', 'L = [mid]'), ('findall R (t5 X R) L', 'L = [2, 3]'), ('findall R (t6 1 R) L', 'L = [cut]'), ('findall R (t6 2 R) L', 'L = [nocut, late]'), ('findall R (t7 R) L', 'L = [1]'), ('t8 R', 'Error: arithmetic expression is not sufficiently instantiated: _G1'), ('findall R (t4 a R) L', 'Error: expected a numeric expression, but got: a')]


def run(query, jit):
    with tempfile.TemporaryDirectory(prefix="infera-ite-") as tmp:
        target = Path(tmp) / "main.nprolog"
        target.write_text(PROGRAM + "> " + query + "?\n")
        result = subprocess.run([binary, str(target)], cwd=tmp, env=dict(os.environ, INFERA_JIT=jit),
                                stdin=subprocess.DEVNULL, capture_output=True, text=True, timeout=60)
        lines = (result.stdout + result.stderr).splitlines()
        index = next(i for i, line in enumerate(lines) if line.startswith("> " + query.split()[0]))
        return lines[index + 1].strip()


failures = []
for jit in ("1", "0"):
    for query, expected in QUERIES:
        got = run(query, jit)
        if got != expected:
            failures.append("JIT=%s %s: got %r, want %r" % (jit, query, got, expected))
if failures:
    print("\n".join(failures))
    sys.exit(1)
print("ite parity: ok")

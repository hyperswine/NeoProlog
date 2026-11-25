#!/usr/bin/env python3
"""The 2x admission gate for std/ (docs/2026-11-15-GENERAL-PURPOSE.md, Step 2).

Library code stays in Infera while it is within 2x of a native version.
Each workload runs three ways, all printing the same checksum:

  std     the library predicate, as a program uses it
  local   the same algorithm written in the program (inferred signatures)
  swipl   SWI-Prolog's library or builtin (C or optimised Prolog)

Times are whole-process medians minus each engine's startup on an empty
program, so they compare the work. Every run's answer is checked.

python3 bench/std-gate.py "$(cabal list-bin exe:infera)" [--runs 3] [--json]
"""
import argparse
import json
import os
from pathlib import Path
import shutil
import statistics
import subprocess
import tempfile
import time

# Shared helpers: a deterministic pseudo-random list and a counting loop.
INFERA_COMMON = """<- notable.
lcg 0 _ [].
lcg N S [X | Xs] <- N > 0, S1 is (S * 1103515245 + 12345) % 2147483648, X is S1 % 1000000, N1 is N - 1, lcg N1 S1 Xs.
"""
SWI_COMMON = """lcg(0, _, []) :- !.
lcg(N, S, [X|Xs]) :- S1 is (S * 1103515245 + 12345) mod 2147483648, X is S1 mod 1000000, N1 is N - 1, lcg(N1, S1, Xs).
plus1(X, Y) :- Y is X + 1.
add(X, A, B) :- B is A + X.
"""

# name: (infera std goal, infera local clauses, infera local goal, swi goal)
WORKLOADS = {
    "reverse": (
        "rloop 2000 0 R",
        """rloop 0 A A.
rloop K A R <- K > 0, numlist 1 1000 L, my_rev L [] [X | _], A1 is A + X, K1 is K - 1, rloop K1 A1 R.
my_rev [] A A.
my_rev [X | Xs] A R <- my_rev Xs [X | A] R.""",
        "rloop 2000 0 R",
        "rloop(2000, 0, R)"),
    "sum_list": ("numlist 1 1000000 L, sum_list L R", """my_sum [] S S.
my_sum [X | Xs] A S <- B is A + X, my_sum Xs B S.""", "numlist 1 1000000 L, my_sum L 0 R",
        "numlist(1, 1000000, L), sum_list(L, R)"),
    "length": ("numlist 1 1000000 L, length L R", """my_len [] N N.
my_len [_ | Xs] A N <- B is A + 1, my_len Xs B N.""", "numlist 1 1000000 L, my_len L 0 R",
        "numlist(1, 1000000, L), length(L, R)"),
    "msort": ("lcg 200000 7 L, msort L S, last S R", """my_last [X] X.
my_last [_, Y | Ys] X <- my_last [Y | Ys] X.""", "lcg 200000 7 L, msort L S, my_last S R",
        "lcg(200000, 7, L), msort(L, S), last(S, R)"),
    "maplist": ("numlist 1 300000 L, maplist plus1 L M, sum_list M R", """plus1 X Y <- Y is X + 1.
my_map _ [] [].
my_map F [X | Xs] [Y | Ys] <- plus1 X Y, my_map F Xs Ys.""", "numlist 1 300000 L, my_map plus1 L M, sum_list M R",
        "numlist(1, 300000, L), maplist(plus1, L, M), sum_list(M, R)"),
    "foldl": ("numlist 1 1000000 L, foldl add L 0 R", """add X A B <- B is A + X.
my_fold _ [] A A.
my_fold F [X | Xs] A R <- add X A B, my_fold F Xs B R.""", "numlist 1 1000000 L, my_fold add L 0 R",
        "numlist(1, 1000000, L), foldl(add, L, 0, R)"),
    "nth1": ("numlist 1 2000 L, nloop 2000 L 0 R", """my_nth 1 [X | _] X.
my_nth N [_ | Xs] X <- N > 1, M is N - 1, my_nth M Xs X.
mloop 0 _ A A.
mloop K L A R <- K > 0, my_nth K L X, A1 is A + X, K1 is K - 1, mloop K1 L A1 R.""", "numlist 1 2000 L, mloop 2000 L 0 R",
        "numlist(1, 2000, L), nloop(2000, L, 0, R)"),
    "assoc": ("numlist 1 50000 L, pair_up L Ps, list_to_assoc Ps A, look Ps A 0 R", None, None,
        "numlist(1, 50000, L), pair_up(L, Ps), list_to_assoc(Ps, A), look(Ps, A, 0, R)"),
    "setof": ("lcg 100000 5 L, setof X (member X L) S, length S R", None, None,
        "lcg(100000, 5, L), setof(X, member(X, L), S), length(S, R)"),
    "between": ("aggregate_all count (between 1 1000000 _) R", """my_count Lo Hi A A <- Lo > Hi.
my_count Lo Hi A R <- Lo <= Hi, B is A + 1, L1 is Lo + 1, my_count L1 Hi B R.""", "my_count 1 1000000 0 R",
        "aggregate_all(count, between(1, 1000000, _), R)"),
}

# Program-side helpers each std workload needs, in both languages.
INFERA_EXTRA = {
    "reverse": """rloop 0 A A.
rloop K A R <- K > 0, numlist 1 1000 L, reverse L [X | _], A1 is A + X, K1 is K - 1, rloop K1 A1 R.""",
    "maplist": "plus1 X Y <- Y is X + 1.",
    "foldl": "add X A B <- B is A + X.",
    "nth1": """nloop 0 _ A A.
nloop K L A R <- K > 0, nth1 K L X, A1 is A + X, K1 is K - 1, nloop K1 L A1 R.""",
    "assoc": """<- import "std/assoc".
pair_up [] [].
pair_up [I | Is] [pair K I | Ps] <- K is (I * 7919) % 50021, pair_up Is Ps.
look [] _ A A.
look [pair K _ | Ps] T A R <- get_assoc K T V, B is A + V, look Ps T B R.""",
}
SWI_EXTRA = {
    "reverse": "rloop(0, A, A) :- !.\nrloop(K, A, R) :- numlist(1, 1000, L), reverse(L, [X|_]), A1 is A + X, K1 is K - 1, rloop(K1, A1, R).",
    "nth1": "nloop(0, _, A, A) :- !.\nnloop(K, L, A, R) :- nth1(K, L, X), A1 is A + X, K1 is K - 1, nloop(K1, L, A1, R).",
    "assoc": ":- use_module(library(assoc)).\npair_up([], []).\npair_up([I|Is], [K-I|Ps]) :- K is (I * 7919) mod 50021, pair_up(Is, Ps).\nlook([], _, A, A).\nlook([K-_|Ps], T, A, R) :- get_assoc(K, T, V), B is A + V, look(Ps, T, B, R).",
}


def run(cmd, stdin, cwd, timeout):
    start = time.perf_counter()
    p = subprocess.run(cmd, input=stdin, capture_output=True, text=True, cwd=cwd, timeout=timeout)
    return time.perf_counter() - start, p


def infera(binary, dirpath, name, clauses, goal, runs):
    path = Path(dirpath) / (name + ".nprolog")
    path.write_text(INFERA_COMMON + clauses + "\nbench R <- " + goal + ".\n> bench R?\n")
    samples, answer = [], None
    for _ in range(runs + 1):
        t, p = run([binary, str(path), "+RTS", "-N1", "-RTS"], ":q\n", dirpath, 300)
        lines = [l for l in p.stdout.splitlines() if l.startswith(("R = ", "Error", "false"))]
        got = lines[-1] if lines else p.stdout[-200:]
        answer = answer or got
        if got != answer or not got.startswith("R = "):
            raise SystemExit(f"{name}: infera answered {got!r}")
        samples.append(t)
    return statistics.median(samples[1:]), answer.split("R = ")[-1].split(",")[0].strip()


def swipl(binary, dirpath, name, clauses, goal, runs):
    path = Path(dirpath) / (name + ".pl")
    path.write_text(SWI_COMMON + clauses + f"\nmain :- {goal}, write(R), nl.\n")
    samples, answer = [], None
    for _ in range(runs + 1):
        t, p = run([binary, "-q", "-g", "main", "-t", "halt", str(path)], "", dirpath, 300)
        got = p.stdout.strip()
        answer = answer or got
        if got != answer or p.returncode != 0:
            raise SystemExit(f"{name}: swipl answered {got!r} {p.stderr[-300:]}")
        samples.append(t)
    return statistics.median(samples[1:]), answer


def main():
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("binary")
    ap.add_argument("--swipl", default=os.environ.get("SWIPL_BIN") or shutil.which("swipl"))
    ap.add_argument("--runs", type=int, default=3)
    ap.add_argument("--json", action="store_true")
    ap.add_argument("--workload", action="append", choices=WORKLOADS, help="measure only selected workloads (repeatable)")
    a = ap.parse_args()
    rows = []
    with tempfile.TemporaryDirectory(prefix="std-gate-") as d:
        base_i, _ = infera(a.binary, d, "empty", "zero 0.", "zero R", a.runs)
        base_s, _ = swipl(a.swipl, d, "empty", "", "R = 0", a.runs) if a.swipl else (0, None)
        for name, (std_goal, local, local_goal, swi_goal) in WORKLOADS.items():
            if a.workload and name not in a.workload:
                continue
            t_std, v_std = infera(a.binary, d, name + "_std", INFERA_EXTRA.get(name, ""), std_goal, a.runs)
            t_loc, v_loc = (infera(a.binary, d, name + "_local", local, local_goal, a.runs) if local else (None, None))
            t_swi, v_swi = (swipl(a.swipl, d, name, SWI_EXTRA.get(name, ""), swi_goal, a.runs) if a.swipl else (None, None))
            for other in (v_loc, v_swi):
                if other is not None and other != v_std:
                    raise SystemExit(f"{name}: answers differ: std {v_std}, other {other}")
            w = lambda t, b: None if t is None else max(t - b, 0.0)
            row = {"workload": name, "answer": v_std, "std_s": w(t_std, base_i),
                   "local_s": w(t_loc, base_i), "swipl_s": w(t_swi, base_s)}
            row["std_vs_swipl"] = (row["std_s"] / row["swipl_s"]) if row["swipl_s"] else None
            row["std_vs_local"] = (row["std_s"] / row["local_s"]) if row["local_s"] else None
            if name == "foldl":
                # Same shipped loop, but the callback is supplied by the caller.
                clauses = INFERA_EXTRA[name] + "\napply_fold F L A R <- foldl F L A R."
                elapsed, answer = infera(a.binary, d, "foldl_variable", clauses,
                                         std_goal.replace("foldl add", "apply_fold add"), a.runs)
                if answer != v_std:
                    raise SystemExit(f"foldl: variable callback returned {answer}, expected {v_std}")
                row["variable_callback_s"] = w(elapsed, base_i)
            rows.append(row)
    if a.json:
        print(json.dumps({"startup_infera_s": base_i, "startup_swipl_s": base_s, "rows": rows}, indent=1))
        return
    print(f"startup: infera {base_i:.3f} s, swipl {base_s:.3f} s (subtracted)")
    print(f"{'workload':10} {'std':>8} {'local':>8} {'swipl':>8} {'std/swipl':>10} {'std/local':>10}")
    f = lambda x, p=3: "-" if x is None else f"{x:.{p}f}"
    for r in rows:
        print(f"{r['workload']:10} {f(r['std_s']):>8} {f(r['local_s']):>8} {f(r['swipl_s']):>8} "
              f"{f(r['std_vs_swipl'], 2):>10} {f(r['std_vs_local'], 2):>10}")
        if "variable_callback_s" in r:
            print(f"  foldl with a variable callback: {r['variable_callback_s']:.3f} s")


if __name__ == "__main__":
    main()

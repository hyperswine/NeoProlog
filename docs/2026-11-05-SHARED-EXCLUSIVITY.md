# JIT clause exclusivity: inference's analysis, and errors in skipped clauses - 2026-11-05

Kind: engine change (correctness fix and small extension). Follows
[`2026-11-05-FILTER-KERNEL.md`](2026-11-05-FILTER-KERNEL.md); base is
`main` at `cedb709`.

## The bug

Native code commits to the first clause whose head and guards hold, so
`Jit.commitSafety` requires each earlier clause to exclude every later one.
Exclusivity says the later clause cannot *succeed*; it did not say the later
clause cannot *raise*. After a failure further down the list the interpreter
backtracks into the later clause and evaluates its guards, and on the
compiled path one guard can raise: `%` with a zero divisor.

```
rem3 _ [] [].
rem3 P [I | Is] Nis <- 0 is I % P, rem3 P Is Nis.
rem3 P [I | Is] [I | Nis] <- Y is 7 % I, X is I % P, X != 0, X < 5, rem3 P Is Nis.
```

`rem3 10 [0, 7] L` raises division by zero in the interpreter (the first
clause takes `0`, `7` fails both recursive clauses, and backtracking into
the third clause at `0` evaluates `7 % 0`), and answered `false` with the
JIT. It needs a later clause that divides by something the earlier one does
not, and a definite failure deeper in the recursion, so no benchmark or
example program met it. It came in with `%` in the JIT (the filter kernel).

## The fix

`laterRaisesNothingNew`: a guard-based exclusivity counts only when every
`%` the later clause evaluates divides by a non-zero literal or by a divisor
the earlier clause also evaluates (keyed by head paths, as
`exprConstraints` keys expressions). The earlier clause then raises first,
which on the compiled path is a bailout to the interpreter. Heads that
cannot both match (`headsExclusive`, the shape test split out of
`clausesExclusive`) need no such check: the later clause's guards never run.
`exprFacts` returns the divisors alongside the ranges; structural `!=`
evaluates nothing and contributes none.

## Inference's exclusivity in the JIT

The JIT had its own pairwise analysis beside `Infer.exclusive`, which
determinism inference uses. `commitSafety` now also accepts a pair that
`Infer.exclusive` proves, when every argument position that proof needs
ground is an input the entry checks can make ground: integers are already,
and list arguments get the existing entry ground check (the cons header's
ground bit). `Infer.exclusive` is exported for this. The JIT's own analysis
stays first, since it needs no ground lists (it reasons about shapes the
native code checks as it goes).

What this adds today is small. Over every program in `examples/` and
`test/core/`, the compiled and declined predicates are the same before and
after except in the new corpus, where `below/3` (exclusive by
`I + 1 < N` against `I + 1 >= N`, an expression against a head variable,
which only inference handles) now compiles. The benchmarks are unchanged
(primes 1387M -> 1388M instructions). The value is one less place where
the JIT must be taught what inference already knows.

## Correctness

- `test/core/parity-exclusive.nprolog` (new, in the `core-engine` group, 16
  queries): the `rem3` case (fails on `main`, agrees here), a non-zero
  literal divisor and a shared divisor (both still compiled), zero divisors,
  and `below/3` with ground, unbound, non-integer and bound inputs.
- `core-engine parity` over `test/core/*.nprolog` normally, with
  `--gc-limit 1`, with `INFERA_JIT=0` and with `INFERA_CORE_STREAM=0`; full
  `cabal test all`; every CI script.

## Not done

- The two analyses are still two. Inference cannot replace the JIT's
  shape reasoning, which holds for partial lists the native code checks
  element by element; the JIT's ranges are a subset of inference's guards
  and could be dropped once inference covers `k is E` against `X is E,
  X != k` with the same positions.

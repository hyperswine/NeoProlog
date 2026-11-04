# Choice points on unification-heavy programs - 2026-11-05

Kind: three engine changes plus one measured non-change. Follows
[`2026-11-04-UNIFICATION-HEAVY.md`](2026-11-04-UNIFICATION-HEAVY.md)
(items 1-3) and the 2026-11-05 unification benchmarks, which left a 3-5x gap
to SWI-Prolog on zebra, primes, deriv and a 30000-key tree insert (bst).

## (c) Determinism: comparison guards against a repeated head variable

`ins K V (t K0 V0 L R) _ <- K < K0, ...`, `... <- K > K0, ...` and a later
`ins K V (t K _ L R) _` cannot both succeed, because identical terms compare
equal. `Infer.repeatGuards` records a repeated head variable as a value
equality, and `exclusive` uses it **only for the later clause of a pair**.
When the comparison clause comes first, it raises its own error for terms
it cannot compare before the repeated-variable clause is reached. The other
order (`range N N [N]` before `range I N _ <- I < N`) stays non-exclusive,
as the 2026-11-04 doc requires, because committing would hide that error.
`ins/4` becomes semidet when the key and tree are ground. `:sig` is
unchanged on every other example, test and bench program.

## (a) Fewer choice points for clauses that fail at once

1. **Selection skips a repeated-head-variable clause when the integers
   differ.** A clause with no leading test whose head repeats a variable
   (`look K (t K V _ _) V`, the equal-key clause of `ins`) gets a selection
   guard `RelEq` between the two argument paths (`repeatedHeadGuard`). It is
   evaluated only when both are immediate integers, which are identical
   exactly when they are equal; any other value keeps the clause. Together
   with the comparison guards of the neighbouring clauses, a lookup or
   insert selects one clause and pushes no choice point.
2. **If-then-else with a single simple test is decided in place.**
   `(M == 0 -> A ; B)` pushed a choice point, a counting scope and a
   counter, and a failed test restored all branch-local state through
   `backtrackChoice`. `quickTest` now decides these directly: `==` between
   bound slots and constants, `!=` and `=` between ground terms, and an
   arithmetic comparison on the fast evaluators. Everything else, errors
   included, takes the general path.

Deferring choice-point creation in general (creating it only after the
head and guard of the first candidate succeed) was not done. With the two
changes above, the measured programs mostly select a single candidate. The
general version touches every `Alt` consumer and the collector's choice
relocation.

## (b) Skipping unchanged state on backtrack: measured, not done

As an upper bound, I built a binary that does no save or restore of tables,
dynamic facts, constraint marks or watched cells at all (unsound, never
committed). Median of 5:

| case | normal | no save/restore |
| --- | ---: | ---: |
| zebra | 2.190 s | 2.118 s |
| primes | 0.887 s | 0.909 s |
| bst | 0.446 s | 0.433 s |
| queens 9 | 0.689 s | 0.723 s |

At most about 3% is available, which is within this VM's noise. A
version-counter scheme would also need the collector to relocate
snapshots, so it is not worth the risk now.

## Results

See the table in the PR description (main d2c56c4 against this branch,
linux-x86_64, GHC 9.8.2 `-O2`, noisy shared VM, whole process, median of 5
with the JIT on and 3 with it off).

## Tests

- `test/det_guards.py`: inferred determinism of `ins`/`look`/`range`; tree
  answers against SWI-Prolog; selection cases (1 vs 1.0, atoms, compounds,
  unbound, nested paths, absent keys); JIT on/off parity.
- `test/ite_parity.py`: if-then-else answers against SWI-Prolog (==, =,
  comparisons, cut in the then branch, inner generator, instantiation and
  type errors), with the JIT on and off.

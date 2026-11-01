# The cost of default auto-tabling on iteration predicates (2026-11-01, report)

Default tabling (`predIsTabled`: recursive, pure, not structurally recursive)
also tables *iteration* predicates: tail-recursive loops driven by an integer
counter, such as `bench_nrev K`, `loop N`, `range I N L` or `zebra`'s
`loop N _ O`. Their calls never repeat a variant within one derivation, so the
table never answers anything. All it does is add work.

## Measurements

linux-x86_64, GHC 9.8.2 `-O2`, whole process, two runs each, noisy shared VM.
"v2.2.0" is `cace1e3`. "patch" is this branch, which removes the
per-answer table scan (below). `iter notable` declares only the iteration
predicates `notable` (`bench_nrev : notable. range : notable.` and
`loop : notable.`). That emulates option A without a code change.
`<- notable.` turns tabling off for the whole program.

| program | default v2.2.0 | default patch | iter notable | `<- notable.` |
| --- | ---: | ---: | ---: | ---: |
| nrev30 x1000 | 0.13 s | 0.12 s | | |
| nrev30 x3000 | 0.87 s | 0.81 s | | |
| nrev30 x10000 | 11.8 s | 11.7 s | | |
| nrev30 x30000 | >60 s (246 s once) | | 0.35 s | 0.36 s |
| zebra x300 | 4.07 s | 4.15 s | 2.08 s | 2.06 s |
| fib 27 | 0.008 s | 0.008 s | | 0.13 s |
| tak 24 16 8 | 0.06 s | **0.02 s** | | 0.60 s |

Answers are identical in every column. Tabling is worth keeping for fib and
tak (15–30x faster), and iteration predicates gain nothing from it.

## Causes

1. **Quadratic nrev loop (verified with a profiling build).** A tabled call
   continues through `CExitTable` and keeps an `AltTable` choice point, so the
   tail call `bench_nrev K1` is no longer a tail call. Each level keeps a
   live fixpoint frame, and the machine's live data grows with K. The
   machine collector (`collect`) runs about every fixed amount of
   allocation, and each run costs time proportional to the live data, so
   total cost is O(K²). In a `-p` profile at K = 10000, `collect` is
   **79 %** of time over 95 calls. At K = 3000 it is 23 %.
   A smaller O(tables) term came from `CExitTable` and
   `finishIteration` filtering the whole table map (`Map.filter teComplete`)
   on every answer and iteration: 31.5M `teComplete` and 19.5M `Term`
   comparisons at K = 3000. This branch removes it (see below), but it
   was not the dominant cost for nrev.
2. **zebra 2x (measured).** Every tabled call runs its clauses at least twice:
   the second fixpoint iteration confirms there are no new answers. The
   profile shows 3.16M `callPlain` for nrev x3000, against about 1.5M
   logical calls. zebra's `loop` contains `findall X (zebra X) [O1]` in its
   recursive clause, so the puzzle is solved twice per iteration.
3. **Side effect:** `CExitTable` has `contDepth` 0, so each tabled level
   restarts the depth count. Deep tabled recursion is not bounded by
   `maxResolutionDepth` in the same way as untabled recursion.

## What this branch changes (no semantic change intended)

`mCompletedLog`: an append-only log of tables completed so far, newest
first. Each fixpoint iteration records the log length at its start
(`fxCompletedMark`). `CExitTable` unions only the entries completed since
then, instead of `Map.filter teComplete` over the whole table map, and
`finishIteration` no longer re-filters `fxTables`, whose complete entries it
already keeps. Unlike before, a table completed in a branch that later
failed is also carried into the iteration's result. A completed table of a
pure call is valid in every branch, so this keeps more answers cached and
does not change any answer. Effect: tak 3x faster (0.06 → 0.02 s), others
unchanged within noise. Full test suite passes.

## Options for the default (not implemented: these change default semantics)

A. **Don't auto-table iteration predicates.** Extend the
   `predStructural` exclusion with "every self call is a last call and some
   argument moves by arithmetic (`N1 is N - c`, `N + c`)". This covers
   countdown and range loops and `bench_nrev`/`loop`, and leaves fib/tak
   (non-tail, several self calls) tabled. Measured effect (emulated above):
   nrev x30000 from >60 s to 0.35 s, zebra 4.1 → 2.1 s, fib/tak unchanged.
   Semantics: tabled calls return deduplicated answers and terminate on
   left recursion. An excluded predicate is never left-recursive (its
   argument moves), but a *nondeterministic* iteration predicate could now
   return duplicate answers. Restricting A to predicates inferred
   det/semidet avoids that.
B. **Keep tabling but make it cheap for non-repeating calls.** For example,
   when the first iteration finds no `ConsumedIncomplete` dependency and the
   call has no recursive variant in progress, complete after one iteration
   (no confirmation pass), and drop the `AltTable` frame so the last call
   stays a tail call. This fixes zebra's 2x and the nrev growth without
   changing which predicates are tabled, but it touches the fixpoint driver
   and needs careful proof.
C. **A table-size cap / LRU.** This bounds memory but not the frame growth
   that makes nrev quadratic, so it is not recommended on its own.
D. **Documentation only.** State that loops driven by counters should be
   declared `notable` (as `bench/bench.nprolog` already does with
   `<- notable.`), and add an `infera check` performance hint for tabled
   tail-recursive counter loops.

The recommendation is A, restricted to det/semidet, plus D. B would be a
later engine improvement.

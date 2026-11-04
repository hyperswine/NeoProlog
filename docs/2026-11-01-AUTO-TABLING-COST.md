# The cost of default auto-tabling on iteration predicates (2026-11-01, report)

> **Default behaviour change (implemented after this report, option A):**
> deterministic counter-driven loops are no longer tabled by default. See
> [Implemented: option A](#implemented-option-a) for the exact criterion,
> what stays tabled, and measurements.

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

The recommendation was A, restricted to deterministic loops, plus D. It is
now implemented (below). B would be a later engine improvement.

## Implemented: option A

**This changes the default.** A predicate that previously was auto-tabled is
now untabled when it is a *deterministic counter-driven loop*. An explicit
`table` flag still forces tabling, and `notable` / `<- notable.` behave as
before.

### Criterion

A predicate is a deterministic counter-driven loop when all of these hold
(`Infera.Infer.counterLoop`, `guardExclusive`, `Program.predIsDetCounterLoop`):

1. **Direct self-recursion only.** It reaches itself, and no other predicate
   it calls can reach it (mutual recursion keeps the general rule).
2. **Last-call recursion.** At least one clause calls the predicate. In every
   such clause there is exactly one self-call anywhere in the body, and it is
   the last top-level body goal (not inside `;`, `->`, `findall`, ...).
3. **A counter.** For each self-call there is an argument position `i` where
   the head has a variable `V`, the self-call has a variable `V1`, and a
   top-level body goal is `V1 is V - c`, `V1 is V + c` or `V1 is c + V`, with
   `c` a positive integer literal.
4. **Deterministic.** Either the inferred determinism is `det` or `semidet`,
   or clause selection is exclusive on the counter: exactly one clause
   recurses; every other clause has a distinct integer literal at a counter
   position `i`; and the recursive clause has a top-level guard `V > k`,
   `V >= k`, `V < k` or `V <= k` that every one of those literals fails.

**Distinct-answer counter generators (2026-11-05).** A nondeterministic
counter loop is also left untabled when its answers are provably the same,
in the same multiplicity, with and without a table
(`Infera.Infer.distinctCounterGenerator`, `Program.predDistinctCounter`).
That is the `between/3` shape, and it needs points 1-3 above plus all of these:

5. **Two clauses.** Exactly one base clause and one recursive clause.
6. **Only arithmetic in the bodies.** Apart from the final self-call, every
   body goal is a comparison (`<`, `>`, `<=`, `>=`) or, in the recursive
   clause only, an `is` goal. No goal can produce more than one solution.
7. **A bounded, monotonic counter.** The counter `V` is stepped `V1 is V + c`
   (`c + V`) with a guard `V < B` or `V <= B`, or stepped `V1 is V - c` with
   `V > B` or `V >= B`. `B` is an integer literal or a variable passed
   unchanged to the self-call at the same position.
8. **The answer is the counter.** At some other position `j` the recursive
   clause has a variable that it passes unchanged to the self-call and uses
   nowhere else, and the base clause has the same variable at `j` as at the
   counter position.

Why tabling cannot change the answers:
- Every answer is the counter value at the depth where the base clause
  succeeded, read at position `j`.
- The base clause gives at most one answer per depth, and the counter takes
  a different value at every depth, so no answer repeats. There is nothing
  for the table to deduplicate.
- The guard stops the recursion at the bound, so the untabled call
  terminates.
- Untabled answers come in SLD order, which is the order SWI-Prolog gives.

Stays tabled:
- the answer is not the counter (`g L H a`: untabled it would repeat `a`);
- there is no guard (`nat`);
- the bound moves with the counter;
- there are two base clauses that can give the same answer.

The one edge case is a float counter beyond 2^53, where `V + 1 = V`. There,
the untabled loop never ends, but a table would stop at the repeated variant.
Integers are unbounded, so integer counters cannot overflow.

Effect, linux-x86_64 on a noisy VM, whole process, median of 5:
`findall X (btw 1 N X) L` took 0.134 / 1.169 / 10.29 s at N = 100 / 200 / 400
when tabled. Untabled it takes 0.008 / 0.007 / 0.007 s, then 0.011 s at
N = 2000 and 0.097 s at N = 50000.

Examples that are no longer tabled: `bench_nrev K` (`bench/bench.nprolog`
shape), `loop N` countdowns, zebra's `loop N _ O`, and accumulator counters
such as `count N A R <- N > 0, A1 is A + 1, N1 is N - 1, count N1 A1 R`.

These stay tabled: `fib` and `tak` (several self-calls, or self-calls that
are not last), left recursion, mutual recursion, any loop without an
`is`-stepped counter, and counter loops whose clauses are not exclusive
(e.g. two `dup 0 a.` facts). The last case keeps its deduplicated answers
and gets the `perf-tabled-counter-loop` information diagnostic from
`infera check`, which suggests `notable` if duplicates are acceptable. The
hint is suppressed when the predicate is explicitly declared `table`.

Semantic note: a table also deduplicates answers. For a loop meeting the
criterion, each call has at most one applicable clause per step, but body
goals other than the self-call may still produce duplicate solutions. Those
are now returned as they are, exactly as with `notable`.

### Measurements (linux-x86_64, GHC 9.8.2 `-O2`, whole process, noisy VM)

| program (default tabling) | before (`perf/tabling-completion-log`) | after, JIT on | after, JIT off |
| --- | ---: | ---: | ---: |
| nrev30 x30000 | >60 s (11.7 s at x10000) | 0.37 s | 2.7 s |
| zebra x300 | 4.15 s | 2.04 s | 2.04 s |
| fib 27 (memoised) | 0.008 s | 0.008 s | 0.009 s |
| tak 24 16 8 (memoised) | 0.02 s | 0.018 s | 0.017 s |

All 23 shipped examples give byte-identical output before and after, with
the JIT on and off (46 runs). `test/autotable.py` covers the criterion:
not tabled, still tabled, explicit `table`, deduplication, the check hint,
and timing with the JIT on and off.

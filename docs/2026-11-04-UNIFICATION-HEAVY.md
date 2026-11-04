# Unification-heavy programs: where the time goes and what is left - 2026-11-04

Kind: diagnosis and ranked plan, with the first item carried out. Follows
[`2026-11-01-INFERA-PERF-RESULTS.md`](2026-11-01-INFERA-PERF-RESULTS.md),
which found Infera about 3x behind SWI-Prolog on zebra, deriv and primes,
and [`2026-11-04-NEXT-HORIZONS.md`](2026-11-04-NEXT-HORIZONS.md), the
state of the JIT after the Horizons merge.

## The workloads

Three programs now live in `bench/bench.nprolog` and `bench/bench.pl` as
cases of `bench/run.py` (`--case zebra`, `deriv`, `primes`), so the numbers
below are reproducible from the repository. The Prolog versions carry no
cuts: every system runs the same search.

| case | program | answer |
| --- | --- | --- |
| zebra | the five-houses puzzle, 300 times, `mem`/`right_of`/`next_to` over `h/5` structures | `japanese` |
| deriv | symbolic differentiation of four expressions, 30000 times; `d/3` builds nested `add`/`times`/`quo` terms | 30000 |
| primes | list sieve to 20000: `remove/3` filters with `%`, `sieve/2` recurses, `len/2` counts | 2262 |

Timings on this Mac (Apple Silicon, `-O1` library, whole process, user
time, median of 5), Infera at `c259cdb` against SWI-Prolog 10:

| case | Infera | SWI | ratio |
| --- | ---: | ---: | ---: |
| zebra | 0.83 s | 0.27 s | 3.1x |
| deriv | 0.53 s | 0.13 s | 4.1x |
| primes | 0.98 s | 0.39 s | 2.5x |

## Findings

**The JIT does not run on any of them.** `INFERA_JIT_DEBUG=1` shows every
predicate declined. `remove/3`, `range/3`, `sieve/2` and the zebra
predicates are "inferred Nondet"; `d/3` and `len/2` are "outside JIT
fragment". `INFERA_JIT=0` changes nothing measurable. The instruction
stream (`INFERA_CORE_STREAM=0` to disable) is worth 5-15%.

**GHC's collector is not the cost.** 2-5% of time in all three. The 1.3-2.8
GB allocated per run is a symptom of interpretive work, as
[`2026-10-20-PER-CALL-COSTS.md`](2026-10-20-PER-CALL-COSTS.md) already
concluded for the earlier workloads.

**Clause selection is the largest single cost.** Late cost-centre profile
(`--profiling-detail=late`), self time:

| cost centre | zebra | deriv | primes |
| --- | ---: | ---: | ---: |
| `callPlain` | 25.8% | 22.4% | 12.6% |
| `principalKeys` + `decisionKeys` + `intersectCandidates` + `candidateClauses` | 9.4% | 14.9% | 6.3% |
| `headUsesSlotExcept1` (Horizon 2 pruning) | 4.7% | - | - |
| `unify` | 12.7% | 1.6% | 2.9% |
| `streamCode` + `streamHead` + `streamOperands` | 22.3% | 10.5% | - |
| `step'` + `matchHead` + `unifyCompound` + `buildArgs` (tree interpreter) | - | 4.7% | 38.8% |
| `buildCompound` | - | 10.3% | 5.0% |
| `occursPattern` | - | 3.3% | 2.2% |
| `collect` (Core heap collector) | - | 6.6% | 11.8% |
| `backtrack` + `dispatchCandidates` + `tryClauseWithFrame` | 19.1% | 13.4% | 12.6% |

`callPlain` carries 41-50% of all allocation: the `Cont`/`CReturn` values,
the `switchGround` check and the candidate dispatch all sit in it. In deriv,
`decisionKeys` runs about seven times per call (13.2 M entries for 1.98 M
calls): the second-level index walks every decision path on every call.

**Horizon 2's runtime pruning (`pruneCandidates`) was a net loss.** It
re-walked the first two head patterns of every candidate clause on every
call. With it replaced by the identity (answers identical on all four
programs):

| case | with pruning | without | change |
| --- | ---: | ---: | ---: |
| zebra | 0.83 s | 0.65 s | -21% |
| deriv | 0.53 s | 0.44 s | -16% |
| primes | 0.98 s | 0.87 s | -11% |
| queens 9, all solutions | 0.42 s | 0.40 s | -5% |

Queens is the program the pruning was written for; the choice points it
removed cost less than the walk that removed them. The first-argument
index, the decision keys and the integer guards already make the same
decisions once per call from precomputed tables.

## What remains, in order of expected value

1. **Remove `pruneCandidates`** (done below) **and compile selection into
   one decision per predicate.** Today a call runs `principalKeys` over
   every selective argument, `decisionKeys` over every decision path,
   `keepGuards` over every candidate and intersects the results. A WAM does
   this with one `switch_on_term` per predicate: a fixed table built at load
   time, consulted once per call, and a choice point only when more than
   one clause remains. The per-call loops here should become a single table
   lookup on the first selective argument, with the deeper decisions applied
   only to the bucket that lookup returns.

2. **One exclusivity analysis, shared by determinism inference and the
   JIT.** `Infer.exclusive` does not see that `0 is I % P` and
   `X is I % P, X != 0` exclude each other, nor that `range N N` and `I < N`
   do, so `remove/3` and `range/3` are inferred nondeterministic: primes
   pushes and pops about 2.6 M choice points, and the JIT declines the
   predicates. `Jit.clausesExclusive` already reasons about integer ranges
   and comparison contradictions but only inside the JIT. Merging the two
   into one analysis removes the choice points and admits the predicates at
   once.

3. **Cheaper choice points and backtracking.** Each `pushChoice` saves
   tables, dynamic facts, the constraint mark and the watched set; each
   backtrack restores all four plus output and scopes, whether or not any
   changed. One version counter that moves when any of them changes lets a
   choice point save the counter and a backtrack skip the restore. And
   when a head fails before any body goal runs, the next clause can be tried
   by unwinding the trail alone, creating the choice point only once a body
   starts (SWI and YAP both defer it this way).

4. **Head unification and construction as compiled code, not pattern
   walks.** deriv calls `occursPattern` 6.5 M times to decide what the
   compiler could decide once: an output argument bound to a constructor of
   fresh and ground parts cannot contain itself. primes still runs on the
   tree interpreter (`matchHead`, `step'`: 27%) because `remove/3` is not
   streamable; widening the stream's admissibility retires that path.

5. **A JIT that compiles the stream rather than matching shapes.** The
   general compiler admits self-recursive tail loops over integers and
   lists with up to four arguments, no structures, no calls and no choice
   points. Compiling from the clause stream would give it everything the
   stream has, in this order: structure matching and building (deriv),
   calls to other predicates, try/retry/trust choice points (zebra,
   `remove/3`), and a native environment stack for non-tail calls. The
   October result that a WAM frame stack was slower applied to a stack
   written in Haskell; in native code the frame stack is the right design.
   This is the item that can close the remaining gap and the largest.

6. **A generational Core collector.** `collect` marks the whole live heap
   each time it runs (7-12% in deriv and primes). The trail already records
   every write into a cell older than the newest choice point, which is the
   remembered set a generational scheme needs.

## Item 1, first half: removing the pruning

`pruneCandidates`, `clauseAcceptsCall`, `clauseAcceptsWordAt`,
`clauseAcceptsInt0`, `headUsesSlotExcept1` and `allClausesRequireCons1`
are removed from `Infera.Core.Run`; `callPlain` and
`callClausesInterpreted` dispatch `candidateClauses`' result directly.
Results after the change are in the section below.

## Results

`bench/run.py --runs 5 --warmup 1`, wall-clock medians on this Mac after the
removal (the harness runs SWI and Scryer as plain `swipl`/`scryer-prolog`
processes, which is why its SWI figures are lower than the hand-timed ones
above):

| case | Infera | SWI | Scryer | Infera ÷ SWI |
| --- | ---: | ---: | ---: | ---: |
| zebra | 0.683 s | 0.171 s | 0.668 s | 4.0x |
| deriv | 0.471 s | 0.097 s | 0.349 s | 4.8x |
| primes | 1.030 s | 0.324 s | 0.613 s | 3.2x |
| queens 8, first | 0.021 s | 0.020 s | 0.060 s | 1.05x |
| nrev 30 x 3000 | 0.049 s | 0.056 s | 0.148 s | 0.88x |
| fib 25 | 0.057 s | 0.052 s | 0.083 s | 1.11x |

Hand-timed user seconds, same binary, before and after: zebra 0.83 -> 0.65,
deriv 0.53 -> 0.44, primes 0.98 -> 0.89, queens 9 all solutions 0.42 -> 0.40.
Infera is now level with Scryer on zebra and ahead of it on primes; SWI
stays 3-5x ahead on all three.

**An observation for item 3.** The harness wraps each query in `once`, and
that alone costs primes 12% (`primes 20000 K` 0.89 s; `once (primes 20000
K)` 1.00 s): one choice point under the whole run makes every call pay the
choice-point protocol it would otherwise skip. Item 3's deferred choice
points and cheaper scopes address exactly this.

Correctness: `core-engine parity` over `test/core/*.nprolog` agrees on every
query; the bench harness unit test passes with the three new cases.

## Item 2, first half: arithmetic guard prefixes in determinism inference

`Infer.guardOf` read one goal: the first, when it was a comparison between
head variables and literals. `Infer.guardsOf` now reads the clause's
leading arithmetic prefix: `is` goals and comparisons, over expressions in
head variables and literals, with a body variable defined by an earlier
`is` standing for its expression. Two clauses are exclusive when a guard of
one contradicts a guard of the other in any orientation: the same operands
with disjoint orderings, as before, or the same left operand against two
different literals whose orderings leave no position for the value
(`jointlySat`). `is` unifies its result by identity (`0 is 0.0` fails), so
an `is` guard is a term-identity constraint, and since a term identical to
a literal has that literal's value it is also recorded as a value
constraint, which lets `0 is E` contradict `X is E, X > 0`.

Effect on `remove/3`: `semidet when argument(s) 2 1 ground`, so the Core
commits after the first solution. primes 0.89 -> 0.82 s user and peak
residency 73 MB -> 15 MB: the choice point per element used to pin the heap
below it. zebra and deriv unchanged (0.65, 0.44). The choice point is still
pushed and popped per element, because selection (`pIntGuards`) evaluates
only comparisons of a head argument against a literal; evaluating the
`is`-expression guard at selection time, so that only the one matching
clause is tried, is the second half of item 1.

Deliberately not inferred: a repeated head variable against a comparison
(`range N N [N]` vs `range I N _ <- I < N`). Committing there would hide
the type error the second clause raises for equal non-numbers, which the
reference engine reports. `range/3` stays nondet, and so does anything
whose determinism depends on it (`primes/2`).

Tests: `InferenceTest` "arithmetic guard prefixes exclude clauses" (the
sieve, residue classes against three literals, and an integer result that
is not identical to `0.0`); `test/core/parity-decisions.nprolog` runs the
same predicates in unbound, non-numeric and float modes against the
reference engine.

## Item 1, second half (part): `is` guards decided at selection

`Compile.leadingIntGuard` used to read one shape: a leading comparison of
head arguments and literals, kept in `pIntGuards` and tested by
`keepGuards` before any clause is entered. It now also reads `k is E` for
an integer literal `k`, `V is E` for a head variable `V`, and `X is E`
into a fresh body variable followed by `X != k`, `X == k` or a comparison
of `X` with `k`. `E` may be any plan-operator expression over head
arguments and literals (`GuardOp`), and `guardHolds` evaluates it with the
interpreter's own `planApply` (moved to `Compile`, shared with `runPlan`),
so the guard decides exactly when the interpreter would succeed: on any
non-integer operand, overflow or division by zero it stays undecided and
the clause runs as before.

Effect: for the sieve's two cons clauses exactly one survives selection,
so no choice point is pushed per element. primes 0.82 -> 0.63 s user
(0.98 s at the start of the day, -36%); zebra and deriv unchanged. The
rest of item 1, one load-time decision table instead of the
`principalKeys`/`decisionKeys`/`keepGuards` walks, is still open.

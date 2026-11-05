# Per-call work on unification-heavy programs - 2026-11-05

Kind: diagnosis and engine changes. Follows
[`2026-11-04-UNIFICATION-HEAVY.md`](2026-11-04-UNIFICATION-HEAVY.md) and
[`2026-11-05-CHOICE-POINTS.md`](2026-11-05-CHOICE-POINTS.md). Base is `main`
at `ae5fd44` (PRs #14, #15 and #16 merged).

## Where the gap is

Infera makes the same number of calls as SWI-Prolog's inference count on
these programs (zebra: 3.87 M calls, SWI 3.85 M inferences). The gap is the
cost of each step. Microbenchmarks (`INFERA_JIT=0`, user time less an empty
run, on a loaded machine, so roughly):

| operation | Infera | SWI-Prolog | ratio |
| --- | ---: | ---: | ---: |
| call with no arguments | 49 ns | 5.5 ns | 8.9x |
| counter step (call, compare, `is`) | 120 ns | 40 ns | 3.0x |
| build `s/1` in a head, write mode | 225 ns | 39 ns | 5.8x |
| `mem` element: choice, head fails, retry | 110 ns | 25 ns | 4.4x |
| build `h/5`, unify with `h/5` | 533 ns | 83 ns | 6.5x |

Profiles of zebra, deriv and primes put the time in five places: the call
protocol (selection, the commit check, the return record), a choice point
on most calls, structure building in write mode, primes' `remove/3` running
on the tree interpreter, and generic unification. Upper bounds measured with
throwaway switches (never committed): no clause selection at all saves 3%
on zebra and costs deriv and primes far more; no occurs check saves 8% on
deriv and nothing on zebra. No single cost is large; the work is spread
across the protocol.

## Measurement

The host carried a load average of 5-14 throughout, which moved wall and
user times by 10% or more between identical runs. Comparisons below use
**instructions retired** (`/usr/bin/time -l`, minimum of three), which load
does not change. Whole-process wall times from `bench/run.py` are given at
the end for orientation.

## Changes

1. **Shallow backtracking** (`Run.shallowCandidates`). A call with several
   candidates saved its arguments and pushed a full choice point before
   trying the first clause; a head that failed at once (zebra's `mem`, most
   of the time) then paid a full backtrack, restoring every piece of
   branch-local state, and an argument reload. Now, while no constraint
   watches bindings, each candidate's head is matched with the choice
   boundary raised to the entry heap top (so every binding is trailed) but
   no choice point; a failed head is undone by unwinding the trail and
   resetting the heap. The choice point is pushed only when a head matches
   while candidates remain, with the marks from before that head
   (`pushChoiceMarked`), and the last candidate runs with no choice point at
   all. Matching a head touches no tables, facts, output, scopes or
   constraints, so the heap and trail marks are all it changes.

2. **Structures built in place** (`Run.buildStructure`, `fillArguments`).
   One top-level loop now builds every constructor, without the per-call
   closure the generic arity path allocated. A fresh activation variable
   met in write mode becomes the structure's own argument cell, with the
   slot referring to it, as WAM's `unify_variable` does; before, the slot was
   written, then promoted to a separately allocated cell and bound to it.
   The collector marks and compacts cells individually, so a reference into
   a structure is an ordinary reference.

3. **Selection does only what can narrow** (`Compile`):
   - `pIndexed` is false when a predicate has no selective key, decision or
     guard, so `candidateClauses` returns every clause at once;
   - principal keys visit only selective positions (`pPrincipal`);
   - decisions are grouped by argument (`pDecisionGroups`): an argument that
     is not a structure skips all its nested paths with one test. deriv's
     `d/3` had six such paths per call into its always-unbound output;
   - an index records the key that keeps every clause (`aiAll`, usually the
     cons of a list predicate), and meeting it skips the table lookup.

4. **No groundness test under an existing commit** (`callPlain`). When the
   continuation already commits at an older height, a call keeps it whether
   or not its own switch arguments are ground, so the test is skipped.
   primes' recursion ran it on every element.

5. **Allocation in the stream and unifier.** Stream structure operands walk
   cell ranges instead of building `[a+1 .. a+n]` lists, and structures of
   other than two arguments are built from the operand stack without a
   list (`copyPushed`). `unify`'s variable-to-structure bind and argument
   loop, and the occurs walk's argument loop, are top-level functions with
   strict arguments, so GHC no longer boxes the address on each bind.

6. **`planApply` strict and inlined.** Moving it to `Compile` on 2026-11-04
   (to share it with selection guards) stopped GHC inlining it into `Run`,
   and without bangs every `is` and comparison boxed both operands and the
   result to call it.

7. **Write mode on the clause stream** (`writeAndBind`, `writeOperands`,
   `writeListFirst`; added after the first review). A head structure met by
   an unbound argument used to leave the stream: `unifyPattern` built it by
   walking the `Pattern` tree, then `occursPattern` walked the tree again.
   Now the structure is built from the same operand instructions read mode
   runs (`UF`, `UV`, `UC`, `US`, `USF`), WAM-style, and the occurs check
   visits only the structure's repeated variables, listed per structure at
   load time in its side entry (`SRefOccurs`, replacing `SRefPattern`). A
   first occurrence is a fresh variable and a constant holds none, so a
   structure of only those binds unconditionally. The occurs check is the
   same check as before, on fewer places: a repeated variable whose value
   contains the target still fails the binding (`self X (f X)` with `X`
   aliased to the output fails, as in the reference engine). The tree
   interpreter's write mode is unchanged.

## What did not help

- **Arithmetic in the clause stream.** An `opGoal` instruction ran `is` and
  comparisons on the stream with the tree's fast path and a one-goal escape,
  so `remove/3` and `fib/2` would stream. primes improved 2%; zebra, deriv
  and queens got 3-7% slower, consistently across reruns. This matches the
  2026-10-30 finding that the stream's dispatch is not cheaper than
  `step'`'s for arithmetic. Not kept.
- **Skipping branch-state save and restore** was measured by
  [`2026-11-05-CHOICE-POINTS.md`](2026-11-05-CHOICE-POINTS.md) at no more
  than 3%; shallow backtracking avoids most of those saves instead.

## Results

Instructions retired, millions, `main` (`ae5fd44`) against this change:

| case | main | after | change |
| --- | ---: | ---: | ---: |
| zebra x300 | 16098 | 13508 | -16% |
| deriv x30000 | 12255 | 10941 | -11% |
| primes 20000 | 16191 | 14861 | -8% |
| queens 9, all | 10607 | 10072 | -5% |
| nrev 30 x 30000 | 5388 | 5222 | -3% |

Microbenchmarks, same measure (`INFERA_JIT=0`):

| operation | main | after | change |
| --- | ---: | ---: | ---: |
| calls, no arguments | 3729 | 3591 | -4% |
| counter steps | 5182 | 4879 | -6% |
| build `s/1` in head | 11165 | 9792 | -12% |
| build `s/1` via a call | 11220 | 10297 | -8% |
| build + unify `h/5` | 6538 | 5512 | -16% |
| `mem` elements | 6359 | 5984 | -6% |

`bench/run.py`, whole process, median of 5, on the loaded host:

| case | main | after | SWI-Prolog | Scryer |
| --- | ---: | ---: | ---: | ---: |
| zebra | 0.917 s | 0.756 s | 0.21-0.23 s | 0.80 s |
| deriv | 0.651 s | 0.600 s | 0.13 s | 0.44-0.53 s |
| primes | 0.834 s | 0.800 s | 0.41-0.43 s | 0.79-0.80 s |

zebra is now ahead of Scryer; all three remain 2-4.5x behind SWI-Prolog.

### Write mode on the stream

Instructions retired, millions, before and after change 7:

| case | before | after | change |
| --- | ---: | ---: | ---: |
| deriv x30000 | 10928 | 9921 | -9% |
| queens 9, all | 10053 | 8966 | -11% |
| zebra x300 | 13496 | 13454 | 0% |
| primes 20000 | 14842 | 14844 | 0% |
| build + unify `h/5` (micro) | 5517 | 5102 | -8% |
| build `s/1` via a call (micro) | 10264 | 9776 | -5% |

queens gains because `perm`/`sel` build their `[H | R]` outputs on every
call. primes is unchanged: `remove/3` starts with `is`, so its clauses run
on the tree interpreter, whose write mode this does not touch. A single
reservation for a nested template (one `reserveCells` instead of one per
level) was not done; a reservation is a bump and a capacity test.

Totals against `main` (`ae5fd44`), all changes: zebra -16%, deriv -19%,
primes -8%, queens -15%, nrev -4%.

## Correctness

- `test/core/parity-shallow.nprolog` (new, in the `core-engine` group): heads
  that bind older variables and then fail, choice points created after a
  matching head, cuts in clauses reached after shallow failures, repeated
  head variables over structures, variables escaping into built structures
  across tail calls, membership under active constraints (the non-shallow
  path), and nested nondeterminism under `findall` and `not`.
- `test/core/parity-write.nprolog` (new, in the `core-engine` group): output
  structures of fresh variables and constants, repeated variables that make
  the binding cyclic (must fail) or not, nested structures and lists, an
  unbound local escaping into an output, write-mode lists built by tail
  recursion, symbolic differentiation, and backtracking over write-mode
  bindings.
- `core-engine parity` over `test/core/*.nprolog` agrees normally, with
  collection at every call (`--gc-limit 1`), and with
  `INFERA_CORE_STREAM=0`.
- Full `cabal test all`, and every CI script: `cli`, `jit_depth`,
  `assert_scaling`, `autotable`, `unify_scaling`, `index_semantics`,
  `det_guards`, `ite_parity`, `example_programs --all-modes`, the bench
  harness tests.

## What remains

The remaining gap is spread across an interpreter written in Haskell: a
bare call is still about 7x SWI's, through the return continuation, frame
setup, the depth check and dispatch, with no single step above a few
percent. Changes inside this design now return a few percent each. The
lever that remains is the one ranked fifth in
[`2026-11-04-UNIFICATION-HEAVY.md`](2026-11-04-UNIFICATION-HEAVY.md):
compiling clauses to native code from the stream, with structures, calls
and choice points, so that per-call work stops being interpretive.

# Native list-search kernels - 2026-11-05

Kind: engine change and measurement. Follows
[`2026-11-05-PER-CALL-WORK.md`](2026-11-05-PER-CALL-WORK.md), whose "What
remains" names native compilation as the lever left, and the first of the
two increments in
[`2026-11-05-UNIFICATION-REFACTOR.md`](2026-11-05-UNIFICATION-REFACTOR.md)
§6. Base is `perf/per-call-costs` at `205405d`.

## Why `mem`

zebra spends most of its calls in `mem/2` and `right_of/3`, scanning a
five-element list of `h/5` houses where most elements fail in the head. Each
element was a full interpreted call: selection, a shallow head attempt, a
trail unwind, the recursive call's frame and continuation. Until now the JIT
compiled only deterministic predicates, and these are nondeterministic.

## The shape

A list search is a predicate of exactly two clauses, the base clause first:

```
mem X [X | _].                    right_of X Y [Y, X | _].
mem X [_ | T] <- mem X T.         right_of X Y [_ | T] <- right_of X Y T.
```

The base clause's list argument is a prefix of one or more elements, each
another argument of the clause or `_`, ending in `_`; its other arguments are
distinct variables. The step clause drops the head and recurses on the tail
with the other arguments unchanged. `Jit.scanShape` recognises it at load
time (no declared contract, not tabled, not dynamic, arity at most 8); the
list argument may be at any position, and an element may repeat an argument
(`twin X [X, X | _]`) or skip (`second X [_, X | _]`).

## The kernel

`Jit.compileScanKernel` emits native code (AArch64 and x86-64, through the
existing IR) that walks the list from the call's list argument. At each
cons it records the trail top and unifies each prefix element with its
argument:

- constants, unbound variables, and structures whose arguments are
  constants, variables or structures marked ground are unified natively;
  two variables bind the younger to the older, as `Store.unify` does;
- binding a variable to a structure not marked ground runs the occurs check
  over that structure's arguments (the variable among them fails; a nested
  structure not marked ground bails);
- two structures nested inside an element, two boxed constants (floats,
  strings, big integers) and an unbound list tail bail.

A failed attempt is undone from the trail by the kernel itself, and the
walk moves to the tail. The kernel returns:

| code | meaning | list argument's slot |
| --- | --- | --- |
| success | a head matched; its bindings stay | the matched cons |
| failure | the list ended with no match | - |
| bailout | the interpreter must continue | the position reached |
| declined | constraints active, or the list argument unbound | unchanged |

Two new IR instructions support it: `JAnd` (functor keys and arities) and
`JShr` (trail entries to addresses), in both assemblers.

## Choice points without a new alternative

On success with more list after the matched cons (a cons or an unbound
tail), `Run.scanRun` saves the arguments with the matched cons in the list
slot and pushes an ordinary `AltClauses` choice point whose next candidate
is the step clause, with the marks from before the kernel ran. Backtracking
undoes the match, reloads the arguments, and runs the step clause on that
cons, whose recursive call reaches the kernel again at the next position.
The step clause is exactly what the interpreter would have run, so the
search continues in the same order with the same bindings, and the collector
and every other piece of the choice stack see nothing new. A match at the
last cons pushes no choice point.

A bailout hands the call at the position reached to the ordinary clause
dispatch: by the step clause, a call at a later position is exactly the
remaining search.

The kernel's bindings are trailed against the entry heap top (every older
cell), so the entry marks undo them. `JBindRef` writes the cell before it
checks the trail's capacity, and bails with the binding in place when the
trail is full; the scan kernel checks capacity before every bind instead,
so a full trail bails with nothing to undo. Before that check zebra failed
at its 130th repetition, the first time the trail filled between
collections.

## Results

Instructions retired, millions (`/usr/bin/time -l`, minimum of three),
`205405d` against this change:

| case | before | after | change |
| --- | ---: | ---: | ---: |
| zebra x300 | 13459 | 4116 | -69% |
| deriv x30000 | 9925 | 9926 | 0% |
| primes 20000 | 14851 | 14854 | 0% |
| queens 9, all | 8980 | 8987 | 0% |
| nrev 30 x 30000 | 5197 | 5199 | 0% |

Microbenchmark: `not (mem 0 L)` over a 1000-element list, 3000 times (3 M
elements), less the cost of building the list: 5832 M instructions before,
152 M after, about 1940 and 51 instructions per element (38x).

`bench/run.py`, whole process, median of 5, load average about 6:

| case | before | after | SWI-Prolog | Scryer |
| --- | ---: | ---: | ---: | ---: |
| zebra | 0.600 s | 0.217 s | 0.170 s | 0.648 s |

zebra goes from 3.5x SWI-Prolog to 1.27x.

The other cases do not use the kernel and are unchanged, after one fix:
with the scan driver as its second caller, GHC stopped inlining
`pushChoiceMarked` into `shallowCandidates` and called it out of line, which
cost deriv and queens about 1% (and 58 MB more GHC allocation on deriv). It
is now `INLINE`. The driver itself (`scanRun`, `scanCommit`) sits outside
the interpreter's recursive group and returns an outcome that the two call
sites dispatch on.

## Correctness

- `test/core/parity-scan.nprolog` (new, in the `core-engine` group, 60
  queries): matches at every position, constants, variable-variable
  bindings in both directions, unbound and improper tails, nested
  structures, lists as elements, floats, strings and big integers, the
  occurs check at the top level and inside elements, constraints (the
  kernel declines), two-element prefixes with repeats and skips, the list
  argument first, predicates that are not list searches (step clause first,
  a third clause), cuts after a search, `findall` and `not` over searches,
  the zebra pattern, and a 10000-iteration loop that fills the trail.
- `core-engine parity` over `test/core/*.nprolog` agrees normally, with
  collection at every call (`--gc-limit 1`), with `INFERA_JIT=0` and with
  `INFERA_CORE_STREAM=0`.
- Full `cabal test all`, and every CI script: `cli`, `jit_depth`,
  `assert_scaling`, `autotable`, `det_guards`, `ite_parity`,
  `index_semantics`, `unify_scaling`, `example_programs --all-modes`, the
  bench harness tests.
- The x86-64 encodings of `JAnd` and `JShr` are checked only by Linux CI,
  which runs the kernel natively; this host is AArch64.

## Not done

- **The same bug in the deterministic kernels.** Their `JBindRef` calls
  share the write-before-check order: a kernel that bails on a full trail
  leaves its last binding untrailed, and the driver's unwind does not undo
  it. Fixing `JBindRef` itself (check, push, then write) in both assemblers
  would close it for every kernel.
- **`sel/3`, `perm/2` and other list predicates that build.** They need the
  kernel to allocate and are the second increment in §6 with general
  single-functor tail recursion.

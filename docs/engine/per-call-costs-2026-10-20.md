# Where the Core's time per call goes - 2026-10-20

A reference diagnosis of why the Core is several times slower than
SWI-Prolog and somewhat slower than Scryer per logical inference. It records
what is a cost of Infera's semantics, what is a cost of the implementation,
what has been tried and measured, and what remains. Branch
`core-unboxed-control` at `59a7119`; figures from `bench/core-major`
(loaded, checked queries, `-O2`, macOS arm64).

## The gap

| Workload | Core ms | ÷ SWI | ÷ Scryer |
| --- | ---: | ---: | ---: |
| Reverse, 100 x 30 | 8.30 | ~9.3x | ~2.5x |
| Loop, 90,000 | 8.71 | ~4.7x | ~1.0x |
| Fibonacci 25 | 37.76 | ~3.5x | ~1.3x |
| First 8-queens | 8.31 | ~3.4x | ~1.5x |

SWI and Scryer were not re-measured; their times come from the
[external comparison](../performance/reports/engine-external-2026-10-18.md)
on the same machine and workloads. Day-to-day drift was about 8%, so the
ratios are approximate. Reverse is about 170 ns per inference before these
changes and ~145 ns after; SWI is about 17 ns.

SWI is not specialised for these benchmarks. It is a WAM-style virtual
machine in C: clauses compiled once at load time, just-in-time first- and
multi-argument indexing, dedicated selection for `[]`/`[_|_]` predicate
pairs and one-clause predicates, last-call optimisation, and no general
allocation per call. Scryer is the fairer yardstick for an engine of this
design.

## Costs of Infera's semantics

These are work SWI does not do, because Infera promises more:

* **Occurs check on every variable-to-structure binding.** SWI's default is
  off. The ground marker on structure cells and first-occurrence head slots
  keep it cheap on these benchmarks; on partial data structures it costs
  time proportional to the term on each binding.
* **Branch-local state in every choice point.** Tables, dynamic facts, the
  constraint-store mark and watched cells are restored on backtracking;
  `assert` is undone, unlike SWI's. Since `1f075ac` these are pointer writes
  into a choice stack, not a boxed record per choice.
* **Contracts and inferred determinism.** Declared predicates select a
  signature, push guards and check outputs. Undeclared predicates may still
  commit after their first solution when inferred switch arguments are
  ground, which needs a groundness check (memoised per structure; about 4%
  of reverse).
* **Error and issue scopes.** `if-then-else`, negation and `findall` buffer
  or count errors in scopes, allocating IORefs and a full choice point each
  time; SWI's if-then-else is a choice mark and a cut.
* **A resolution-depth cap** of 100,000 (`maxResolutionDepth`). Non-tail
  recursion deeper than that ends as "exhausted"; SWI is bounded only by
  its stack limit. This limits generality rather than costing speed.

Variable identity used to belong here: the Core reproduced the reference
engine's fresh variable ids so answers matched exactly. Since `1f075ac`
answers are compared up to renaming, and that bookkeeping is gone.

## Costs of the implementation

Before `1f075ac`, ticky counted about 300 bytes of GHC allocation per call,
spread across the call path with no single culprit. GHC's own collector was
only about 3% of time, so the allocation was a symptom of interpretive work
rather than a cost in itself. The structural causes:

1. **Tree-walking interpretation.** Each goal walks `[Goal]`, `[Pattern]`
   and `Expr` values through generic `step'`, `buildArg` and `unifyPattern`
   code with many cases. A WAM runs short specialised instruction sequences.
2. **One generic call protocol.** Every call checked the collection limit,
   selected a signature, decided commits, read guard and choice heights and
   counted depth, whether or not the predicate had a contract.
3. **Boxed control state.** Choice points were ten-field records in a boxed
   array; choice and guard heights were `IORef Int`, which allocate on every
   write; a push took the `length` of the scope list.
4. **List-building clause selection.** `candidateClauses` returned `[Int]`
   from IntMap lookups, intersections and a `filterM` over guards: 40-96
   bytes per call.
5. **Generic arithmetic.** `evalFast` walked an expression tree per `is` and
   comparison, passing every value through a store register.
6. **Per-query compilation.** Plans are built when a query starts. Measured
   at about 0.09 ms per query: small here, relevant for very short queries.

## What was done, and what it bought

Against `main` (`1a97539`), median of seven runs:

| Workload | `main` ms | now ms | CPU | GHC allocation |
| --- | ---: | ---: | ---: | ---: |
| Reverse | 9.82 | 8.30 | -15% | -50% |
| Loop | 10.39 | 8.71 | -16% | -64% |
| Fibonacci | 48.49 | 37.76 | -22% | -60% |
| Queens | 9.36 | 8.31 | -11% | -45% |

* `1f075ac` ([report](control-stacks-2026-10-19.md)): answers up to
  renaming (removing fresh-id bookkeeping and the marker scan in every
  variable-variable unification), a plain call path for predicates without
  contracts (cause 2), and an unboxed choice stack with unboxed counters
  (cause 3). Most of the CPU gain on reverse and queens.
* `e47bc65` ([report](clause-selection-2026-10-19.md)): precomputed,
  allocation-free clause selection (cause 4). Allocation fell 24-43%; CPU
  was flat to +3%.
* `59a7119` ([report](arith-plans-2026-10-19.md)): compiled plans for flat
  `is` and comparison shapes (cause 5). Fibonacci -10-12%, loop -5-9%.

## What did not work

* **Continuation frames on an unboxed stack** (WAM environments). Built,
  correct, and 5-14% slower than keeping continuations as GHC values, at
  equal allocation. A frame access is an IORef, a record and an array load,
  and entering a frame maintains the frame top; allocating a short-lived
  six-word continuation in GHC's nursery is already a pointer bump. The
  WAM's reason for stack frames, avoiding general allocation, does not
  apply in GHC.
* **Strict driver arguments.** Cut allocation 5-13%, no CPU gain.

## Lessons for this code base

* **Allocation is not CPU in GHC.** Two changes halved allocation without
  moving CPU. Measure time; use ticky allocation counts to find *where*
  work happens, not to predict a speed-up.
* **Shared `where` bindings in hot functions allocate on every call.** A
  binding used by several `step'` branches became a closure allocated on
  every goal, used or not. Local functions closing over the machine in
  `candidateClauses` did the same. Keep them in the branch that needs them,
  or make them top-level.
* **Inspect what GHC produced.** `-ddump-stg-final -dsuppress-all`
  identifies such closures and boxed arguments directly; a late
  cost-centre profile (`--enable-profiling --profiling-detail=late`) gives
  time shares. Exclude the Reference oracle's cost centres, which the
  benchmark runner also executes.

## What remains

Late profile of the Core share before the arithmetic and selection
changes: reverse spends `unifyCompound` 20%, `step'` 16%, `buildCompound`
13%, `matchHead` 12%, `buildArgs` 12%; Fibonacci spends `step'` 26%,
`evalFast` 14%, `matchHead` 10%, `candidateClauses` 9%. The last two items
are now addressed. In order of expected value:

1. **Specialised head matching and construction** for reverse and append:
   get-list/put-list style plans for list heads, and occurs checks skipped
   where the compiler proves the target fresh or the term ground. Reverse,
   the furthest behind, spends most of its time here.
2. **Closure compilation of clause bodies**: compile each body once into
   chained Haskell functions, removing per-goal dispatch through `step'`.
   The largest change; simpler after item 1.
3. **Cheaper control constructs**: if-then-else and negation without IORef
   allocation and full choice points when no error can occur inside.
4. **Load-time plan caching** instead of per-query compilation.
5. **Lifting the resolution-depth cap** to a growable, memory-bounded limit.

Re-profile after each step; the shares above will shift.

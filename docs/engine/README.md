# Current engine

Normal CLI and REPL queries use `Infera.Core` automatically through
[`Infera.Engine.solveQuery`](../../src/Infera/Engine.hs). The implementation
is Haskell, with mutable execution inside an immutable lazy answer API.

## Query execution

1. Loading resolves imports, parses source, expands DCGs, infers predicate
   properties and performs the existing checks.
2. When a query starts, the [compiler](../../src/Infera/Core/Compile.hs)
   builds head patterns, body plans, predicate references and indexes for
   that query's program. Plans are currently built per query.
3. The [driver](../../src/Infera/Core/Run.hs) executes those plans with
   argument registers, explicit continuations and choice points. Eligible
   tail calls reuse continuations.
4. The [store](../../src/Infera/Core/Store.hs) represents values as tagged
   words. Variables are references, compounds have contiguous cells, and
   bignums, floats and strings use a boxed table. Bindings are trailed when
   backtracking may need to undo them.
5. Backtracking restores heap/trail marks and branch-local state. A
   mark-compact collector runs at call boundaries and relocates live roots,
   continuations, choice points and trail entries.
6. Answers are exported as immutable bindings, constraints and output
   through the existing lazy `Search` interface.

Indexing is enabled by default. Automatic tabling applies to eligible pure
recursive predicates that are not classified as structural recursion;
`table`, `notable`, `index` and `noindex` declarations override the defaults.
Tabling, dynamic facts, control constructs and minimization run within the
core. Constraint posting and labeling use a sparse mutable propagation kernel
with native linear reduction, domain cells and work queues. Core choices save
undo marks; immutable stores are materialized at answer and compatibility
boundaries. Complex single-constraint reducers still use the persistent kernel.
Watched binding deltas synchronize propagation with the heap. Some other leaf
builtins still use Reference adapters.

Declared sorts, modes and determinism are enforced where needed. Compiler
proofs remove checks already established by callers or clause bodies;
inferred signatures do not authorize removing safety checks. The
[contracts report](contracts-performance-2026-10-17.md) describes the proof
rules and their measured effect.

## Compatibility boundaries

Tracing and library `solveGoal`/`solveGoals` entry points still use
`Infera.Machine.Control`. If a core run reaches an unsupported construct,
the [facade](../../src/Infera/Core.hs) restarts the query on that machine and
skips already-delivered search items; it does not transfer the live heap.
`Infera.Engine.Reference` remains the correctness oracle used by tests.

The earlier machine and its opt-in bytecode backend remain available for
those paths and comparisons. They are not the normal CLI/REPL query engine.

## Design and evidence

* [Diagnosis and core migration](engine-diagnosis-2026-10-17.md)
* [Contract proofs and performance](contracts-performance-2026-10-17.md)
* [Mutable CLP propagation](mutable-clp-2026-10-18.md)
* [Four major Core designs](major-design-2026-10-18.md)
* [Latest performance overview](../performance/README.md)
* [Reverse construction, matching and collection](../performance/reports/engine-reverse-2026-10-17.md)
* [Earlier machine/bytecode roadmap](roadmap.md)
* [Legacy machine validation detail](legacy-machine-validation.md)

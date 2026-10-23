# Four further Core performance designs

Date: 2026-10-18

This document records the first four-design slice. The subsequent
[mutable CLP follow-up](2026-10-18-MUTABLE-CLP.md) replaces the persistent
constraint state and synchronization path described below.

This change implements a bounded first slice of four structural improvements:
native constraint search, compiled clause decisions, precise activation
liveness, and incremental tabling. Each targets work that the tagged-cell Core
still repeats or retains unnecessarily. They build on the existing public Core
and preserve its reference-compatible search boundary.

This document describes the implementation and its validation contract. It does
not establish that the checks have passed or that any workload is faster. The
associated measurements, validation results, source identities and remaining
limitations belong in the [performance report](2026-10-18-ENGINE-MAJOR.md).

| Design | Implemented slice | Deliberate boundary |
| --- | --- | --- |
| Native constraints | Core owns constraint posting dispatch, labeling choices, rollback and branch-and-bound search. | Propagation still uses the persistent `CLP.Store`, with heap/store synchronization. |
| Compiled decisions | Intersect argument indexes, inspect bounded nested constructor paths, and reject proven-false leading integer guards. | No general guard evaluation or new commitment proof; additional refinement is disabled when CLP is active. |
| Precise liveness | Retain cells used by suspended plans instead of entire activation blocks. | Collection still preserves query roots, live structures, constraint watches, saved choices and copied scope results. |
| Incremental tabling | Proven positive, same-variant linear recursion consumes only the previous round's new answers. | General fixpoint iteration remains for other recursion shapes and observable issues. |

## Native constraint posting and search

[`Core.Constraint`](../src/Infera/Core/Constraint.hs) provides the operations
that [`Core.Run`](../src/Infera/Core/Run.hs) needs without constructing a
reference `Search` or a `SolverState` for each constraint-search node. Exact
builtin arities for integer relations, domains, disequality, all-different and
reification enter this path. Other leaf builtins keep the existing compatibility
dispatch.

Ordinary `label` and `labeling` select variables by stable smallest-domain-first
order and enumerate ascending values. `AltLabel` choices save the same heap,
trail, fresh-variable, output, table, dynamic-fact, constraint-store and watched
cell state as other Core alternatives. Backtracking restores those components
together. The permissive ordinary-label list-tail policy and its handling of
aliases intentionally follow Reference behavior.

`labeling [min Cost] Variables` uses a separate strict proper-integer-list
contract. Core keeps an incumbent and adds a strict upper bound before exploring
the next branch. It recomputes the remaining domain after incumbent changes,
retains the first optimum on ties, and uses a minimize sentinel to buffer
issues and restore only the winner. An error or incomplete search prevents a
winning answer. Errors while binding a value stop that variable's optimization
exploration, matching Reference; ordinary labeling retains its independent
alternative behavior.

Winner restoration also records the candidate's fresh-variable bound and uses
one shared copy namespace across every restored root. Shared variables remain
shared, distinct escaped locals remain distinct, and later allocations cannot
reuse their logical IDs. The logical-to-physical cell map and watched-cell set
are rebuilt from those copies and surviving older cells, rather than retaining
addresses from the abandoned candidate branch. Reconstruction temporarily
suppresses reconciliation against the old entry store before installing the
already-propagated winning store. This repair applies to the shared minimize
sentinel used by ordinary `minimize` and native minimum labeling.

This is native search over the existing propagator, rather than a mutable
constraint-engine rewrite. Posting and propagation still return persistent
`CLP.Store` values. `installStore` still compares substitutions, imports new
bindings, and refreshes heap watches. Heap bindings still reconcile with the
constraint store at goal boundaries. Removing those synchronization costs and
replacing persistent propagation state with a trailed mutable representation
remain separate design work.

## Compiled clause and guard decisions

[`Core.Compile`](../src/Infera/Core/Compile.hs) builds decisions once per
compiled predicate. Principal indexes now intersect all useful bound argument
keys while retaining ascending source-clause order. Open heads remain candidates.

Additional decisions inspect at most three nested constructor edges, with at
most 32 paths per predicate. Paths can discriminate functors and scalar keys,
including boxed integers and strings. An unbound ancestor, missing child or
unusable scalar key leaves the clause available for ordinary matching. NaN is
not used as an ordered-map discriminator.

A leading comparison can also reject a clause when both operands are proven
immediate integers obtained directly from call arguments or integer constants.
This does not evaluate an arithmetic expression or move arbitrary body goals
ahead of head matching. Unknown, boxed, noninteger and unbound operands retain
the ordinary execution path and its errors.

Nested and guard refinement are disabled while a constraint store is active.
A head binding could otherwise wake a constraint before a later mismatch or
failed guard. Skipping that clause early could hide an observable error. The
established principal-key selection remains available under this conservative
gate. `noindex` bypasses all index decisions.

These decisions can remove failed matching work and the alternatives it would
have created. They do not introduce a new general proof of clause exclusivity
or determinism. Existing contract and inferred-commit rules still decide when
successful execution may discard alternatives.

## Precise activation liveness

[`Core.Liveness`](../src/Infera/Core/Liveness.hs) enumerates the heap operands
of suspended goals, arithmetic expressions and scope continuations. Collection
can retain those operands without retaining every variable in the original
activation block. Surviving slot operands are rewritten into relocated cell
references, so subsequent bindings and trail unwinds remain visible through the
same logical variable. Shared immutable predicate plans are not rewritten.

[`Core.Store`](../src/Infera/Core/Store.hs) keeps sparse logical identities
for cells detached from their activation markers by collection. Fresh
activations continue to use compact block markers. This separates a variable's
reference-visible identity from its physical address and from whether its
former sibling cells are still alive. Heap rollback removes sparse identities
above the restored boundary before those addresses can be reused.

Syntax liveness is only one source of roots. Core also retains query cells,
argument registers, explicit return-check operands, table-call arguments,
findall copies, minimize winners, current and saved watched constraint cells,
and pending heap-to-constraint reconciliation cells. Choice marks and trail
entries are compacted consistently with relocation. A live compound still
retains its reachable children; the improvement reclaims dead locals and the
graphs reachable only from those locals.

Collection counters expose the number of collections, live cells at the last
collection and cumulative reclaimed cells. They allow an acceptance check to
assert that a deliberately dead graph was actually collected, independently
of answer parity or a timing observation.

## Incremental table rounds

[`Core.Delta`](../src/Infera/Core/Delta.hs) ports the narrow semantic proof
already used by Reference. A qualifying recursive clause starts with exactly
one self-call of the current variant. Its suffix and all base-clause bodies
must be acyclic positive goals with no declared contracts, effects, dynamic
predicates or CLP operations. The tabled call itself must not be constrained
or subject to an inferred commitment. Source-clause order is retained when
mapping the proof to compiled clause ordinals.

The first round runs normally. Later qualifying rounds run only the recursive
clauses and expose only the preceding round's fresh answers through the
incomplete table. The accumulated answer set still deduplicates results, and
the final answer list appends fresh batches in discovery order. Open answers
and variable aliases remain canonicalized and are instantiated afresh when
consumed.

The proof is deliberately narrower than arbitrary semi-naive evaluation.
Mutual recursion, nonlinear recursion, a different self-call variant, control
constructs and uncertain reachable goals use the full fixpoint evaluator. A
buffered error, resolution exhaustion or foreign incomplete dependency during
a delta round restarts full iteration from the entry table map, discarding
speculative answer batches and issues. The sentinel has already restored heap,
trail, output, fresh-variable and constraint state before that restart.
Answers that carry constraints retain the existing plain-evaluation fallback.
The existing iteration limit and truncation indication remain in force.

This slice does not introduce dependency-driven SCC scheduling, incremental
updates after fact mutation, or general delta handling for multiple recursive
body calls.

## Validation contract

The new tests are intended to detect semantic regressions and prove that the
selected implementation path was exercised. Their existence is not a passing
result; executed results are recorded in the performance report.

- [`CoreConstraintTest`](../test/CoreConstraintTest.hs) compares direct Core
  streams with Reference, including ordered answers, residual constraints,
  output, fresh IDs, errors and exhaustion. Generated finite grids have an
  independent Cartesian answer oracle; generated optimization cases have an
  independent cost oracle. Selected tests compare every persistent store field.
  Controls, alias lists, failed branches, nonlinear errors and winner rollback
  exercise the boundary behavior.
- [`CoreDecisionTest`](../test/CoreDecisionTest.hs) compares indexed and
  unindexed execution and checks candidate ordinals directly. Generated guards
  and nested patterns cover both eliminated and retained clauses, including
  open patterns, scalar values and the active-CLP gate. Direct Core draining
  rejects a runtime abandonment.
- [`CoreLivenessTest`](../test/CoreLivenessTest.hs) uses tiny collection
  thresholds, generated partially live activations, retained and interleaved
  answer streams, and sparse-ID rollback checks. A dead-graph case asserts
  collection and reclamation through counters, so parity alone cannot mask
  continued whole-activation retention.
- [`CoreDeltaTest`](../test/CoreDeltaTest.hs) compares delta and explicitly
  disabled delta execution against the full Reference fixpoint. A leading
  inert `true` disables the proof while preserving logical clause behavior.
  Generated graph closures and multiple recursive rules have a separate
  reachability oracle. Fixed checks cover proof exclusions, open answers,
  aliases, collection, errors, output, cuts and iteration exhaustion. A direct
  Core acceptance query rejects fallback to the legacy machine.

The checked-in parity fixtures also combine these mechanisms with surrounding
language features. Tests using the public facade alone are insufficient:
facade compatibility replay could conceal a Core abandonment. Forced
collection, direct draining and direct proof/candidate checks address different
failure modes and are kept distinct.

Performance acceptance compares the same answer-checked workload before and
after this change, using identified builds and source snapshots. Breadboard
and Minesweeper exercise constraint search; nested dispatch and failed guards
exercise decisions; a dead-local workload exercises retention; graph closure
exercises table rounds. CLI startup and loaded execution must be labeled
separately. A gain on a targeted fixture does not establish a general speedup
or proximity to SWI-Prolog or Scryer.

Pure selection stops refining once only one clause remains; ordinary head and
body checks then decide it. Constrained calls retain the complete principal
index intersection. Nested metadata excludes variable-only paths and is not
built for single-clause predicates. These bounds avoid charging routine calls
for decisions that cannot remove another alternative.

## High-value work after this slice

1. Profile constraint synchronization and propagation separately, then design
   trailed mutable domains and a mutation-aware scheduler if those costs still
   dominate. Preserve native search and its parity oracles while changing the
   kernel beneath it.
2. Extend clause decisions using measured selectivity and explicit proofs of
   harmless skipped bindings. A more precise CLP gate and proven exclusive
   head/guard combinations could remove additional alternatives without hiding
   errors. General guard reordering remains outside the current proof.
3. Use liveness information before collection for slot reuse and earlier
   retirement. Measure the cost of rewriting suspended plans and choose
   compile-time lifetime annotations or compact captured environments where
   they improve real workloads.
4. Expand delta eligibility one recursion shape at a time, retaining the full
   evaluator as an ordered oracle. Dependency-driven scheduling for mutually
   recursive tables is a separate project with explicit ordering, incomplete
   dependency and resource-limit contracts.

The next choice should follow the measured bottleneck and retained-memory
evidence. None of these bounded implementations establishes a qualitative
performance ceiling for the language.

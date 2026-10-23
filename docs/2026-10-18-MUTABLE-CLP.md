# Mutable CLP propagation in Core

Date: 2026-10-18

Core now keeps active constraint state in a mutable, trailed kernel. Domain
narrowing, linear reduction, dependency scheduling and labeling assignments
can update that state without constructing a persistent `CLP.Store` at every
search node. The public solver still returns immutable stores and retains the
Reference engine's constraint algorithms, search order and observable errors.

This document describes the implementation and its acceptance contract.
Measurements, executed checks and source identities belong in the associated
[performance report](2026-10-18-ENGINE-MUTABLE-CLP.md).
The preceding [four-design stage](2026-10-18-MAJOR-DESIGN.md) describes the
native search driver that this kernel extends.

## Mutable state and rollback

[`CLP.Mutable`](../src/Infera/CLP/Mutable.hs) uses sparse `IntMap` indexes
whose entries point to mutable cells. A variable cell holds its optional
substitution binding, optional interval-with-holes domain and dependent
constraint IDs. Constraint cells hold individual residual constraints. Pending
constraint IDs, dirty variable IDs, watched IDs, the next constraint ID and
the active constraint count have separate mutable state.

Each semantic write records an undo action. A mark is a trail position;
rollback restores writes after that position in reverse order. Cell creation
and removal also participate in rollback. Public posting and binding
operations are atomic: an arithmetic/type error or contradiction restores the
operation's entry state before returning its error or failure result. A
successful operation leaves the new state available to later goals and to
older search marks.

The kernel performs occurs-checked unification directly against its variable
cells. Heap bindings accepted from Core use a separate binding API because
Core's unifier has already checked their validity. Both paths wake the same
watched-variable dependencies as persistent propagation.

Dropped constraints are removed from the live sparse index rather than left
as empty entries for every historical constraint ID. An undo action retains
the removed cell while an older mark can still need it. A constraint posted
and dropped between immutable snapshots needs no lasting snapshot delta;
removing a constraint that a previous snapshot contained still records the
required deletion.

## Native scheduling and linear propagation

The mutable scheduler processes the highest pending constraint ID first and
settles dirty variables in ascending ID order. It wakes dependencies before
moving domains across aliases, binds singleton domains and schedules any
further changes. The propagation budget remains 500 times the larger of one
and the constraint count at the start of the public propagation operation.
Unprocessed work remains queued when that safety budget is reached.

Linear equalities, inequalities and disequalities reduce against the mutable
substitution and domains. Bounds propagation retains the existing ordered
coefficient traversal and removable aggregate of finite bounds and infinity
counts. Single-variable bounds can discharge into a domain; single-variable
disequalities can discharge into domain holes. A residual's dependency entries
change only for variables entering or leaving it, avoiding temporary
unregister/register work for unchanged dependencies.

These choices preserve the persistent kernel's propagation strength and
ordering. The change concerns state representation and synchronization, rather
than introducing a different solver or a new labeling heuristic.

## Complex constraint bridge

Absolute-value relations, reification, global all-different and general term
disequality retain the single-step algorithms in
[`CLP`](../src/Infera/CLP.hs). The mutable scheduler creates an immutable
view, calls the pure reducer for one constraint and imports its effects before
continuing its own work queue.

For ordinary reductions, the pure reducer changes domains, watched IDs and
dirty IDs. Its dirty set identifies every changed domain, so the bridge
imports those cells and their watches without scanning all variables and
constraints or comparing the entire historical watched set. Top-level
nonlinear-to-linear conversion, the other pure reducer operation that can add
watches, is intercepted by the native reducer. Nested reification uses the
same substitution and cannot acquire another linearization in this path. The
single-step reducer does not settle singleton domains or bind substitutions;
the mutable normalizer performs that work afterward.

A symbolic all-different wrapper supplied through a public store can instead
post replacement pair constraints. This changes the next constraint ID and
selects the full store import path, including new constraints, dependencies,
counts and pending work. That discriminator depends on the current
single-step reducer contract and must be revisited if the pure reducer gains
other forms of state mutation.

Complex propagation algorithms therefore remain pure. This stage gives them
a mutable scheduler and a bounded delta bridge; it does not claim native
mutable implementations of matching, Hall-interval pruning, reification or
absolute-value propagation.

## Immutable snapshots

The kernel caches immutable substitution and store views. Changed-variable,
changed-substitution and changed-constraint sets update only affected entries
when a view is requested. Rollback invalidates the same cache entries as
forward writes. Snapshot construction preserves domains, substitutions,
dependency maps, pending and dirty sets, watched IDs, constraint counts and
IDs. Derived residuals appear in descending constraint ID order.

An imported public store may carry an explicit residual list awaiting the
public `propagate` operation. The snapshot machinery preserves that list until
propagation rebuilds its index, matching the persistent store boundary.

Returned snapshots contain immutable maps and terms, so advancing the Core
answer stream cannot mutate an earlier answer's store. Importing a Reference
leaf result or a saved minimum winner records undoable writes in the current
kernel. It does not replace the active trail with a snapshot's private
history or invalidate choices outside that operation.

## Core integration

[`Core.Run`](../src/Infera/Core/Run.hs) creates the kernel lazily. Pure
queries can keep an absent backend; a choice created before initialization
records that absence. If a later branch initializes constraints, returning to
the earlier choice restores the kernel's remembered initial mark.

Core choices now save optional constraint marks alongside their heap, heap
trail, output, scope, fresh-variable, table, dynamic-fact and watched-cell
state. Backtracking restores these components before entering the alternative.
Cuts discard alternatives while retaining the current constraint state.
Table iteration and opaque control sentinels use the same rollback boundary.

Posting, ordinary labeling and minimum labeling use the mutable adapter in
[`Core.Constraint`](../src/Infera/Core/Constraint.hs). List validation,
stable smallest-domain-first selection, ascending enumeration and the
different ordinary/minimum alias policies follow the preceding native search
implementation. These operations read mutable walks and domains without
freezing a complete store at each node.

After propagation, Core imports the final substitution values written since
the operation's mark and maps newly watched logical IDs to physical heap
cells. This removes full substitution differences and full watched-cell
rebuilding from the native node path. New variable cells created during a
binding import also consult existing watches. Reference imports and minimum
winner reconstruction retain their full boundary-specific watch rebuilding.
The collector continues to retain and relocate current watches, saved choice
watches and saved winner watches; the constraint trail itself contains logical
identities rather than heap addresses.

Minimum retries require an earlier mark than the tentative result. Core marks
the original state, performs domain restriction, incumbent bounding and the
trial assignment, then creates the retry choice with that original mark
before synchronizing propagated heap writes. A binding error stops exploration
at that variable level; a contradiction or completed child permits the next
value. Winners remain immutable snapshots, and restoring one stays undoable
under an enclosing choice.

## History reclamation and limits

When no Core choice survives, successful synchronization, answer boundaries
and cuts can commit the mutable state and discard its undo history. The
returned mark becomes the new root. Commit invalidates previously issued
marks and is therefore forbidden while a live alternative can refer to them.
It does not change semantic state, immutable snapshots or diagnostic counters.

Live outer choices still retain the writes needed to restore them. Removing
dropped constraint cells and committing unneeded undo history address distinct
forms of retention; neither makes the complete solver constant-space.
Substitutions and the historical watched-ID superset can grow with logical
state, and retained answer snapshots can also retain immutable data. Broader
memory claims require separate residency evidence over the relevant workload.

## Acceptance contract

Breadboard exercises affine equalities, disequality, all-different,
absolute-value cost terms, reification and branch-and-bound. Its fixed-row and
flexible placement paths must retain valid holes, electrical connectivity,
score and optimum. Minesweeper exercises Boolean domains, a long exact bomb
sum, overlapping window bounds, partition sums and ordinary labeling; seeded
and multiple-window examples add different search and propagation shapes.

Acceptance compares complete ordered answer/error/output streams with the
Reference engine, checks immutable store fields at kernel boundaries and
uses independent placement/grid models. Tiny initial collection limits,
retained answers, nested control scopes, imported Reference leaves, constrained
tables and nested minimums exercise the integration boundaries. Optional
propagation counters distinguish mutable linear work from complex reducer
calls; normal execution leaves those per-reduction counters disabled.

Performance comparisons must keep the same checked queries and runner in the
baseline and candidate. Algorithm coverage, parity, allocation, elapsed time
and residency are separate claims; the linked performance report records the
evidence obtained for each.

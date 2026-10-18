# Answers up to renaming, plain calls and the choice stack

Date: 2026-10-19

Three changes to the Core: answers are compared up to renaming of variables,
calls to predicates without declared contracts take a shorter path, and
choice points live in unboxed arrays. A fourth, moving continuation frames to
an unboxed stack, was built, measured and not adopted. Against `main` at
`1a97539`, checked loaded-query CPU falls 9-16% and GHC allocation 27-40% on
the four ordinary workloads.

## Answers up to renaming

The identity of an internal variable is an implementation detail. Parity
checks now compare answers, output and errors after a consistent renaming of
the variables inside each answer ([`Infera.Engine.Alpha`](../../src/Infera/Engine/Alpha.hs)).
Query variables keep their ids, since the query names them. Every Core
observer in the tests and benches uses it; no observer compares `ssFresh`.

Infera has no standard order of terms, so variable identity was observable
only through printed names (`write`, `term_str`, error messages). Those names
may now differ from the reference's; programs that compute with the printed
text of an unbound variable (for example its string length) see an
implementation-defined value.

### Lazy stable names

The Core no longer reproduces the reference's fresh ids. Clause entry does
not reserve ids and frame markers carry only the block size. A variable cell
gets a name when it first leaves the heap: an export, a constraint, a copied
answer ([`nameCell`](../../src/Infera/Core/Store.hs)). Names live in the
sparse address map, move with their cells during collection, are pruned when
the heap top falls below them, and are never reused within a query (the
counter does not move back on backtracking). Variable-variable unification
binds the younger cell to the older by address, as a WAM does; collection
preserves address order.

This removes the per-clause fresh-id bookkeeping, the backward marker scan in
every variable-variable unification, and the marker walk in the collector.

### A findall bug the old parity hid

`findall` must copy each solution. Three engines got this wrong in ways the
exact-id parity concealed:

* **Reference and legacy machine.** A solution's internal variables kept the
  ids of the branch that created them. Each branch started from the same
  fresh counter, and so did the code after the `findall`, so two solutions'
  variables, or a solution's variable and a later one, could be the *same*
  variable. `findall X (local X) L, local Y, Y = (pair linked linked)` gave
  `L = [pair linked linked]`. Both now rename each solution apart
  (`Reference.renameApart`) and advance the counter: `L = [pair _0 _0]`.
* **Core.** An unbound clause variable in the template was promoted to a
  fresh cell inside each branch, so solutions did not share it. Its copies
  were given the same logical id, so the answer *printed* as one shared
  variable, but binding one copy did not bind the others. Template slots now
  receive their stable cells before the `findall` begins, so every solution
  shares them, as in the reference's renamed clause.

Two legacy-machine test expectations that encoded the capture were corrected
(`MachineSubsearchTest`).

## Plain calls

A predicate without declared contracts has no signature to select, no guard
to push and no output to check. [`callPlain`](../../src/Infera/Core/Run.hs)
does only the collection check, the depth check and the inferred switch
commit; declared predicates keep the full path (`callDeclared`).

## The choice stack

A choice point was a ten-field boxed record in a boxed array, and pushing one
read four IORefs and took the `length` of the scope list. Now the marks (heap,
trail, output length, scope depth) are unboxed, and the alternative and the
branch-local state (tables, dynamic facts, constraint mark, watched cells) are
pointers in boxed arrays: a push allocates only its alternative. The choice
height, guard height and scope depth are unboxed counters instead of
`IORef Int`, whose every write allocated. A `Choice` record is still built on
cold paths (collection, the invariant checker).

## Continuation frames: measured, not adopted

Continuations were moved to an unboxed frame stack: frame words in an unboxed
array, goal lists and rare payloads in boxed arrays, WAM placement (a new
frame at the top, entering a frame lowers the top to above its continuation
but not below the newest choice's mark, backtracking restores the mark), and
in-place relocation by the collector. It passed the full suite and both
example sweeps.

It was slower. Once its own extra allocation was removed, it matched the
choice-stack build's allocation but took 5-14% more CPU (fib 45.4 vs 39.8 ms,
loop 9.8 vs 8.8 ms). A frame read is an IORef, a record and an array load,
and entering a frame updates the frame top, whereas allocating a six-word
continuation in GHC's nursery is already a pointer bump and dies young. The
WAM's reason for stack frames, avoiding general allocation, does not carry
over to GHC. Making the driver's integer arguments strict likewise cut
allocation 5-13% but did not reduce CPU, so it was not kept either.

The building of that frame stack exposed one real cost, now avoided: a
closure shared by several `step'` branches through a `where` binding is
allocated on every goal. Bindings that only some goal kinds need belong in
those branches.

## Measurements

Median of seven fresh processes per case, `bench/core-major` (loaded,
checked, per-query compilation included), `-O2`, macOS arm64, quiet machine,
same binary runner for both columns:

| Workload | `main` CPU ms | Now CPU ms | Change | `main` alloc MiB | Now alloc MiB |
| --- | ---: | ---: | ---: | ---: | ---: |
| Reverse, 100 x 30 | 9.71 | 8.15 | -16% | 36.9 | 24.7 |
| Loop, 90,000 | 10.12 | 9.04 | -11% | 34.3 | 20.6 |
| Fibonacci 25 | 47.00 | 40.89 | -13% | 161.1 | 112.8 |
| First 8-queens | 9.35 | 8.54 | -9% | 35.1 | 25.6 |

A late cost-centre profile (`--enable-profiling --profiling-detail=late`)
of the Core share of reverse: `unifyCompound` 20%, `step'` 16%,
`buildCompound` 13%, `matchHead` 12%, `buildArgs` 12%, clause entry and
selection 20%, groundness walks for inferred commits 4%. Fibonacci:
`step'` 26%, `evalFast` 14%, `matchHead` 10%, `candidateClauses` 9%. Head
matching, term construction, arithmetic and goal dispatch dominate; the
control records are a minor share. This is where the next work belongs:
specialised head and construction instructions, `candidateClauses` without
list allocation, compiled arithmetic shapes, and closure compilation of
clause bodies.

## Validation

* Full Haskell suite: 496 checks.
* `core-engine parity` over every example and parity file except blocks and
  database_access, normally and with collection at every call: 512 queries
  agree with the reference and the legacy machine in both modes. Those two
  examples take over 25 minutes in the reference/legacy engines, on `main`
  too; their complete CLI output is identical to `main`'s up to renaming,
  as is that of the other 16 examples.
* CLI acceptance, 56 harness tests and 61 LSP tests.

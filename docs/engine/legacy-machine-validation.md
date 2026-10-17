# Legacy machine and bytecode validation

This is historical validation detail for `Infera.Machine`, extracted from
an earlier version of the repository README. Statements below about the
public default or current gates describe those implementation stages.
Normal queries now use the core described in the [current engine guide](README.md).
Use the [performance overview](../performance/README.md) for the latest results.

The [machine heap](../../src/Infera/Machine/Heap.hs) uses paged cells and a trail with
immutable copy-on-write snapshots. Five generated
properties run 300 cases each against the existing unifier, checking term
round trips, ordered binding attempts, nested rollback, independent resumed
branches and allocations after checkpoints. Fixed cases cover occurs checks,
atomic failure, variable scope, typed scalars, NaN, signed zero, stale handles
and heap/trail page growth.

The public solver delegates to `Infera.Machine.Control` for indexed ordinary
clause execution, explicit tasks and backtracking choices, scoped cuts and
first-success commitments after output checks. Its immutable `start`/`resume`
boundary returns the existing `SearchItem` and `SolverState` types. Fourteen
control/bridge properties include 600 generated comparisons of ordered
answers and issues, plus retained/interleaved snapshots and adapter state.
Native scope frames now handle `call`, `once`, `not`, if-then-else and
`findall`, including isolated cuts, ordered issue handling and complete state
retention or rollback. Nine more properties add 300 generated nested-control
comparisons, findall sharing/fresh-ID/output checks, retry guards and lazy
resume checks.

Native CLP integration now keeps constrained clause calls, unification,
constraint posting, `label` and `labeling [min Cost]` on the machine driver.
Bindings wake the existing persistent propagators; propagated singletons
update the heap. Failed transactions, labeling alternatives and nested scopes
restore the heap, logical variable map and complete store together. Generated
tests compare ordered observations with the reference and bounded results with
independent models, including aliasing, domain holes, reification, absolute
values, large integers, branch-and-bound ties and immutable resumed searches.
Imported solver states preserve their original free-variable representatives
so domains and watched constraints continue to refer to the correct IDs.
General `minimize Cost Goal`, `forall`, file-backed DCGs, ordinary builtins and
dynamic fact operations also execute through native machine dispatch. Native
variant tables run their producer bodies on the driver, preserve complete
canonical answer/dependency state and retain the existing fixedpoint and
truncation behavior. The retained reference remains the oracle for generated
comparisons; production calls use the machine through the same public API.

The shipped breadboard placer is the native CLP acceptance example: `rc`,
`div` and `tri` optima match the reference, and the `tri` report is compared
byte for byte through native `phrase`/`emit` wrappers. Generated narrow grids
compare native and reference exhaustive labeling with an independent physical
grid enumerator; a wide case places three disconnected parts over columns
1 through 16. These checks validate holes, electrical nodes, shorts, jumper
counts, ground costs and the independent optimum.

The historical CLP integration gate passed 162 properties, including 13 native
CLP and four native breadboard properties. Initial validated
[breadboard samples](../performance/data/tsv/engine-native-clp-2026-10-16.tsv) put the experimental
machine about 2–7 times slower than the reference on these small cases.
This is binding/search integration evidence; a speed improvement remains a
later gate. The measurements exclude loading and CLI startup.

The machine reuses tail calls across a closed first-order graph of native
arithmetic, equality, guards and pure user predicates, including mutual
recursion and calls through helpers. Undeclared calls can carry free or structured
arguments, including shared variables and result terms. Ground declared
arguments can reuse frames when their contracts remain valid and no
`det`/`multi` required-success obligation survives. It retires redundant returns and
cut owners, and periodically rebuilds the active heap from reachable bindings.
Collection also reclaims completed non-tail activations at ordinary execution
boundaries. Raw graph copying preserves shared suffixes and alias syntax;
undeclared returns discard argument roots without delayed checks.
Live alternatives and opaque scopes own independent frozen snapshots; restoring
a snapshot restores its matching bindings, control, complete CLP store, tables,
dynamic facts and output. Selected sub-search states are synchronized into the
restored parent heap. Query variables and raw control syntax are retained;
unreachable internal activation bindings are reclaimed. Active constraint,
table and dynamic metadata survives collection. Declared input, sort and output
checks remain enforced. Nonground declared arguments and `det`/`multi` failure
obligations retain their ordinary return frames; cuts and effects remain outside
the source proof. `startGoals` retains
its explicit fuel limit; eligible calls through `start` reuse their depth
budget. `startMeasured` adds opt-in execution counters.

Fresh-process [tail measurements](../performance/data/jsonl/engine-tail-2026-10-16.jsonl) complete
one million iterations in 11.84 seconds without instrumentation. Peak RSS
stays about 81.5 MiB at 10k, 100k and 1m iterations; measured live counts stay
at 4 tasks, 2 cut owners, 1,038 cells and 138 bindings. RSS includes program
loading and fingerprinting. These historical samples establish the initial
scalar-loop memory gate. Broader fresh-process samples for free results and
fixed structured arguments are recorded separately in
[structured tail measurements](../performance/data/jsonl/engine-tail-structured-2026-10-16.jsonl).
Both new cases complete one million calls; peak RSS stays around 85 MiB at
10k, 100k and 1m calls, with maximum machine cell counts of 1,029 and 1,033.
Growing result terms remain live, and repeated structural traversal can add
substantial work. Those samples predate collection with live alternatives and
opaque scopes. The historical
[breadboard recheck](../performance/data/tsv/engine-structured-tail-breadboard-2026-10-16.tsv)
also predates the public facade switch and places the machine behind the
reference on these small cases. Later Step 1 samples are tracked in the
roadmap; current compiler evidence is in the control report. These
historical results establish no general performance improvement.

The historical Step 1 gate passed 278 Haskell properties (20,698 property test
cases), 37 editor/LSP tests, 20 harness tests and CLI/trace acceptance. The
[step 1 acceptance report](../performance/reports/engine-step1-acceptance-2026-10-16.md) records
that snapshot's local exit gates and remaining step 2 throughput work. Its
generated comparisons cover native builtins, table producers, mutual/helper
tail calls, collection with live
choices and nested scopes, retained snapshots and trace source/frame metadata.
Existing independent models, breadboard optima/report checks, contract errors,
ordered answers, duplicate preservation, residual constraints and output
remain acceptance criteria.

The first Step 2 slice is available through
`Infera.Machine.Control.solveQueryWithBackend Bytecode` and the corresponding
`start*WithBackend` checkpoint APIs. Existing entry points default to
`Interpreted`. Compiled head instructions inspect known caller structures
without building duplicate head graphs; free caller targets build only the
required source subtree before ordinary occurs-checked unification. All head
writes reach CLP together after the complete structural match succeeds.
After head matching and propagation accept, body terms are constructed one
reached goal at a time. Source locals map to compact operand positions once at
compilation; materialization validates their original raw logical roots, then
reads repeated operands by dense position, using bounded list reads for up to
four locals and arrays for larger layouts. Source-facing instruction views and
fresh IDs remain unchanged. Simple locals, scalars and all-local constructors
avoid temporary arrays. The materializer owns one rollback transaction for its
whole plan; checked scalar/constructor helpers avoid redundant nested marks.
Public heap builders retain their atomic behavior. Eighteen fixed arithmetic
and CLP builtins now share one multi-root argument plan and dispatch without
a callable wrapper; `unify` consumes raw handles and `is` imports only its
evaluated result. Tracing and malformed arities retain their source invocation
path. Local variables retain
their logical identities;
temporary constructor/scalar registers are reused after their last read.
Scalar sharing preserves exact bits. Pending code keeps suffix-live logical
IDs so collection can retire completed locals without losing future uses.
No mutable register or heap address escapes into a pending body frame. Body
syntax retains original local IDs. Known user calls dispatch directly, while
contracts, tables and backtracking retain the native driver's semantics.
Conjunction, disjunction, cuts, `call`, `once`, negation, if-then-else and
`findall` use pure compiled control continuations and the native choice/scope
driver. Untaken branches allocate no control wrappers or leaf graphs. Body
cuts rewrite recursively, including inside data; head data stays literal.
Dynamic/noncallable leaves and less-common meta/DCG operations use native
runtime handlers through invocation plans. Lazy clause plans now belong to
immutable predicate versions and are shared across queries. Exact source
witnesses prevent stale plans after public record edits; selected results are
memoized per query. Resolved calls carry their predicate and runtime metadata,
avoiding repeated lookups and dynamic-name scans. The full argument/environment
register design remains future work. Ordinary untraced/unmeasured invocations
dispatch directly below the collection threshold; collection, tracing and
measurement retain the existing queued boundary. Opaque searches keep lazy
protected-ID sets and convert them only when collection needs a list. Table
producer heads still use their existing template path; native producer bodies
select the requested backend. Compiler and
backend tests compare raw scalar bits, ordered observations, source frames and
repeated/interleaved resumes. The
[foundation report](../performance/reports/engine-step2-foundation-2026-10-16.md) records the
historical initial compiler gate: 315 Haskell properties (22,180 property test
cases), 37 editor/LSP tests, 20 harness tests and CLI acceptance passed. Its
initial comparison established working compiled dispatch and parity without
establishing a throughput gain. Subsequent implementation and validation are
recorded separately in the
[head/register report](../performance/reports/engine-step2-head-register-2026-10-16.md),
[lifetime report](../performance/reports/engine-step2-lifetimes-2026-10-16.md) and
[control report](../performance/reports/engine-step2-control-2026-10-16.md) and
[cache/dispatch report](../performance/reports/engine-step2-cache-2026-10-16.md) and
[operand report](../performance/reports/engine-step2-operands-2026-10-16.md).
The current gate passed 370 Haskell properties (25,723 cases), 47 LSP tests,
20 harness tests and CLI acceptance. Ordinary compiled execution skips
instruction statistics; measured variants distinguish accepted-head work from
reached body construction. The allocation changes establish smaller temporary
arrays and skipped future graphs; throughput results remain mixed. All 30
compiled residency samples and the six-sample interpreted recheck pass.

The historical Step 1 [fresh-process residency gate](../performance/data/jsonl/engine-step1-tail-2026-10-16.jsonl)
passed 28 checked samples, including repeated million-call mutual recursion,
live choices/findall, helpers, structured inputs and live CLP/table/dynamic
state. Peak RSS stayed around 127–128 MiB, including startup and source
fingerprinting; measured active heaps stayed at or below 1,037 cells. CI runs a
mutual/helper subset through `bench/check-tail-memory.py --quick` to catch
retained host-language history as well as growing machine state.

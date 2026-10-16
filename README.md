# Infera v2

A Prolog-inspired logic programming language implemented in Haskell, with
declared or inferred **sorts, modes and determinism**, **indexing** and
**tabling** on by default, **cut / if-then-else**, a simple **CLP(Z)** solver,
DCGs, and a hash-addressed **module system**.

The previous engine lives on the `v1` branch (tag `v1.0.0`).

## Install

With [Homebrew](https://brew.sh) (builds from source with Homebrew's GHC):

```
brew tap hyperswine/neoprolog https://github.com/hyperswine/NeoProlog
brew install infera
```

From a checkout, with GHC and cabal-install (for example via
[ghcup](https://www.haskell.org/ghcup/)):

```
cabal build
cabal test
cabal install            # puts `infera` in ~/.cabal/bin or ~/.local/bin
```

If linking fails on macOS with `tapi error: malformed file ... unknown
architecture`, your Command Line Tools SDK is newer than the linker Xcode
selects; build with `DEVELOPER_DIR=/Library/Developer/CommandLineTools`.

## Usage

```
infera <file.nprolog>      # load a file, run its inline queries, drop into the REPL
infera reg <file.nprolog>  # register a module in ./neoprolog.conf
infera check <files...>    # parse and analyse files, report errors (exit 1 on failure)
infera check --json <files...> # structured diagnostics for editors and tools
infera check --json --stdin <file> # check source from stdin at this file's path
infera --trace <file> ["query?"] # trace an explicit query, or the file's inline queries
```

`check` resolves imports and checks undefined predicates, call arities,
declarations without matching clauses, and literal arguments that conflict
with every declared signature. Singleton variables, conflicting flags, and
unreachable clause heads produce warnings. Errors exit 1; warnings alone exit
0. Informational performance suggestions also leave the exit status unchanged:

| code | opportunity |
| --- | --- |
| `perf-non-tail-recursion` | a self-recursive call has work after it |
| `perf-labeling-before-constraints` | later constraints could prune variables before enumeration |
| `perf-unbounded-labeling` | fresh labeled variables lack preceding finite bounds |
| `perf-unselective-index` | clauses share the same index key in every argument |

These are conservative source checks, with no timing estimate or automatic
rewrite. They suggest changes only when the relevant pattern can be identified;
preserving answers, order and declared contracts remains the programmer's job.
Checks do not execute inline queries or prove runtime mode/determinism
contracts. Dynamic call targets remain runtime checks.

JSON output is an array of `{file, severity, code, message, range}` objects on
stdout. Ranges use zero-based lines and UTF-16 character offsets, with an
exclusive end. Performance suggestions identify the recursive call, labeling
name or first clause head precisely when the source site is unambiguous.
Ambiguous sites and other semantic diagnostics retain the containing clause,
declaration or query range; parse errors identify the offending position. Imported diagnostics
retain their own source file. Human-readable diagnostics go to stderr.

`--stdin FILE` checks an unsaved buffer without writing `FILE`; its path supplies
the import context and diagnostic identity. Optional `--buffer SOURCE SNAPSHOT`
arguments supply unsaved dependency snapshots, preserving each original source
path. These checks use the same parser, import resolver and diagnostics as disk
checks.

REPL: clauses end with `.`, queries with `?`.  Commands: `:load <file>`,
`:reload`, `:sig [pred]` (declared and inferred signatures), `:preds`,
`:trace <query?>`, `:quit`.

```
cabal run infera -- examples/stdlib.nprolog
```

`:trace member X [a, b]?` traces one REPL query. The CLI equivalent is
`infera --trace examples/stdlib.nprolog "member X [a, b]?"`; omitting the query
runs the file's inline queries. CLI events go to stderr and ordinary answers
and output go to stdout. Runtime errors and incomplete searches exit nonzero.
Events include `Call`, `Exit`, `Redo`, `Fail`, `Cut` and `Exception`, with
activation frames and original source positions. Imported predicates retain
their file identities; generated DCG/control code and ambiguous equal source
occurrences fall back to the owning clause span. Table producer bodies also
retain their source positions and enclosing frames.

Tracing is opt-in and delivers events in batches at each public answer or
completion. A long search can accumulate a large batch and logical tail-return
metadata before yielding; this is an execution-event hook, not a live
single-step debugger. Trace buffers and deliberately retained continuations
are excluded from ordinary tail-loop residency measurements.

## Syntax

Mostly unchanged from v1:

```prolog
# comment
append [] L L.
append [H | T] L [H | R] <- append T L R.      # clause
greeting -> [hello], name.                     # DCG rule; { Goal } embeds a goal
> append X Y [1, 2]?                           # inline query, run on load
<- import "mymod#<sha1>".                      # directive
```

Terms: `atom`, `Var`, `_`, `42`, `1.5`, `'c'`, `"str"`, `f X (g Y)`, `[1, 2 | T]`,
`X :: Xs`.  Operators: `+ - * / % ^`, comparisons `< > <= >=`, `=` (unify),
`==` (structural equality), `!=` (delayed disequality), `is`, and the CLP(Z)
operators below.  Bodies may use `,`, `;`, `->` and `!`:

```prolog
sign N S <- (N > 0 -> S = pos ; N < 0 -> S = neg ; S = zero).
first X <- member X [a, b, c], !.
```

Builtins: `true fail not once call phrase findall forall minimize`,
effects `write writeln nl emit read_file phrase_from_file assert retract retractall`,
DCG helpers `seq wr nl sp fmt padl padr`,
type checks `var nonvar ground is_int is_float is_num is_str is_atom is_char is_list`,
strings `str_concat str_length str_chars str_atom str_num str_upper str_lower`.

Ground arithmetic inside call arguments is evaluated before head matching, so
`fact (N - 1) R` calls `fact 4 R`, and arithmetic in answers is evaluated.

## Declarations

```prolog
mypred : semidet (int: <=) (int: <=>) (str: =>).
```

| part | values |
| --- | --- |
| determinism | `det` (exactly one), `semidet` (at most one), `multi` (at least one), `nondet` |
| sort | `int float num str char atom any`, `list <sort>` |
| mode | `<=` input: ground at call, `=>` output: ground after, `<=>` no requirement |
| flags | `table notable index noindex unsafe dynamic` |

Bare modes are allowed (`f : det <= =>.`), a bare sort means `<=>`, and a
declaration with only flags (`nat : notable.`) applies to every arity of the
name.  Several declarations of one predicate are alternative modes; the first
whose inputs are ground is used.

Declared signatures are **enforced**: an unground input or a sort mismatch is
a runtime error, `det`/`multi` predicates that fail raise a determinism error,
and `det`/`semidet` predicates commit to their first solution.

### Inference

Undeclared predicates get the most general signature (`any`, `<=>`,
`nondet`) unless analysis can do better.  `:sig` shows the result:

```
length/2
  inferred: length : semidet (list any: <=>) (num: =>).   # semidet when argument(s) 1 ground
```

* **Sorts** come from head patterns, literals, arithmetic, string builtins and
  the sorts of called predicates, using bounded evidence propagation.
* **Modes**: `<=` is a conservative grounding prerequisite; `=>` promises
  grounding after success under the inferred prerequisites. Branches retain
  only common guarantees. Constraints on an unknown variable do not imply
  grounding. Input and output analyses run to convergence; input hints may
  overestimate prerequisites of predicates used in several relational modes.
* **Determinism**: `semidet` when clauses are pairwise exclusive (distinct
  principal functors, complementary guards such as `A >= B` / `B > A`, or a
  literal against a guard like `0` / `N > 0`, or cuts) and every body is at
  most semidet.  The exclusivity may depend on some arguments being ground;
  those positions are recorded and checked at call time.

Inferred signatures are advisory: they never raise errors.  The engine only
uses an inferred `semidet` to drop choice points, and only when the recorded
positions are ground in the actual call.  Everything else falls back to plain
backtracking.

Declaration alternatives are analysed in runtime selection order: every mode
that could precede the first definitely eligible mode contributes to the
guarantee. Guard proofs require shared operands to be ground before the call,
including calls with aliased arguments. Term identity (`==`, `!=`) is analysed
separately from numeric or lexical ordering. Numeric ordering places NaN after
other numeric values and compares numeric NaNs equally, so reversing operands
reverses the ordering; this does not change term identity.

## Engine

* Predicates are keyed by name **and arity**.  Calls to undefined predicates
  are errors.
* **Indexing**: every argument position is indexed on its principal functor;
  a call only tries clauses compatible with its bound arguments.  Disable with
  `noindex` or `<- noindex.`.
* **Tabling** (linear tabling with fixpoint iteration): calls are memoised by
  variant, left recursion terminates, `fib` is linear.  On by default for
  predicates that are recursive, pure (no output) and not merely structurally
  recursive (list walkers).  Disable with `notable` / `<- notable.`, force with
  `table`.  A tabled call collects all its answers first, so predicates with
  infinitely many answers must be declared `notable`; otherwise the fixpoint
  stops after a bound and reports "search depth limit reached".  Calls
  involving constrained variables are never tabled.
* **Cut** uses explicit choice-stack barriers. It is transparent through `,`,
  `;` and the selected arm of `->`; `call`, `not`, `once`, `findall` and an
  if-then-else condition have isolated cut scopes. The public lazy search
  stream retains compatible foreign-owner markers.
* Output (`write`, `nl`, `emit`) is collected per answer and printed with it.

## Effects and pure IO

Predicates are pure unless declared `unsafe`.  A clause of a predicate that
is not `unsafe` may not use `write`/`writeln`/`print`/`nl`, `emit`,
`read_file`/`phrase_from_file`, `assert`/`retract`/`retractall`, or cut, and
may not call an unsafe predicate; the program is rejected at load time with
an `unsafe-call` error naming the fix.  Inline queries (`> ...?`) are the
entry points and may do anything.

Text is produced and consumed with DCGs, so a report is a grammar for its own
output and effects stay at the edges:

```prolog
report Rows -> "name      score", nl, rows Rows.
rows [] -> [].
rows [row N S | Rs] -> padr N 8, padl S 7, nl, rows Rs.
line [row N S] -> seq Cs, " ", wr S, { str_chars NS Cs, str_atom NS N }.

> emit (report [row alice 3, row bob 12])?          # print a grammar's text
> phrase_from_file (file_rows Rows) "scores.txt"?   # parse a file
> phrase (line R) "alice 3"?                        # parse a string, purely
```

DCG helpers: `"literal"`, `seq Xs`, `wr Term`, `nl`, `sp`,
`fmt "~w ~d ~s ~a ~n" Args`, `padl Term Width`, `padr Term Width`.  Plain
builtins: `term_str`, `str_lines`, `char_code`; comparisons order characters,
strings and atoms as well as numbers.  File paths must be string literals: the
engine is pure, so the loader reads the files up front.

Dynamic facts: `seen : dynamic.` declares a predicate with no clauses whose
facts are added with `assert (seen X)` and removed with `retract`/`retractall`
from an `unsafe` predicate.  They live in the solver state, so they are
undone on backtracking.  See `examples/io.nprolog`.

## CLP(Z)

```prolog
X in 1..9            # also [X, Y] in 0..sup ; inf / sup for open bounds
A #= B  A #!= B  A #< B  A #> B  A #<= B  A #>= B
all_different Xs
reify (A #<= B) Truth # Truth is 0 or 1, equivalent to the relation
label Xs             # enumerate, smallest domain first
labeling [min Cost] Xs # one minimum, with branch-and-bound pruning
minimize Cost Goal   # one minimum of a finite goal's answers
```

Interval domains with holes and bounds propagation for linear constraints.
Changed variables wake their dependent constraints, and list domains are posted
as a batch. Linear sums use aggregate bounds instead of rescanning the sum for
each variable. Other non-linear constraints wait until they become linear or ground. Residual
domains and constraints are shown in answers (`X in 4..5`, `X + Y #= 10`).
See `examples/v2_clp.nprolog` (SEND + MORE = MONEY, N-queens).

`all_different` is a global constraint: fixed values are excluded from other
variables, and bounded Hall-interval and matching checks detect impossible
groups and prune unsupported values. Large domains retain cheaper propagation.
Stronger pruning can change the order of labeled solutions.
`reify Relation Truth` supports all six CLP comparisons; either the relation or
its Boolean truth can constrain the other. `D #= abs Expr` propagates bounds
when `D` and `Expr` are linear expressions, retaining the absolute-value
relation while its sign is unknown.

### Optimisation

```prolog
> [X, Y] in 0..10, X + Y #>= 7, Cost #= 2 * X + Y,
  labeling [min Cost] [X, Y]?
# X = 0, Y = 7, Cost = 7
```

`labeling [min Cost] Vars` propagates a strict cost bound after each improved
answer. `Vars` must be a proper list of integers or variables with finite
domains, and `Cost` must become a ground integer at each complete assignment.
It returns one optimum and retains the first encountered on ties. Variable
selection remains smallest-domain-first; pruning may change which tied
assignment is encountered first. Only the `[min Cost]` option is supported.

For costs computed after solving, `minimize Cost Goal` scans a finite search
and retains only its best answer, including that answer's bindings and output.
It does not prune the search and requires a ground integer cost in every
answer. Ties keep the first answer; no answers means failure. Cuts inside
`Goal` are local. Errors or an incomplete search produce no claimed optimum.
The breadboard placer posts a constrained score before
`labeling [min Cost] Vars`, so incumbent bounds prune partial placements while
preserving its jumper/window priorities. The original ground score and ordinary
placement enumerator remain available for exhaustive comparisons.

### Minefield generation

`examples/minesweeper.nprolog` generates binary grids with an exact bomb count
and limits on every overlapping rectangular window. It uses the existing
CLP(Z) solver; no new builtins are required.

```sh
infera examples/minesweeper.nprolog
```

```prolog
# Width 10, height 10, exactly 50 bombs, at most 2 in every 2x2 window:
> once (mines 10 10 50 2 Grid)?

# Change search order with a reproducible integer seed and print * / . cells:
> show_seeded 10 10 50 [window 2 2 2] 42?

# Combine limits: at most 2 per 2x2 and at most 3 per 3x3:
> once (minefield_seed 8 6 12 [window 2 2 2, window 3 3 3] 42 Grid)?
```

`minefield Width Height Bombs Rules Grid` enumerates valid grids; wrap it in
`once` to get one. `minefield_seed` adds a seed before `Grid` to permute search
order. A grid contains `Height` rows of `Width` values (`1` bomb, `0` clear).
Incompatible requirements return no answers. A window larger than the board
has no matching region, so its rule is vacuous. Disjoint tile counts strengthen
propagation without changing the solution set, including partial edge tiles.

Seeded generation is reproducible, rather than uniform random sampling. A
2x2 cap still allows long stripes; add larger windows to restrict those.
Small-board properties compare all solutions against independent exhaustive
enumeration, with acceptance checks for the 10x10 / 50-bomb case.

## Modules

```
infera reg examples/mymod.nprolog   # → mymod#<sha1> in ./neoprolog.conf
```

```prolog
<- import "mymod#<sha1>".
main <- mymod:greet "world".
```

Imported clauses and declarations are prefixed with `mymod:`; a module's own
imports are resolved recursively.

## Editor support

[lsp/](lsp/) contains a VS Code extension with a language server: semantic
highlighting, hover (built-ins, declared signatures), go to definition and
references (including `mod:pred` through `neoprolog.conf`), completion,
document symbols, and diagnostics (undefined predicates, arity mismatches,
declaration problems, singleton variables and parser errors). All validation
comes from the compiler through `infera check --json --stdin`; open, edited and
saved buffers use the same messages, codes, severities and source ranges.
Unsaved imports are included, and outdated checks are cancelled. Untitled
buffers use the workspace as their import context. `infera.checkOnChange`
controls live checks (enabled by default); `infera.checkOnSave` controls checks
on save. A missing or incompatible compiler produces an explicit availability
warning; navigation and highlighting continue without a separate validator.

Extension version **2.0.2** displays the compiler's four `perf-*` suggestions
as informational diagnostics, using the editor's theme colors.
`infera.performanceHints` is enabled by default; disabling it hides performance
suggestions while retaining correctness diagnostics. Declared `unsafe` and
`dynamic` predicates receive semantic underlines at declarations, clause heads
and resolved calls, including imported live buffers and statically known
`call`/`phrase` targets. Effectful built-ins are also underlined. Overloads are
distinguished by arity, and comments, strings and data atoms are excluded.
Themes and user settings can override the underline styles; the markers
describe effects and declarations without adding warnings for intentional use.

```
cd lsp && npm install && npm run install-extension
```

## Roadmap

The public `Infera.Engine` now runs an explicit abstract machine with a trail,
choice-point stacks, last-call optimisation, heap reclamation and tracing.
`Infera.Engine.Reference` retains the previous resolver for comparisons through
the bytecode transition. Step 2 now has opt-in compiled clause activation,
specialized head matching, per-goal body allocation, temporary register reuse,
compiled core controls/cut barriers, lazy predicate-owned plans and resolved
ordinary user calls, dense operand layouts and transaction-owned data allocation;
the public
solver still selects the
interpreted native driver. [docs/engine-roadmap.md](docs/engine-roadmap.md)
tracks the remaining argument/environment register design, indexing
instructions and operand dispatch work. The
[foundation report](docs/engine-step2-foundation-2026-10-16.md) records the
minefield regression repair and initial compiler slice; the
[head/register report](docs/engine-step2-head-register-2026-10-16.md) covers the
subsequent matcher and allocation changes. The
[lifetime report](docs/engine-step2-lifetimes-2026-10-16.md) covers temporary
register reuse and pending body continuations. The
[control report](docs/engine-step2-control-2026-10-16.md) covers compiled
branches, opaque searches and cut barriers. The
[cache/dispatch report](docs/engine-step2-cache-2026-10-16.md) covers immutable
code reuse, edit correctness and cold/warm scaling. The
[operand report](docs/engine-step2-operands-2026-10-16.md) covers dense local
dispatch, simple operand fast paths, deferred protected-root sets and matched
batch measurements. Bytecode is the intended eventual
default; the roadmap records its correctness and performance migration gates.
Proved tail transfers
reuse their depth budget; other nested calls
retain the 100 000 activation limit and explicit exhaustion reporting.
`bench/run.sh` runs checked engine benchmarks. Earlier relative-speed numbers
from the unchecked harness are historical observations, not validated baselines.
The roadmap preserves historical local baselines with checked warmups and
samples; current changes need source/profile-matched measurements.

## Layout

```
src/Infera/Syntax.hs    terms, declarations, parser, printer
src/Infera/Unify.hs     substitutions, unification, renaming
src/Infera/Compile.hs   head matching, allocation plans and pure control instructions
src/Infera/Compile/Cache.hs lazy clause plans with exact source witnesses
src/Infera/Machine/Heap.hs paged heap/trail and immutable snapshots
src/Infera/Machine/Bridge.hs logical variables and complete solver-state adapters
src/Infera/Machine/Control.hs native task/choice stacks, scopes and immutable resume
src/Infera/Machine/CLP.hs native binding transactions over persistent propagation
src/Infera/Machine/Tail.hs closed first-order call-graph proof for tail reuse
src/Infera/Machine/Builtins.hs native builtin dispatch and dynamic fact operations
src/Infera/Machine/Bytecode.hs specialized head matching and deferred body construction
src/Infera/Machine/Table.hs native variant-table producers and fixedpoint iteration
src/Infera/Machine/Trace.hs opt-in execution events and source metadata
src/Infera/Arith.hs     numeric evaluation
src/Infera/CLP.hs       domains, linear constraints, propagation
src/Infera/Program.hs   predicate table, indexes, signatures, flags
src/Infera/Infer.hs     sort / mode / determinism / recursion analysis
src/Infera/Diagnostic.hs source-aware compiler diagnostics and JSON output
src/Infera/Engine.hs    public solver facade over the machine
src/Infera/Engine/Reference.hs retained reference resolver and shared public result types
src/Infera/Module.hs    neoprolog.conf and imports
src/Infera/Repl.hs      interactive loop
test/InferaTest.hs      hedgehog test suite
test/CorrectnessTest.hs generated correctness tests with independent models
test/InferenceTest.hs   inferred pruning compared with unpruned execution
test/MachineHeapTest.hs heap unification, rollback and snapshots compared with the reference
test/MachineControlTest.hs ordered control streams, adapters and retained snapshots
test/MachineSubsearchTest.hs native call/once/not/if/findall and scoped state retention
test/MachineCLPTest.hs native propagation, labeling, rollback and immutable resumes
test/MachineBreadboardTest.hs native placer compared with exhaustive and independent grids
test/MachineTailTest.hs tail reuse, live roots, immutable resumes and conservative fallbacks
test/MachineStructuredTailTest.hs free/structured tail arguments, sharing and declared contract fallbacks
test/MachineReclaimTest.hs generated raw-root, complete-store and reclamation models
test/MachineGeneralTailTest.hs mutual/helper tail reuse with live choices and scopes
test/MachineInternalTailTest.hs tail retirement with parked retries, late errors and success barriers
test/MachineSnapshotTest.hs independent frozen rollback snapshots across collection
test/MachineBuiltinTest.hs native builtin and dynamic fact parity
test/MachineTableTest.hs native tabling and producer parity
test/MachineTailProofTest.hs closed call-graph proof and tail-reuse exclusions
test/MachineTraceTest.hs trace parity, source locations, frames and cut boundaries
test/MachineGraphReuseTest.hs shared argument graphs and normalization compatibility
test/MachineNormalizeTest.hs generated raw graph normalization, alias and scalar-bit parity
test/CompileTest.hs     generated compiler register contracts and fallback boundaries
test/MachineBytecodeTest.hs interpreted/bytecode/reference parity and immutable resumes
test/MachineHeadTest.hs whole-head CLP transactions, raw IDs, register sharing and snapshots
test/MachineLifetimeTest.hs pending body roots, register reuse and incremental allocation parity
test/MachineCompiledControlTest.hs generated control trees, cut barriers, scopes and trace parity
test/MachineEnvironmentTest.hs branch-owned environments and graph relocation models
test/MachineGeneralReclaimTest.hs non-tail collection with contracts, cuts and effects
test/PerformanceDiagnosticTest.hs generated performance-advice models and precise source locations
examples/               stdlib, v2_decls, v2_clp, v2_tabling, breadboard (CLP placer), jumpman (one rule set: verify / solve / play / generate), ...
Formula/infera.rb       Homebrew formula
bench/                  engine benchmarks (infera vs swipl vs scryer)
bench/check-tail-memory.py fresh-process residency gate, including CI quick mode
bench/machine-minefield.hs validated larger minefield setup/generation regression runner
bench/machine-bytecode.hs serial checked reference/interpreted/bytecode comparison
bench/machine-cache.hs fresh-process cold/warm predicate-cache comparison
docs/engine-roadmap.md  plan for the abstract machine and bytecode engine
docs/engine-step2-foundation-2026-10-16.md regression repair and opt-in compiler evidence
docs/engine-step2-head-register-2026-10-16.md specialized head matching and register allocation
docs/engine-step2-lifetimes-2026-10-16.md per-goal body construction and logical root lifetimes
docs/engine-step2-control-2026-10-16.md compiled controls/cuts and default-backend migration gates
docs/engine-step2-cache-2026-10-16.md predicate caching, dispatch and cold/warm evidence
docs/engine-step2-operands-2026-10-16.md dense operands, owned allocation and performance evidence
lsp/                    VS Code extension and language server
```

## Validation

CI is configured to build and test on Linux and macOS with GHC 9.8.2 and Node 22. It runs the
Haskell properties, editor and language-server integration tests, and real CLI
diagnostic checks. Optimisation properties compare generated finite problems
against exhaustive search; breadboard acceptance compares complete placements
and costs for `rc`, `div`, and `tri` with the previous exhaustive implementation.

The generated correctness properties run 300 cases each with structural
shrinking and coverage checks. Independent Haskell models check unification,
finite CLP solutions and both optimisers, tabled graph reachability, ordered
fact indexing, arithmetic, and diagnostic arities, sorts and UTF-16 locations.
It also exercises recursive term round trips, variable aliases, constraint
ordering, domain holes, integers beyond machine size, and minimum-cost ties
with output. Fixed regressions cover character and string escaping.

Inference tests compare ordered answers (including duplicates and residual
constraints), output, errors and exhaustion against the same loaded program
with only inferred pruning disabled. Declared commitments, indexes and tabling
remain identical. Generated programs vary guards, mixed literal types, nested
and aliased heads, declaration alternatives, long dependencies, controls and
cuts; positive controls keep useful conditional semidet optimisations enabled.

The [machine heap](src/Infera/Machine/Heap.hs) uses paged cells and a trail with
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
[breadboard samples](docs/engine-native-clp-2026-10-16.tsv) put the experimental
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

Fresh-process [tail measurements](docs/engine-tail-2026-10-16.jsonl) complete
one million iterations in 11.84 seconds without instrumentation. Peak RSS
stays about 81.5 MiB at 10k, 100k and 1m iterations; measured live counts stay
at 4 tasks, 2 cut owners, 1,038 cells and 138 bindings. RSS includes program
loading and fingerprinting. These historical samples establish the initial
scalar-loop memory gate. Broader fresh-process samples for free results and
fixed structured arguments are recorded separately in
[structured tail measurements](docs/engine-tail-structured-2026-10-16.jsonl).
Both new cases complete one million calls; peak RSS stays around 85 MiB at
10k, 100k and 1m calls, with maximum machine cell counts of 1,029 and 1,033.
Growing result terms remain live, and repeated structural traversal can add
substantial work. Those samples predate collection with live alternatives and
opaque scopes. The historical
[breadboard recheck](docs/engine-structured-tail-breadboard-2026-10-16.tsv)
also predates the public facade switch and places the machine behind the
reference on these small cases. Later Step 1 samples are tracked in the
roadmap; current compiler evidence is in the control report. These
historical results establish no general performance improvement.

The historical Step 1 gate passed 278 Haskell properties (20,698 property test
cases), 37 editor/LSP tests, 20 harness tests and CLI/trace acceptance. The
[step 1 acceptance report](docs/engine-step1-acceptance-2026-10-16.md) records
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
Public heap builders retain their atomic behavior. Local variables retain
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
[foundation report](docs/engine-step2-foundation-2026-10-16.md) records the
historical initial compiler gate: 315 Haskell properties (22,180 property test
cases), 37 editor/LSP tests, 20 harness tests and CLI acceptance passed. Its
initial comparison established working compiled dispatch and parity without
establishing a throughput gain. Subsequent implementation and validation are
recorded separately in the
[head/register report](docs/engine-step2-head-register-2026-10-16.md),
[lifetime report](docs/engine-step2-lifetimes-2026-10-16.md) and
[control report](docs/engine-step2-control-2026-10-16.md) and
[cache/dispatch report](docs/engine-step2-cache-2026-10-16.md) and
[operand report](docs/engine-step2-operands-2026-10-16.md).
The current gate passed 361 Haskell properties (25,018 cases), 37 LSP tests,
20 harness tests and CLI acceptance. Ordinary compiled execution skips
instruction statistics; measured variants distinguish accepted-head work from
reached body construction. The allocation changes establish smaller temporary
arrays and skipped future graphs; throughput results remain mixed. All 30
compiled residency samples and the six-sample interpreted recheck pass.

The historical Step 1 [fresh-process residency gate](docs/engine-step1-tail-2026-10-16.jsonl)
passed 28 checked samples, including repeated million-call mutual recursion,
live choices/findall, helpers, structured inputs and live CLP/table/dynamic
state. Peak RSS stayed around 127–128 MiB, including startup and source
fingerprinting; measured active heaps stayed at or below 1,037 cells. CI runs a
mutual/helper subset through `bench/check-tail-memory.py --quick` to catch
retained host-language history as well as growing machine state.

```sh
cabal build all
cabal test --test-show-details=direct
npm ci --prefix lsp
INFERA_BIN="$(cabal list-bin exe:infera)" npm test --prefix lsp
python3 test/cli.py "$(cabal list-bin exe:infera)"
python3 -m unittest discover -s test -p bench_harness_test.py
```

The engine benchmark harness checks successful execution and independent expected
results for naive reverse, a counting loop, untabled Fibonacci and 8 queens.
Every warmup is validated; timed runs report medians and individual samples.
Errors, wrong answers, missing completion markers and timeouts exit nonzero
without a timing result for the failed case. Engine processes run in temporary
directories, and executable paths are passed directly without a shell.

```sh
INFERA_BIN="$(cabal list-bin exe:infera)" sh bench/run.sh --runs 3 --warmup 1 --timeout 30
# Select an engine/workload or emit JSON Lines:
sh bench/run.sh --engine infera --case fib --json
```

Without `--engine`, the runner includes installed SWI-Prolog and Scryer engines.
Explicitly requesting an unavailable engine is an error. `--binary` overrides
the Infera executable; `SWIPL_BIN` and `SCRYER_BIN` override comparison binaries.
JSON records include workload hashes, executable paths, runner information and
the Infera RTS options. Timings include CLI startup/loading/output; record build
revision and compiler flags alongside any baseline. Ordinary CI runs harness
failure tests and a checked smoke workload, with no noisy timing threshold.

Performance tests compare the constraint store with a frozen full-scan reference,
and eligible delta tabling with ordered observations from the general evaluator.
Breadboard scoring and optima have independent arithmetic and exhaustive models.
Run `python3 test/bench.py "$(cabal list-bin exe:infera)"` for validated local
timings; see [benchmark results and scope](docs/performance.md). Timing thresholds
are not correctness gates.

The optional machine/reference breadboard benchmark loads and checks the
program once, then validates one warmup and three measured executions per
engine/case with a 30-second timeout:

```sh
cabal bench machine-breadboard --offline --enable-optimization=2 --benchmark-options='+RTS -T -RTS'
```

It reports wall/CPU samples, source fingerprint and compiler/platform metadata.
The measured work includes execution, projection and result validation, and
excludes parsing, loading and inference. This scope differs from CLI startup
benchmarks. Failed, exhausted or invalid results do not produce a timing row;
there is no CI timing threshold or bounded-residency claim.

The opt-in compiler comparison runs first-order helper-dispatch, structured
list/constructor and structured-head workloads serially through Reference,
Interpreted and Bytecode:

```sh
cabal bench machine-bytecode --offline --enable-optimization=2 --benchmark-options='+RTS -T -RTS'
```

It checks an independent result model and the complete ordered
answer/residual/output/error/exhaustion stream, with one warmup and three
validated samples per engine/case under explicit 30-second budgets. Distinct
unused variable bases prevent sharing an evaluated pure search across samples.
An untimed measured probe requires positive compiled-activation, instruction and
direct-call counters and reports head-constructor avoidance and register usage.
These VM counters describe accepted activations only; rejected head attempts
return no activation statistics. Ordinary timed runs disable counter sampling.
The untimed compiled probe warms reached immutable predicate plans. Timing
includes fresh per-query dispatch/tail setup, execution, projection and validation,
excluding program parsing/checking and CLI startup. The runner records its
source fingerprint, compiler, platform and build scope, with no speed threshold.

`machine-cache` separates the first compiled query from a query after one
checked warmup. Each invocation emits one checked sample and runs its measured
path probe after timing; every search has fresh logical state. Run each sample
in a fresh process, for example:

```sh
cabal bench machine-cache --offline --enable-optimization=2 --benchmark-options='--engine bytecode --phase cold --case helper-1000'
cabal bench machine-cache --offline --enable-optimization=2 --benchmark-options='--engine bytecode --phase warm --case minefield-16'
```

Cases cover helper dispatch with 0/100/1,000 unused predicates, structured heads,
compiled opaque control and the 16x16 minefield acceptance grid. Reference and
explicit Interpreted selection remain available for comparisons.

Warm control and breadboard comparisons can batch fresh validated queries to
reduce timer noise. Cold cache samples require batch size one; each warm batch
query still starts with a fresh heap, store, tables and dynamic facts. Runners
report both total and per-query time, using bounded unused variable bases
behind distinct opaque nonces to avoid reusing evaluated searches:

```sh
cabal bench machine-cache --offline --enable-optimization=2 --benchmark-options='--engine bytecode --phase warm --case controls --batch 100'
cabal bench machine-breadboard --offline --enable-optimization=2 --benchmark-options='--batch 100'
```

The separate tail runner verifies and fully drains one query per fresh process:

```sh
cabal bench machine-tail --offline --enable-optimization=2 --benchmark-options='1000000 +RTS -T -s -RTS'
cabal bench machine-tail --offline --enable-optimization=2 --benchmark-options='1000000 --unmeasured +RTS -T -s -RTS'
# A free output variable or a fixed structured input with a shared leaf:
cabal bench machine-tail --offline --enable-optimization=2 --benchmark-options='100000 --case result +RTS -T -s -RTS'
cabal bench machine-tail --offline --enable-optimization=2 --benchmark-options='100000 --case structured --unmeasured +RTS -T -s -RTS'
# Tail reuse with mutual recursion, a caller choice or an opaque scope:
cabal bench machine-tail --offline --enable-optimization=2 --benchmark-options='100000 --case mutual --unmeasured +RTS -T -s -RTS'
cabal bench machine-tail --offline --enable-optimization=2 --benchmark-options='100000 --case choice --unmeasured +RTS -T -s -RTS'
cabal bench machine-tail --offline --enable-optimization=2 --benchmark-options='100000 --case once --unmeasured +RTS -T -s -RTS'
```

Repeat at 10k and 100k iterations to compare memory growth. Its JSON separates
machine high-water counters from RTS process residency; normal execution
avoids counter sampling. Cumulative allocated bytes still grow with work.
`--case ground` retains the historical scalar fixture and is the default;
`result` and `structured` validate their corresponding output bindings too.
Additional cases are `mutual`, `helper`, `choice`, `once`, `call`, `if`,
`findall`, `clp`, `cached` and `dynamic`, covering the current collection
contexts with independently checked expected results.

Failures print a seed and shrink path. To replay a counterexample, open
`cabal repl infera-test` and call `replay "PROPERTY NAME" (Seed VALUE GAMMA)
"SHRINK PATH"` with the values from the failure report. Replay is an interactive
debugging aid; use `cabal test` for the suite's pass/fail exit status.

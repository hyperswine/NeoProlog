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
with every declared signature. Singleton variables (`singleton-variable`),
conflicting flags (`conflicting-flags`), unreachable clause heads
(`head-sort-mismatch`) and clauses that shadow a builtin (`shadowed-builtin`)
produce warnings. Builtins are matched before user clauses, so clauses for a
builtin's name and arity such as a user-defined `is/2` or `findall/3` never
run; the warning names the builtin and asks for a rename. Variables used once
in an inline query are answer variables and are not reported as singletons.
Errors exit 1; warnings alone exit 0. Informational performance suggestions
also leave the exit status unchanged:

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

## Examples

Classic problems, each in one commented file whose inline queries print the
results (`infera examples/queens.nprolog`):

| file | problem | technique |
| --- | --- | --- |
| `queens.nprolog` | N-queens three ways, solution counts, symmetry classes | generate and test, early pruning, CLP(Z) |
| `blocks.nprolog` | blocks world: shortest plans, the Sussman anomaly, every reachable state | breadth-first search, tabling over a cyclic graph |
| `timetable.nprolog` | a school week of teachers, courses, rooms and students | search plus CLP(Z) with reification; rules rechecked as queries |
| `stable_matching.nprolog` | Gale-Shapley pairing, all stable pairings, electives with seats | list algorithms, a theorem checked on an instance |
| `database_access.nprolog` | readers and writers sharing a database, four protocols | tabling as a model checker, shortest failing runs, fair loops |

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

The repository includes `infera.conf` so `examples/facts2.nprolog` can resolve
its existing `facts#...` reference from a fresh checkout. Module IDs are exact
keys in the selected configuration; imports do not guess a file from its name.
`neoprolog.conf` takes precedence over `infera.conf`, and the files are not
merged. If you maintain a local `neoprolog.conf`, copy the example mapping into
it. A nearer map such as `examples/neoprolog.conf` also shadows the root map
in the editor. `infera reg` generates a key from the absolute file path, so a newly
registered or moved module can have a different key from an older example.

## Editor support

[lsp/](lsp) contains a VS Code extension with a language server: semantic
highlighting, hover (built-ins, declared signatures), go to definition and
references (including `mod:pred` through `neoprolog.conf`), completion,
document symbols, and diagnostics (undefined predicates, arity mismatches,
declaration problems, singleton variables and parser errors). All validation
comes from the compiler through `infera check --json --stdin`; open, edited and
saved buffers use the same messages, codes, severities and source ranges.
Only the changed buffer and its transitive importers are scheduled for checks.
Unchanged source, dependency and module-map contents reuse cached compiler
diagnostics; duplicate saves and watcher events do not rerun the compiler.
Only relevant unsaved imports are included, and outdated checks are cancelled.
CLP operators such as `#=`, `#!=` and `#<=` provide hover documentation with
propagation behavior and executable examples. Untitled
buffers use the workspace as their import context. `infera.checkOnChange`
controls live checks (enabled by default); `infera.checkOnSave` controls checks
on save. A missing or incompatible compiler produces an explicit availability
warning; navigation and highlighting continue without a separate validator.

Extension version **2.0.4** includes dependency-aware diagnostic caching and
detailed CLP operator hovers. The compiler's four `perf-*` suggestions appear
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

## Engine and documentation

Normal CLI and REPL queries run on the core resolution engine: compiled head
and body plans, tagged heap cells, argument registers, a conditional trail,
explicit continuations and compacting collection. Tracing and the goal-level
library APIs still use the earlier machine. Unsupported core constructs
restart on that machine and skip already-delivered search items.

Start with the [documentation index](docs/README.md) or the
[current engine guide](docs/engine/README.md). The
[performance overview](docs/performance/README.md) links to checked results,
dated reports and raw measurements. The
[engine roadmap](docs/engine/roadmap.md) records the earlier machine/bytecode
plan; its historical backend decisions do not describe the current default.

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
test/MachineTypedBuiltinTest.hs generated arithmetic/CLP operand and transaction parity
test/MachineHeadTest.hs whole-head CLP transactions, raw IDs, register sharing and snapshots
test/MachineLifetimeTest.hs pending body roots, register reuse and incremental allocation parity
test/MachineCompiledControlTest.hs generated control trees, cut barriers, scopes and trace parity
test/MachineEnvironmentTest.hs branch-owned environments and graph relocation models
test/MachineGeneralReclaimTest.hs non-tail collection with contracts, cuts and effects
test/PerformanceDiagnosticTest.hs generated performance-advice models and precise source locations
examples/               stdlib, v2_decls, v2_clp, v2_tabling, breadboard (CLP placer), jumpman (one rule set: verify / solve / play / generate), the classics above, ...
Formula/infera.rb       Homebrew formula
bench/                  engine benchmarks (infera vs swipl vs scryer)
bench/check-tail-memory.py fresh-process residency gate, including CI quick mode
bench/machine-minefield.hs validated larger minefield setup/generation regression runner
bench/machine-bytecode.hs serial checked reference/interpreted/bytecode comparison
bench/machine-cache.hs fresh-process cold/warm predicate-cache comparison
docs/README.md          documentation index
docs/engine/            current engine guide, contracts and implementation history
docs/performance/       performance overview and dated reports
docs/performance/data/  raw JSONL and TSV benchmark records
docs/website/           published language/tooling reference
docs/dash/              Dash docset builder and feed
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

Core acceptance compares ordered answers, output, errors and exhaustion
against both the reference resolver and the earlier machine, and replays
fixtures with frequent collection. Dedicated regressions cover declared tail
recursion and collection workspace growth. The
[reverse report](docs/performance/reports/engine-reverse-2026-10-17.md) records
the completed 391-property suite, all 296 example/parity queries, 61 LSP tests
and 34 benchmark-harness tests.

The older machine remains covered for tracing, fallback and goal-level APIs.
Its detailed [machine/bytecode validation history](docs/engine/legacy-machine-validation.md)
is kept separately from the current execution guide.

```sh
cabal build all
cabal test --test-show-details=direct
npm ci --prefix lsp
INFERA_BIN="$(cabal list-bin exe:infera)" npm test --prefix lsp
python3 test/cli.py "$(cabal list-bin exe:infera)"
python3 -m unittest discover -s test -p '*bench_harness_test.py'
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
timings; see [benchmark results and scope](docs/performance/README.md). Timing thresholds
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
compiled opaque control (combined and arithmetic/once/negation/conditional splits),
core reverse/loop/Fibonacci/queens workloads and the 16x16 minefield acceptance grid. Reference and
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

`bench/runtime-compare.py` compares the explicit bytecode backend with installed
SWI and Scryer on equivalent, independently checked control and core workloads.
Pass the built `machine-cache` pathname with `--infera-runner`, and optional
`--swipl`/`--scryer` paths. Loading, startup and one checked warmup are outside
timing; every timed query drains and validates its result. Increase `--batch`
when millisecond clock resolution is too coarse. Scryer reports loaded CPU
only; the runner leaves loaded wall time unavailable. The bytecode default
requires roughly 2× or better than at least one engine across representative
workloads, alongside the roadmap's correctness and residency gates.

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

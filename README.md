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
```

`check` resolves imports and checks undefined predicates, call arities,
declarations without matching clauses, and literal arguments that conflict
with every declared signature. Singleton variables, conflicting flags, and
unreachable clause heads produce warnings. Errors exit 1; warnings alone exit
0. Checks do not execute inline queries or prove runtime mode/determinism
contracts. Dynamic call targets remain runtime checks.

JSON output is an array of `{file, severity, code, message, range}` objects on
stdout. Ranges use zero-based lines and UTF-16 character offsets, with an
exclusive end. Semantic ranges cover the containing clause, declaration or
query; parse errors identify the offending position. Imported diagnostics
retain their own source file. Human-readable diagnostics go to stderr.

`--stdin FILE` checks an unsaved buffer without writing `FILE`; its path supplies
the import context and diagnostic identity. Optional `--buffer SOURCE SNAPSHOT`
arguments supply unsaved dependency snapshots, preserving each original source
path. These checks use the same parser, import resolver and diagnostics as disk
checks.

REPL: clauses end with `.`, queries with `?`.  Commands: `:load <file>`,
`:reload`, `:sig [pred]` (declared and inferred signatures), `:preds`, `:quit`.

```
cabal run infera -- examples/stdlib.nprolog
```

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
* **Cut** is implemented with barrier markers in the lazy answer stream; it is
  transparent through `,` `;` `->` and local inside `call`, `not`, `once`,
  `findall`.
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

```
cd lsp && npm install && npm run install-extension
```

## Roadmap

The resolution core is a lazy-list interpreter limited to 100 000 nested
activations. [docs/engine-roadmap.md](docs/engine-roadmap.md) is the plan
for replacing it: first an explicit abstract machine (trail, choice-point
stack, last-call optimisation, tracing hooks), then bytecode compilation.
`bench/run.sh` runs checked engine benchmarks. Earlier relative-speed numbers
from the unchecked harness are historical observations, not validated baselines.
The roadmap records a fresh local baseline with checked warmups and samples.

## Layout

```
src/Infera/Syntax.hs    terms, declarations, parser, printer
src/Infera/Unify.hs     substitutions, unification, renaming
src/Infera/Machine/Heap.hs isolated heap/trail and immutable snapshots for the engine roadmap
src/Infera/Arith.hs     numeric evaluation
src/Infera/CLP.hs       domains, linear constraints, propagation
src/Infera/Program.hs   predicate table, indexes, signatures, flags
src/Infera/Infer.hs     sort / mode / determinism / recursion analysis
src/Infera/Diagnostic.hs source-aware compiler diagnostics and JSON output
src/Infera/Engine.hs    resolution, cut, tabling, labeling, answers
src/Infera/Module.hs    neoprolog.conf and imports
src/Infera/Repl.hs      interactive loop
test/InferaTest.hs      hedgehog test suite
test/CorrectnessTest.hs generated correctness tests with independent models
test/InferenceTest.hs   inferred pruning compared with unpruned execution
test/MachineHeapTest.hs heap unification, rollback and snapshots compared with the reference
examples/               stdlib, v2_decls, v2_clp, v2_tabling, breadboard (CLP placer), jumpman (one rule set: verify / solve / play / generate), ...
Formula/infera.rb       Homebrew formula
bench/                  engine benchmarks (infera vs swipl vs scryer)
docs/engine-roadmap.md  plan for the abstract machine and bytecode engine
lsp/                    VS Code extension and language server
```

## Validation

CI builds and tests on Linux and macOS with GHC 9.8.2 and Node 22. It runs the
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

The first [engine roadmap](docs/engine-roadmap.md) foundation adds an isolated
paged heap and trail with immutable copy-on-write snapshots. Five generated
properties run 300 cases each against the existing unifier, checking term
round trips, ordered binding attempts, nested rollback, independent resumed
branches and allocations after checkpoints. Fixed cases cover occurs checks,
atomic failure, variable scope, typed scalars, NaN, signed zero, stale handles
and heap/trail page growth. The production resolver is unchanged; control,
CLP/table integration and collection are later milestones.

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

Failures print a seed and shrink path. To replay a counterexample, open
`cabal repl infera-test` and call `replay "PROPERTY NAME" (Seed VALUE GAMMA)
"SHRINK PATH"` with the values from the failure report. Replay is an interactive
debugging aid; use `cabal test` for the suite's pass/fail exit status.

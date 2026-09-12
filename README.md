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
```

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

Builtins: `true fail not once call phrase findall forall write writeln nl`,
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
| flags | `table notable index noindex` |

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
  the sorts of called predicates, iterated to a fixpoint.
* **Modes**: `<=` when a clause needs the argument ground before anything could
  bind it; `=>` when every clause leaves it ground.
* **Determinism**: `semidet` when clauses are pairwise exclusive (distinct
  principal functors, complementary guards such as `A >= B` / `B > A`, or a
  literal against a guard like `0` / `N > 0`, or cuts) and every body is at
  most semidet.  The exclusivity may depend on some arguments being ground;
  those positions are recorded and checked at call time.

Inferred signatures are advisory: they never raise errors.  The engine only
uses an inferred `semidet` to drop choice points, and only when the recorded
positions are ground in the actual call.  Everything else falls back to plain
backtracking.

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
* Output (`write`, `nl`) is collected per answer and printed with it.

## CLP(Z)

```prolog
X in 1..9            # also [X, Y] in 0..sup ; inf / sup for open bounds
A #= B  A #!= B  A #< B  A #> B  A #<= B  A #>= B
all_different Xs
label Xs             # enumerate, smallest domain first
```

Interval domains with holes and bounds propagation for linear constraints;
non-linear constraints wait until they become linear or ground.  Residual
domains and constraints are shown in answers (`X in 4..5`, `X + Y #= 10`).
See `examples/v2_clp.nprolog` (SEND + MORE = MONEY, N-queens).

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
declaration problems, singleton variables, plus the real parser's errors
via `infera check <file>` when the binary is installed).

```
cd lsp && npm install && npm run install-extension
```

## Layout

```
src/Infera/Syntax.hs    terms, declarations, parser, printer
src/Infera/Unify.hs     substitutions, unification, renaming
src/Infera/Arith.hs     numeric evaluation
src/Infera/CLP.hs       domains, linear constraints, propagation
src/Infera/Program.hs   predicate table, indexes, signatures, flags
src/Infera/Infer.hs     sort / mode / determinism / recursion analysis
src/Infera/Engine.hs    resolution, cut, tabling, labeling, answers
src/Infera/Module.hs    neoprolog.conf and imports
src/Infera/Repl.hs      interactive loop
test/InferaTest.hs      hedgehog test suite
examples/               stdlib, v2_decls, v2_clp, v2_tabling, breadboard (CLP placer), ...
Formula/infera.rb       Homebrew formula
lsp/                    VS Code extension and language server
```

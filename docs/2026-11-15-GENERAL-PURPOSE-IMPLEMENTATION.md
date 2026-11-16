# General-purpose implementation

15 November 2026. Local implementation of roadmap Steps 2–5. This page
records actual interfaces and conservative fallbacks. Qualification remaining
below is separate from feature implementation.

## Standard modules

Modules in `std/` are Infera source with explicit conservative declarations.
Their source is embedded at build time, so an installed binary needs neither
a checkout nor registered hashes. `std/list`, `std/order` and `std/aggregate`
are loaded implicitly. `<- noprelude.` disables that default; explicit
`<- import "std/assoc".` still loads the requested module and its dependencies.
Each module loads once. User clauses replace the entire library predicate of
the same name and arity, including its declarations. Builtins keep precedence.
Library names are unqualified; registered hash imports retain their existing
qualification. `clause` can inspect library implementations.

The modules provide the roadmap's list/higher-order operations, ordering and
pairs, grouped/existential aggregation, AVL associations, string operations,
DCG helpers, coroutine suspension and effect entry points. Pairs use
`pair Key Value`. `sort Field Order List Sorted` takes field 0 for the whole
term, otherwise a 1-based compound argument; orders are `lt`, `lte`, `gt`,
`gte`. Strict orders remove equal keys; inclusive orders preserve duplicates
stably. Numeric representations use Step 1's order (integers before floats).

Sorting and grouped collection use private native primitives behind ordinary,
shadowable library wrappers. `bagof` and `setof` group free goal variables;
`Variable ^ Goal` excludes an existential variable. Empty groups fail.
`aggregate_all` supports count, sum, max, min, bag and set; count/sum yield
zero for an empty search and min/max fail.

`std/assoc` uses height-balanced AVL trees and persistent updates. Repeated
keys in `list_to_assoc` keep the last value. `std/str` adds split, join, trim,
sub_str and character-code lists over the existing string builtins.
`std/os` adds an explicit-seed LCG; `random_seed` itself is an effect.

`examples/stdlib.nprolog` is now a thin import example. The earlier source
is retained as `test/fixtures/legacy-stdlib.nprolog` for its inference and
bytecode regression checks.

## Entry points, worlds and faults

```
infera run FILE [ARGUMENTS...]
```

Run mode does not execute inline queries or preload their literal file paths.
It calls `main Args` as an effect grammar, passing strings in Args. Declare
`main : io.` and write its clauses with `->`. `io` implies unsafe permission
and deterministic execution. The world is hidden by the grammar translation;
manually expanded clauses remain subject to static and runtime checks.
Conditional DCG translation now keeps its final state unification inside the
committed then branch, fixing the earlier wrapping of if-then-else.

The runtime owns a current world generation. Every external operation checks
and consumes it exactly once, and requires a fresh output world. Reusing a
world, retaining a pure alternative across an effect, closing a handle twice,
or failing after an irreversible effect is a fault. Pure conditions and
`once` may search internally. Static checking rejects nonlinear chains and
effects in collecting/negating scopes; runtime checks cover dynamic calls
and search choices that cannot be established statically.

Run exit statuses are 0 for success, 1 for ordinary main/parse failure, 2 for
a fault, or the status supplied to halt. Fault reports include the error,
goal and available source-located IO activation frames. A resource bracket
closes all owned handles on every outcome. Faults cannot be caught by Infera
code. The existing pure Search API still represents errors as SearchItems.

Inline queries can use surface effect sequences directly, for example:

```prolog
> open (string "abc") read (ok H), read_line H R, close H?
> say (fmt "~w~n" [hello])?
```

Each query owns its handles. The pure engine and its retained search streams
never perform external IO. The explicit effect runner uses the same parsed
clauses, unification, pure resolver, text grammars and source metadata.

## Handles and operations

Addresses: process streams `stdin/stdout/stderr`, `file Path`, `string Text`,
`tcp Host Port`, `listen Port`, `listen Host Port`, `unix Path`,
`listen (unix Path)`, and `udp Port`. Modes are read, write, append, update,
or `binary Mode`. Process streams are borrowed and cannot be closed.
Strings normally contain initial input; opening `string Variable` for writing
binds Variable to the collected text on close.

Operations below omit the hidden world pair:

| Operation | Result |
| --- | --- |
| `open Address Mode R` | `ok H` or `err Reason` |
| `read_line H R` | `ok String`, eof or err; newline is consumed |
| `read_chars H N R` | up to N characters, eof or err |
| `read_bytes H N R` | up to N bytes as integer list, eof or err |
| `write H String R`, `write_bytes H Bytes R` | ok or err |
| `say Grammar [R]`, `say_to H Grammar [R]` | render a text grammar; optional explicit result |
| `phrase_from H Grammar` | parse a prefix, leaving remaining input available |
| `phrase_from_file Grammar Path` | runtime path, complete-file parse and automatic close |
| `close H` | close an owned handle |
| `accept Listener R` | ok connection handle or err |
| `wait Handles Milliseconds Ready` | list of handles ready to read, including EOF |
| `send_to H (udp Host Port) Bytes R` | ok or err |
| `recv_from H N R` | ok `(packet Peer Bytes)` or err |
| `handle_address H Address` | actual socket address, including assigned port 0 |

The optional-result say forms are conveniences: an unchecked output error
faults with an instruction to use the result-bearing form. To recover from
an expected missing file, use open and inspect its result. Successful writes
flush their handle. Text encoding is UTF-8; byte lists contain 0–255.
Known errors map to enoent, eacces, eexist, econnrefused, eaddrinuse,
etimedout or eof; remaining platform errors map to eio.

`getenv Name R`, `now T`, `monotonic T`, `sleep Milliseconds`, `random_seed S`,
`list_dir Path R`, `stat Path R`, `remove Path R`, `rename A B R`,
`make_dir Path R` and `halt N` are effect operations. Wall time is fractional
POSIX seconds; monotonic time is integer nanoseconds. Stat returns
`ok (stat file Bytes)` or `ok (stat directory 0)`.

The handle parser interprets DCG clauses against an input cursor. Matching
another terminal asks the stream for one character; alternatives reuse cached
read-ahead. Direct reads share that cursor, so failed lookahead does not lose
input. Successful prefix parsing discards consumed cache entries. An eos
nonterminal requests EOF; without eos a socket parser can return while its
peer stays open. Parsing has a per-invocation resolution budget. This runner
currently uses depth-first grammar interpretation rather than native tabling.

## Attributes and coroutines

`put_attr V Module Value`, `get_attr V Module Value` and `del_attr V Module`
operate on a persistent, branch-local map. A binding queues the affected
modules' `attr_unify_hook Value Other` calls at the next goal boundary,
after the complete head has unified. Hook failure rejects that branch,
including its bindings and attribute changes. Unbound aliases are passed to
the hook so each domain can merge its own attributes.

`copy_term` now copies user attributes and their sharing. `copy_term_nat`
copies only structure. Neither copies native CLP(Z) domains. Attribute goals
are produced through `Module:attribute_goals V` grammars and only reachable
residuals are displayed. Native CLP remains separate as planned.

`std/coroutine` implements dif, freeze, when and frozen. Suspensions have
private identities so aliasing and re-watching do not register a task twice.
When supports nonvar, ground, conjunction and disjunction. Frozen returns a
list of residual when goals. With this module loaded, != uses the library
dif implementation. The Boolean attribute domain and watched-literal SAT
example exercise composition and binding failure.

Queries that use attributes conservatively use the persistent interpreter
for their entire search, so JIT/native bindings cannot skip hooks. Tabled
calls involving attributed variables and attributed answers use plain
resolution. Native checkpoint/port-trace APIs are not an attributed-variable
execution backend; native per-kernel attribute bailout is future optimization.

## Validation and remaining qualification

`test/general_purpose.py` supplies independently computed list/order/map,
aggregation and SAT expectations, plus real file, string, stdin, socket,
readiness and fault/exit-status tests. `test/example_programs.py` includes
the new pure examples. Both support all four JIT/stream configurations.
The Haskell suite adds complete-head hook timing, table fallback and retained
answer checks. CI runs the new acceptance script on Linux and macOS.

The existing edited Minesweeper example is preserved. Its legacy tests reject
inline queries; use the committed fixture in an isolated validation directory
to separate that pre-existing edit from this implementation.

Local validation (macOS arm64, GHC 9.8.2):

- 475 Haskell checks passed with the committed Minesweeper fixture in an
  isolated directory. The working-tree edit was not changed.
- 261 general-purpose acceptance cases passed in each of the four JIT/stream
  configurations, including real TCP, UDP and Unix traffic, two-client wait,
  fault cleanup, non-ground aggregation sharing and dynamic attribute calls.
- 21 example programs and 56 independently checked example queries passed in
  each configuration.
- CLI acceptance passed; all 61 language-server tests passed with the real
  compiler (none skipped).
- Checking all shipped standard sources reports no warnings or errors.

Remaining qualification: Linux CI has not been executed locally; the library's
2x native-performance admission target has not been established; not every
platform-specific error mapping is induced by the tests. The JSON and Lisp
examples are small language implementations, not a claim of full standards
conformance. Full native attributed-variable tracing and common CLP/attribute
residual plumbing remain future work.

## 2026-11-16: pure goals of `infera run` on the Core engine

The effect runner solved every pure prefix, if-then-else condition and text
grammar with the reference resolver. Under `infera run`, nrev30 × 3000 took
8.28 s against 0.03 s as an inline query, and the deriv loop 6.19 s against
0.40 s. `Runtime.pureSearch` now turns the walked goals into a query over
their free variables, solves it with `Core.solveQueryOrFallback` (and so the
JIT), and unifies each answer's bindings back into the runner's state, with
the answer's own fresh variables renamed above `ssFresh`.

The reference resolver still runs a search when the program uses attributes
or dynamic predicates, or when the state or an answer carries domains,
constraints, attributes, residual goals or dynamic facts. An answer that
cannot cross the boundary sends the whole search to the reference resolver,
skipping the answers already delivered. In programs without attributes the
per-goal attribute boundary is skipped.

Measured on an Apple M4, whole process, warm: nrev30 × 30000 takes 0.17 s
under `infera run` against 0.19 s inline, and the deriv loop × 3000 0.47 s
against 0.40 s.

`examples/lisp.nprolog` now declares `<- notable.`. Its symbol tokenizer is
ambiguous, so `expr`, which is tabled automatically, has exponentially many
parses. A tabled call collects them all before `once` takes the first, so
`(plus 2 (times 3 4))` took 34 s on the Core and over 100 s on the earlier
machine; the reference resolver had hidden this. Untabled, it takes 0.05 s.
Automatic tabling of ambiguous grammars under `once` remains a trap worth a
diagnostic.

The Minesweeper properties load the example without its inline query, as the
Breadboard properties do, so the Haskell suite passes with the shipped file.

## 2026-11-16: open items from the audit

All measurements below are on an Apple M4: whole process, warm, medians of
three runs. The first run after a rebuild pays about 0.6 s of cold start and
is discarded.

### `wait` blocks in one poll

`wait Handles Milliseconds Ready` no longer polls every 1 ms.

- Input already buffered is ready at once: a parser's read-ahead, an
  in-memory string, or a handle's buffer.
- Otherwise a single `poll()` over every descriptor blocks until one is
  readable or the timeout passes (`infera_poll_many`).
- When something is buffered, the remaining handles are still polled
  without blocking. Every ready handle is reported, in the order given, so a
  listener listed first is seen alongside a client's data.
- A negative timeout waits until a handle is ready.

A 2 s idle wait now uses 0.01 s of CPU.

`close` always succeeds, as documented. A write that failed (to a peer that
has gone) left its data buffered, and the later `close` raised the same error
as a fault; closing now drops it.

### No resolution budget in the handle parser

`phrase_from` faulted after 100,000 resolutions per parse: a total count,
not a depth, so a 300 KB file could not be parsed. The budget is gone. A
looping input grammar now loops, as untabled left recursion does anywhere
else.

`phrase_from_file`, which parses a complete file, now reads the file and runs
`phrase` on the Core instead of the incremental parser. Parsing 300,000
characters takes 0.08 s. The incremental parser, still used by streaming
`phrase_from` on sockets and stdin, needs about 2.6 KB per character, which
is open work.

### Grammars are not tabled by default

Every recursive DCG rule was tabled by default. The structural-recursion test
looked only at head patterns, and a DCG rule consumes input with a body goal
`S0 = [c | S1]`. A tabled call computes every answer before returning one, so
grammars became quadratic (a 4,000-character file took 16 s) or exponential
under `once` (the Lisp example's ambiguous tokenizer).

`structurallyRecursive` now follows body unifications with a head argument,
and covers every predicate on a cycle, not only direct self-calls. A grammar
whose recursion follows consumed input is untabled. A left-recursive rule
passes `S0` unchanged and stays tabled, so it still terminates. The
`<- notable.` added to `lisp.nprolog` on 2026-11-15 is removed again.

### Examples

- **`regex.nprolog`** keeps the backtracking matcher as the specification and
  adds Thompson compilation to an NFA, run as a set-of-states machine by a
  grammar. `test/example_programs.py` compares both on 12 generated
  expressions against Python's `re.fullmatch`, on every string of length up to
  4 over {a, b}.
- **`prolog_in_infera.nprolog`** parses Prolog clause syntax with variables and
  compound terms (built with `univ`) and interprets it with unification,
  backtracking and cut. Clauses are renamed with `copy_term`. Cut is built from
  if-then-else, not the engine's own cut: a clause with a cut proves its head
  and the goals before the cut as a condition. Atoms take their own clause
  because `univ` builds only compounds, and object programs cannot use `nil`
  and `cons`, which are Infera's list constructors.
- **`lisp.nprolog`** adds closures, `lambda`, `let`, `define` across REPL lines
  (so definitions can recurse), `minus`, `lt` and `eq`, and printing of values.
  `session` runs a list of lines as a pure relation.
- **`chat.nprolog`** serves any number of clients until the last one leaves.

`std/dcg`'s `integer` and `number` take the longest numeral deterministically.
Before, `once` committed to `1` in `10`.

### The 2x gate (`bench/std-gate.py`)

The gate first exposed problems that made library code orders of magnitude
slower:

1. **Catch-all declarations.** Every library predicate was declared
   `nondet notable (any: <=>)...`. Declared signatures override inference, so
   the library lost inferred determinism, and declared nondet calls were
   quadratic: `numlist` with `sum_list` over 40,000 elements took 32 s. The
   modules now declare only `name : notable.`, and their signatures are
   inferred. A flags-only library declaration is shadowed by any user clause
   of that name, since it covers every arity.
2. **The declared-call return check.** A declared call stacked a return-check
   frame even when its signature constrained nothing, which blocked frame
   reuse and made `contDepth` walk the chain on every call. A declared nondet
   counter over 40,000 calls took 9.85 s and now takes 0.06 s.
   Signatures with real output checks still stack those frames (open).
3. **Leaf builtins.** Every result of a term-toolkit or string builtin was
   kept in the constraint store's substitution and re-diffed on each later
   call, so 8,000 `compare` calls took 3.86 s. With no constraints active, a
   leaf runs from an empty store and installs only its own bindings: 100,000
   calls take 0.17 s. A ground `compare` is now ordered on the Core with the
   toolkit's `compareTerms`, without the reference resolver.
4. **`call/N`.** A closure naming an ordinary, untabled, non-dynamic user
   predicate becomes the same `GCall` a static call compiles to, placed first
   in the caller's goal list. There is no export or compile per call, and the
   decision is cached per functor. `foldl` over 200,000 elements: 0.38 s to
   0.15 s.
5. **Library code.**
   - `length` counts with an accumulator; it hit the 100,000 depth limit on
     long lists.
   - `nth0`/`nth1` take a separate deterministic path for a bound index.
   - `bagof`/`setof` run over `findall` with variant grouping of witnesses,
     instead of the reference resolver.

Seconds of work after startup is subtracted. "Local" is the same algorithm
written in the program, and SWI-Prolog is 10.0.2.

| workload | std | local | SWI | std / SWI |
| --- | --- | --- | --- | --- |
| reverse 1000 x 2000 | 0.023 | 0.025 | 0.108 | 0.21 |
| sum_list 1e6 | 0.109 | 0.170 | 0.069 | 1.58 |
| length 1e6 | 0.116 | 0.167 | 0.049 | 2.34 |
| msort 200k | 0.739 | 0.731 | 0.115 | 6.45 |
| maplist 300k | 0.200 | 0.083 | 0.054 | 3.68 |
| foldl 1e6 | 0.454 | 0.165 | 0.117 | 3.89 |
| nth1 2000 x 2000 | 0.002 | 0.001 | 0.010 | 0.17 |
| assoc 50k put + get | 1.931 | - | 0.051 | 37.6 |
| setof 100k | 0.421 | - | 0.052 | 8.04 |
| aggregate_all count, between 1e6 | 0.357 | 0.002 | 0.045 | 7.93 |

Before these changes, `nth1` was 681x, `foldl` 13x, `assoc` 67x and `setof`
12x SWI-Prolog, and `sum_list`, `length` and `setof` timed out at these
sizes.

Workloads still outside the gate, and the change each one points to:

- **`msort`, `setof`.** Sorting exports the list to the reference resolver and
  back. Sort on Core heap words with the toolkit order.
- **`assoc`.** Inference cannot prove `put_assoc` deterministic: its clauses
  are exclusive on a bound (not ground) argument. Declaring it `semidet` was
  slower still, because declared calls carry their own cost. Inferring
  exclusivity on a bound principal functor would fix the library without
  declarations.
- **`aggregate_all count`.** It builds the list of solutions to count it. A
  counting form of `findall` would not.
- **`maplist`/`foldl`.** 2.4x the hand-written loop: the closure call still
  builds its goal per call.
- **`length`.** 2.3x.
- **Engine.** The engine-wide default resolution depth of 100,000
  (`INFERA_MAX_DEPTH`) is itself an arbitrary bound.

Run `python3 bench/std-gate.py "$(cabal list-bin exe:infera)"`.

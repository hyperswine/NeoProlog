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

# Infera as a general-purpose language

Date: 15 November 2026. Kind: design proposal. Status: proposed; nothing here
is implemented at `154eaa8` (2.5.0 + 4).

## Why

Infera is already good at search, constraints and tabled reasoning, and its
analysis, tooling and speed hold up against SWI-Prolog and Scryer (see
[COMPETITOR-BENCHMARKS](2026-11-09-COMPETITOR-BENCHMARKS.md)). It is not yet a
language you can write an ordinary self-contained program in. At `154eaa8`:

- There is no way to take a term apart or build one generically: no
  `functor`, `arg`, univ, `copy_term`, standard order or `clause`.
- There is no standard library that is loaded by default. `examples/stdlib.nprolog`
  is an example file, and there are no `sort`, `maplist`, `foldl`, `setof` or maps.
- IO is limited to the edges of an inline query. File paths must be string
  literals because the loader reads files up front. There are no argv, streams,
  sockets, exit status, clock or randomness.
- Runtime errors (`SolveError` in `src/Infera/Error.hs`) abort the query, and
  there is no defined program-level outcome beyond "exit nonzero".
- There are no attributed variables, so `dif`, `freeze` and new constraint
  domains cannot be written in Infera itself.

This page records the direction for closing those gaps and the rules that keep
the result small.

## Principles

1. **A small core that composes.** A feature belongs in the engine only if
   it cannot be written as a library over existing pieces. Everything else
   lives in `std/` modules written in Infera, with declarations.
2. **No exceptions.** There is no `catch`/`throw`. Every goal ends in exactly
   one of three ways:
   - **success**;
   - **failure**, which is ordinary logic and backtracks;
   - **a fault**: the program is wrong, the run stops gracefully with a report
     and an exit status, and a fault can never be caught.

   Conditions a correct program must expect (a missing file, a refused
   connection, malformed input) are **values**, never faults.
3. **Pure by default, effects at the edges.** Ordinary predicates stay pure
   relations. Text is produced and consumed by grammars (`emit`,
   `phrase_from_file`), as it is today. Interaction with the world is written
   as an explicit, linear sequence of effects (see [Effects](#effects)).
4. **One abstraction per concern:**
   - every external object is a **handle**;
   - every effect sequence is an **effect grammar**;
   - every extension of unification is an **attribute**.

   New capabilities are new instances of these, not new mechanisms.
5. **Everything is analysed.** Library predicates and builtins carry sort,
   mode and determinism declarations, so `infera check`, the language server
   and inference treat them the same as user code.

### Admission rule

A proposed builtin or library predicate is accepted only when it:

- can't be expressed as a library predicate over existing ones, if it is to be
  a builtin;
- fits one of the abstractions above rather than adding a parallel one;
- has a declaration, reference documentation, an example and an independent
  test, as the classic examples do in `test/example_programs.py`.

Explicitly out of scope, so the question is settled:

- exceptions and `catch`/`throw`;
- threads;
- global mutable variables (`nb_setval` and friends);
- spawning processes or shelling out;
- an FFI;
- ISO's stream-alias and `format/2` directive zoo (`fmt` plus grammars covers
  formatting);
- a second debugging print path (the tracer and effect grammars cover it).

Each can be reopened only by a dated page that shows why the existing
abstractions don't suffice.

## Step 0: arithmetic functors as data

The term toolkit depends on this being settled. Today ground arithmetic in a
call argument is evaluated before head matching, so `functor (plus 1 2) N A`
would see `3`. The same rule is why `deriv` with `plus`/`minus` gives 375
instead of 377 (issue #7, closed as documented behaviour plus the
`arith-functor-as-data` lint).

Proposal: evaluate an argument only where the callee expects a number. That
means a parameter whose declared or inferred sort is `int`, `float` or `num`,
plus the arithmetic contexts (`is`, comparisons, CLP operators). Arguments of
sort `any`, and every argument of the term toolkit and `std` term predicates,
receive the term unevaluated. `fact (N - 1) R` keeps working because
`fact`'s first argument is inferred numeric. `deriv (plus X Y) D` receives
the structure.

Acceptance:
- the deriv benchmark rows give 377 and 11,310,000;
- every example and parity query keeps its answers;
- the lint reports only the sites whose meaning still depends on evaluation.

## Step 1: the term toolkit (engine)

| predicate | meaning |
| --- | --- |
| `functor T Name Arity` | principal functor; builds a term of fresh arguments when `T` is unbound |
| `arg N T A` | the `N`th argument (1-based); enumerates `N` when unbound |
| `univ T L` | `T` as a list `[Name, A1, ..., An]` and back (ISO `=..`) |
| `copy_term T C` | a copy with fresh variables, copying attributes (Step 5) |
| `term_variables T Vs` | the variables of `T` in depth-first order |
| `compare Order A B` | standard order of terms; `Order` is `lt`, `eq` or `gt` |
| `clause H B` | clauses of a predicate visible to the caller, for meta-interpreters |

`clause` is the only new reflective capability. It sees predicates in the
caller's module and predicates its module exports. Builtins have no clauses
and fail, rather than fault, so a meta-interpreter can dispatch them to
`call`. `call/N` already exists in the core compiler.

Standard order extends the existing ordering of numbers, characters, strings
and atoms:

`Var < Number < Char < Atom < String < Compound`

Compounds compare by arity, then name, then arguments left to right.

Acceptance: generated tests against an independent Haskell model of each
predicate in every mode, through both the JIT and the interpreter.

## Step 2: the standard library

`std` is a set of modules shipped with the binary and imported by name rather
than by hash:

```prolog
<- import "std/list".
<- import "std/assoc".
```

A **prelude** made of the smallest broadly useful set (`std/list`, `std/order`,
`std/aggregate`) is imported implicitly unless a file says `<- noprelude.`.
Library names may be shadowed by user clauses; builtins still may not.

| module | contents |
| --- | --- |
| `std/list` | `length nth0 nth1 last append member memberchk reverse select permutation sum_list max_list min_list numlist between take drop zip exclude partition`, plus `maplist/2..5`, `foldl/4..6` and `include` over `call/N` |
| `std/order` | `msort sort/2 sort/4 predsort keysort`, `pairs_keys_values pairs_keys pairs_values` |
| `std/aggregate` | `bagof setof` with `^`, `aggregate_all (count / sum / max / min / bag / set)` |
| `std/assoc` | AVL maps: `empty_assoc put_assoc get_assoc list_to_assoc assoc_to_list assoc_to_keys assoc_to_values` |
| `std/str` | the existing `str_*` builtins re-exported, plus `split join trim sub_str str_code_list` written as grammars |
| `std/dcg` | `seq digits blank blanks whites string_without integer number eos rest` |
| `std/coroutine` | `dif freeze when frozen`, written over attributes (Step 5) |
| `std/io`, `std/net`, `std/os` | the effect library (Steps 3 and 4) |

Library code is written in Infera wherever the result is within 2× of a
native version on the existing benchmarks. Only `msort`/`sort` (over
`compare`) and `bagof`/`setof` (over the existing `findall` machinery) are
expected to need native support. `examples/stdlib.nprolog` becomes a thin
file that imports `std/list`, so the example keeps working.

Acceptance:
- every exported predicate has a declaration that `:sig` shows;
- `infera check` reports no warnings on `std/`;
- the generated tests compare each against an independent model.

## Step 3: faults, `main` and effects

### Faults

Every `SolveError` becomes a **fault**:

- instantiation, sort and mode errors;
- `DetError`;
- division by zero;
- unknown predicates reached through `call`;
- an unbounded labeling;
- the tabling depth bound.

A fault stops the run and prints a structured report to stderr: the kind, the
predicate, the source span, the frame stack the tracer already records, and
the goal. Open handles are closed, and the process exits with status **2**.
`infera check` keeps moving faults to load time wherever analysis can prove
them, and new diagnostics should prefer that over runtime checks.

Exit statuses:

| status | meaning |
| --- | --- |
| 0 | `main` succeeded, or `halt 0` |
| 1 | `main` failed, or a halt the program chose (`halt N` for N ≥ 1) |
| 2 | a fault |

### `main` and `infera run`

```
infera run prog.nprolog arg1 arg2
```

This loads the program, runs no inline queries, and calls `main Args` with the
argument strings as an effect grammar (below). Inline queries stay what they
are today: REPL and documentation entry points.

### Effects

An **effect grammar** is a DCG whose hidden state pair is the world instead of
a character list. The DCG translation is unchanged: two extra arguments,
`W0` and `W`. What is new is that the analyser enforces three rules on any
predicate declared `io`:

1. **The world is linear.** Each world value is used once, so no effect can
   be repeated or backtracked into.
2. **No backtracking across an effect.** An `io` predicate is `det`. Pure
   goals in `{ }` and if-then-else conditions may backtrack internally, but
   nothing may leave a choice point after an effect. A violation is a load-time
   error where analysis can prove it and a fault otherwise.
3. **Effects only in `io` predicates.** Effects may appear only in `io`
   predicates and inline queries. `io` implies `unsafe`; `unsafe` alone keeps
   its current meaning (cut, dynamic facts).

```prolog
main : io.
main [Path] ->
  open (file Path) read R,
  ( { R = ok H } ->
      phrase_from H (lines Ls),
      { length Ls N },
      say (fmt "~d lines~n" [N]),
      close H
  ; { R = err Why } ->
      say_to stderr (fmt "cannot open ~s: ~w~n" [Path, Why]),
      halt 1
  ).
main _ -> say_to stderr "usage: count FILE\n", halt 1.
```

- `say NT` and `say_to H NT` emit the text described by the text grammar
  `NT`, so `emit` becomes `say` at stdout.
- Pure text grammars (`report Rows -> ...`) are unchanged and are what effect
  grammars print. A report written today becomes printable from `main` with
  no edits.

**Logging from pure code** is a writer, also written as a DCG. A pure
predicate that wants to report progress takes an event-list pair and pushes
events with the library nonterminal `note`:

```prolog
solve P S -> note (trying P), { step P P1 }, solve P1 S.
```

The edge prints the list with `say_to stderr (events Es)`. Logging stays
pure, testable and visible in the predicate's arity. When the logging
predicate also parses text, `std/dcg` provides `with_events` to thread both
states, so a program never needs a second print path.

**Reading lazily.** `phrase_from H NT` parses a handle's contents as a lazy
list, read on demand, so it works on stdin and sockets as well as files.
`phrase_from_file NT "path"` remains, as `open`, `phrase_from` and `close`
under the hood, and no longer requires a literal path.

Acceptance:
- every current example and inline query runs unchanged;
- `infera run` programs have tests for each exit status;
- the analyser rejects a generated corpus of non-linear and backtracking
  effect grammars;
- `test/cli.py` covers fault reports and that no handle is left open after a
  fault.

## Step 4: handles, files, sockets and the OS

Every external object is opened from an **address term** and used through the
same operations:

| address | object |
| --- | --- |
| `stdin` `stdout` `stderr` | the process streams, always open |
| `file Path` | a file; `Mode` is `read`, `write`, `append` or `update` |
| `string S` | an in-memory text, for tests and pure round trips |
| `tcp Host Port` | a client connection |
| `listen Port` / `listen Host Port` | a listening socket; `accept L R` yields a connection handle |
| `udp Port` | a datagram socket (`send_to`, `recv_from`) |
| `unix Path` | a Unix-domain socket |

| operation (effect grammar) | result |
| --- | --- |
| `open Address Mode R` | `ok H` or `err Reason` |
| `read_line H R` `read_chars H N R` `read_bytes H N R` | `ok Data`, `eof` or `err Reason` |
| `write H Text`, `write_bytes H Bs` | `ok` or `err Reason` |
| `say_to H NT` | `ok` or `err Reason` |
| `phrase_from H NT` | the lazy parse; a parse failure is ordinary failure |
| `close H` | always succeeds; closing twice is a fault |
| `wait Hs Timeout Ready` | the handles ready to read; one loop serves many connections without threads |

Reasons are atoms from one table (`enoent eacces econnrefused etimedout
eaddrinuse ...`). Encoding is UTF-8 by default; `binary` mode gives byte lists.

`std/os` holds the remaining primitives. Each is an effect grammar, because
each observes or changes the world:

- `getenv Name R`
- `now T` (wall clock) and `monotonic T`
- `sleep Ms`
- `random_seed S`. Randomness itself is a pure library over an explicit seed,
  so search stays reproducible.
- `list_dir Path R`, `stat Path R`, `remove Path R`, `rename A B R`, `make_dir Path R`
- `halt N`

Process spawning stays out (see the admission rule).

Acceptance:
- loopback tests for `tcp`, `udp` and `unix`, run in CI on Linux and macOS;
- `wait` serves concurrent clients in a test;
- every `err` reason is reachable in a test;
- the `string` address round-trips every grammar in the examples.

## Step 5: attributed variables (engine)

The interface follows SWI-Prolog's, keyed by module:

| predicate | meaning |
| --- | --- |
| `put_attr V Module Value` | set `V`'s attribute for `Module`; trailed, undone on backtracking |
| `get_attr V Module Value` | read it; fails when absent |
| `del_attr V Module` | remove it |
| `Module:attr_unify_hook Value Other` | called after `V` is bound to `Other`; failure undoes the binding |
| `Module:attribute_goals V` | a grammar for the residual goals shown in answers |

Engine points:
- **Binding an attributed variable** queues its hooks, and they run before the
  next goal, after head unification as a whole, so a hook sees the complete
  head.
- **The JIT** bails to the interpreter when a kernel would bind an attributed
  variable, as it does today for constrained variables.
- **Tabling** never tables a call involving an attributed variable, as for
  CLP variables today.
- **`copy_term`** copies attributes. `copy_term_nat` (in `std/coroutine`)
  does not.

`dif`, `freeze` and `when` move to `std/coroutine` on this interface. `!=`
stays the operator for `dif`. CLP(Z) stays native for speed. Its residual
display and wakeups should eventually go through `attribute_goals` and the hook
queue, so that a library domain (Booleans, finite sets) composes with it
instead of being a second mechanism.

Acceptance:
- `dif`, `freeze` and `when` written in Infera pass parity against the
  current `!=` and an independent model;
- a CLP(B)-style Boolean domain written purely in Infera solves the existing
  generated SAT cases.

## Examples to add

Each example is one self-contained file that runs as `infera run FILE` or
through its inline queries. None shells out, and each has an independent
check in `test/example_programs.py`. Several exercise every step at once, so
they double as acceptance tests for the design.

| file | program | exercises |
| --- | --- | --- |
| `meta_vanilla.nprolog` | the three-line `solve`, then depth-bounded, proof-tree and "why" explanations | `clause`, `call/N` |
| `meta_tabled.nprolog` | a meta-interpreter with its own variant table, checked against the engine's tabling | `clause`, `copy_term`, `std/assoc` |
| `meta_cost.nprolog` | an interpreter that counts inferences and enforces a budget | `clause`, failure as budget exhaustion |
| `prolog_in_infera.nprolog` | a parser and interpreter for a small Prolog subset, with cut | grammars, `univ`, `copy_term` |
| `lisp.nprolog` | a Scheme-like REPL reading stdin | lazy `phrase_from`, effect grammars |
| `stlc.nprolog` | type inference for simply typed lambda calculus with let-polymorphism | unification as inference, `term_variables` |
| `datalog.nprolog` | a semi-naive Datalog engine over `std/assoc` | aggregation, sorting |
| `dpll.nprolog` | a DPLL SAT solver with watched literals | attributed variables |
| `json.nprolog` | a JSON parser and printer as one reversible grammar | `std/dcg`, `string` handles |
| `regex.nprolog` | regular expressions compiled to an NFA and matched by a grammar | grammars over grammars |
| `wc.nprolog` | `wc`, reading files named in argv or stdin, with exit statuses | `main`, handles, `err` values |
| `http_hello.nprolog` | a minimal HTTP/1.1 server; the request is parsed by a grammar | `listen`, `accept`, `wait` |
| `chat.nprolog` | a line chat relay for many clients without threads | `wait`, linear effects |
| `log_report.nprolog` | a pure analyser that logs its progress, printed at the edge | the writer pattern, `note` |

## Order of work

1. Step 0 (arithmetic as data). This is small and unblocks Step 1.
2. Step 1 (term toolkit) and the meta-interpreter examples.
3. Step 2 (std and the prelude), moving `examples/stdlib.nprolog` onto it.
4. Step 3 (faults, `main`, effect grammars, `file`/`string`/process-stream
   handles), with `wc`, `lisp` and `log_report`.
5. Step 4 (sockets, `wait`, `std/os`), with the server examples.
6. Step 5 (attributes and `std/coroutine`), with `dpll`.

Steps 1–2 and Steps 3–4 are independent and can proceed in parallel. Step 5
depends only on Step 1 (`copy_term`).

## Open questions

- **Evaluating by sort (Step 0) under several declaration modes.** Should a
  predicate with several declaration modes evaluate per selected mode, or only
  when every mode agrees the argument is numeric? The proposal leans to "every
  mode agrees", which is conservative.
- **Visibility of `clause`.** Is "module-visible" enough, or should
  predicates opt in with a `public` flag to keep JIT-compiled predicates free of
  reflection? Reflection does not stop compilation, since clauses are retained
  for the interpreter anyway, but an opt-in flag documents intent.
- **The world token.** Should it be visible to the programmer, as a type the
  analyser checks, or hidden entirely by the `io` rule translation? Hidden is
  simpler; visible allows passing a world to a pure helper that only threads
  it.

# Total recursion inference

Date: 16 November 2026. Kind: design proposal. Status: not started. Base:
`22280a6`.

Infera should work out, for every recursive predicate, whether its recursion
always ends. It should show the result in the language server: what it proved
and why, or the exact call where the proof fails. Recursion the engine cannot
prove total must carry the `unsafe` marker, which today covers only effects.
The idea comes from FP-RISC's termination measures (`fprisc/compiler/Safety.hs`),
but differs in one respect: FP-RISC verifies a measure the programmer writes,
while Infera infers the measure. Infera's analysis also knows about modes,
tabling, nondeterminism and grammars, none of which FP-RISC has to handle.

## Why

- **No fixed limits any more.** Since `22280a6` nothing stops a runaway
  computation except memory. A non-tail runaway grows until it hits the heap
  limit and faults; a tail loop never faults and runs forever. Only a static
  check can warn about either, and it should warn while you type, not after a
  query hangs.
- **Today's analysis is only a tabling heuristic.** `predStructural` and
  `predCounterLoop` in `src/Infera/Infer.hs` exist to decide whether to table
  a predicate. If they fail, the predicate is quietly tabled; nobody is told,
  and nobody can ask why.
- **The gap is measurable.** A census of `examples/*.nprolog` at `22280a6`
  ran `inferProgram` on every file and classified each recursive predicate:

  | | structural | counter loop | not proven |
  |---|---|---|---|
  | user predicates | 245 | 13 | 66 |
  | prelude predicates | 35 | 0 | 4 (`take`, `drop`, `last`, `std_order_pred`) |

  The 66 unproven user predicates fall into a few groups, listed under
  [What the census shows](#what-the-census-shows). Most of them are total,
  and a better inference would prove it.

## What "total" means here

A predicate is **total in a mode** if every call in that mode has a finite
search tree: it gives finitely many answers, each after finitely many steps,
and then fails or stops. This is the logic-programming meaning of
termination. Determinism is a separate question: a total predicate can be
nondeterministic.

- **Untabled predicates.** The search tree is the ordinary depth-first
  tree. Every recursive call must lower a measure that cannot decrease
  forever.
- **Tabled predicates.** It is enough that the table can hold only finitely
  many distinct answers and calls. For example, transitive closure over
  finite facts is total under tabling even though it is left-recursive.
- **Modes.** A verdict depends on the call mode. `append` is total when its
  first or third argument is a proper list. It is not total when all three
  arguments are free, because it then enumerates lists forever. So the
  verdict is a condition on the arguments, not a yes or no.

## What the inference proves

Each predicate gets one verdict, computed per strongly connected component
of the call graph, bottom-up:

```
total when <condition>, by <reason>     -- proven
total by tabling over a finite domain   -- proven, tabled
not proven: <call site>, <why>          -- needs a fix or `unsafe`
reactive                                -- an io predicate; see below
```

Every proof is checked, never assumed. The inference generates candidate
measures, and a single verifier accepts or rejects each one; this is how
FP-RISC splits the work between the user and `measureCheckCG`. A poor
candidate can make a proof fail, but it can never make a wrong proof pass.

### 1. Norms

A norm is a size of a term:

- **list length**, which only means something when the list's spine is
  bound;
- **term size**, the number of constructors;
- **integer value**, which only means something with a floor taken from the
  guards.

The first two are rigid when the argument is bound in its call mode: an input
argument, or an argument that the groundness inference marks as bound at
that call.

### 2. Measures

A measure is a combination of norms over the argument positions. It must
decrease at every recursive call in the SCC, and it must be bounded below at
every call. The candidates are tried cheapest first:

- **A single position, structurally.** This is today's rule. The argument at
  the call is a proper subterm of the head argument, following body
  unifications through `unify`.
- **A single position, by norm.** The argument at the call is built, but it
  is smaller. In `last [_, Y | Ys] X <- last [Y | Ys] X`, the call passes
  `[Y | Ys]`, whose length is one less than `[_, Y | Ys]`. Structural descent
  misses this because `[Y | Ys]` is not a variable from the head. The same
  rule covers `increasing [A, B | T] <- … increasing [B | T]`.
- **A single integer position, linearly.** At each call the integer drops
  by at least 1, the head or guards give it a floor, and the calls need not
  be in tail position. For example, `factorial N R <- N > 0,
  factorial (N - 1) R2, …` passes `N - 1` in an evaluated argument position,
  and the guard `N > 0` gives the floor.
- **A guard difference.** Counting upwards has no floor of its own, but the
  guard supplies one: `board_rows … Row` under `{ Row <= 5 }`, called with
  `Row + 1`, decreases `5 - Row`. Candidates come from the comparison guards
  in the clause: `Lo <= Hi` or `Lo < Hi` gives `Hi - Lo`, and `X <= c`
  gives `c - X`.
- **A sum of positions.** A merge recursion such as `merge [X | Xs] [Y | Ys]`
  shrinks a different argument at different calls. Together the two
  arguments decrease at every call.
- **Lexicographic order.** Every call either decreases the first component,
  or leaves it equal and decreases the second (Ackermann, nested loops).
- **SCC-wide.** In a mutually recursive group such as `even`/`odd`, one
  measure is evaluated across the whole group, as FP-RISC does.

The set of positions a measure uses becomes the verdict's condition. If
`append`'s first argument decreases in one proof and its third argument in
another, the verdict is "total when argument 1 or argument 3 is a proper
list".

### 3. Size relations through callees

Many recursions shrink their input inside another predicate:

- `digits -> digit, digits`: `digit` consumes one character, so the state
  passed on is shorter.
- `place Free … <- select Q Free Rest, …, place Rest …` in queens.

The same bottom-up pass records a **size relation** for each predicate and
mode: for a pair of positions (in, out), whether the out argument's norm is
`<`, `≤` or unrelated to the in argument's norm.

- `digit S0 S1` gets `|S1| < |S0|`;
- `select _ Xs Ys` gets `|Ys| < |Xs|`;
- `append Xs Ys Zs` gets `|Xs| ≤ |Zs|` and `|Ys| ≤ |Zs|`.

These relations are a small fixpoint per SCC over the lattice
{`<`, `≤`, unknown}. They are not polyhedra, so they stay cheap. Builtins
and std leaves get hand-written relations. With these relations a measure
can decrease through a chain of body goals, not only at the call itself.
This is what turns grammar recursion over consumed input into a proof,
including grammars that consume through other nonterminals. Today that
works only when the terminal is in the same rule.

### 4. Tabling over a finite domain

A tabled predicate is total when:

- every answer argument is ground;
- every argument value comes from a finite set: constants in the program,
  answers of total predicates over a finite domain, or finite builtins such
  as `between` with bound limits;
- no clause builds a new term or new number into an answer position.

That is the Datalog case: `path X Y <- path X Z, edge Z Y` over `edge`
facts, or `reachable` and `price_path` when the price is bounded.

### 5. Builtins and std

The verdicts for builtins are written by hand:

- `between`, `findall` and `aggregate_all` over a total goal, `member` on a
  proper list, `msort`, `nth0`/`nth1`, and labeling over finite CLP domains
  are total;
- `length` with a free list, `repeat`, and `call` on an unknown closure are
  not.

Higher-order calls whose closure is known statically (`maplist (eval_in G
Env) Args Vs`) count as calls to the closure's predicate. That is the same
resolution `directTarget` already does for `call/N`. With that edge, the
call graph also sees recursion through `maplist`, and `maplist` itself is
total when its list is proper and the closure is total.

## What stays unproven, and `unsafe`

Some recursion is genuinely partial: a Prolog interpreter (`solve`, `prove`),
a Lisp `eval_in`, a fixpoint that saturates until nothing changes
(`saturate`), an infinite generator (`nat`). No inference proves these, and
none should.

**Proposal: `unsafe` means "the checker does not vouch for this predicate".**
A predicate needs it for either of two reasons: it has effects on the
database (today's rule), or its recursion is not proven total. That keeps a
single opt-out marker, as FP-RISC has, instead of adding a second flag.

- **Transitive.** If a predicate calls an `unsafe` predicate in a mode that
  is not proven total, it must be `unsafe` too, just as effects are
  transitive in `src/Infera/Purity.hs` today.
- **Exempt.** Queries and directives stay exempt, since they are the
  program's entry points.
- **Hover gives the reason.** The marker doesn't record which reason applies;
  the hover reports it ("unsafe: effects", "unsafe: recursion not proven
  total", or both).
- **Unneeded markers.** An `unsafe` marker on a predicate that has no effects
  and whose recursion is proven gets a hint suggesting the marker be
  removed. That is FP-RISC's "declared unsafe but the analysis finds it safe".
  It is a hint, not an error: the inference will get stronger over time, and
  each improvement should not break code that compiled before.

**What `unsafe` loosens.** Marking a predicate `unsafe` for partiality also
allows it to have effects. That is the price of having one marker. A
predicate that is only partial can still be checked for effects, and the
hover shows that it has none.

**Severity.** Today `unsafe-call` for effects is an error that stops loading
(`Module.buildChecked`). For partiality, start with a warning: unproven
recursion without `unsafe` is a `partial-recursion` warning in `infera check`
and the language server. The program still loads, so you can experiment in
the REPL. std and the examples must have no such warnings, and the census
check enforces that. Making it an error is a later decision, once the
inference has been tried on real programs.

**io predicates are reactive.** `io` predicates (effect grammars) such as
`serve`, `repl` and `wc_handle` loop for as long as the world feeds them
input; that is their job. Their verdict is `reactive`. They don't need
`unsafe`, but the pure goals they call inside `{ }` are checked normally.

**No measure declarations at first.** FP-RISC lets you write a measure for
the compiler to check. Infera starts without one: when inference fails on a
predicate you know is total, you either restructure it or mark it `unsafe`
and leave a comment. If real programs keep hitting the same miss, a measure
declaration can be added using the same verifier. It would be a declaration
flag, not new expression syntax.

## Interaction with tabling

The tabling default now asks "is this proven total without a table?" in
place of `predStructural`:

- **proven total by a measure:** not tabled by default, as structural
  predicates are today;
- **total only by tabling over a finite domain:** tabled;
- **not proven:** tabled, as today.

Untabling a nondeterministic predicate can make duplicate answers appear,
because tables answer with set semantics. Today's structural rule already
accepts that, and the new rule only untables more predicates of the same
kind. The example suites check every answer, which will show any change, and
any example that relies on deduplication gets an explicit `table`.

## Language server

The language server already shows compiler diagnostics from
`infera check --json --stdin` (`lsp/server/server.js`). The new parts are:

- **Diagnostic at the call that defeats the proof.**
  `partial-recursion` (warning) sits on the recursive call where every
  candidate fails. The message names the closest candidate and what it
  lacks:

  > `factorial (N - 1) R2`: argument 1 decreases by 1 but nothing bounds it
  > below; a guard such as `N > 0` before this call would prove the
  > recursion ends. Otherwise declare `factorial : unsafe.`

  The closest candidate is the one that failed at the fewest calls, with
  ties broken by order of cost.
- **Calls in a non-total mode.** `nonterminating-mode` (information) marks
  a call to a predicate that is total in some modes, made in a mode none of
  its proofs covers, such as `append X Y Z` with all three free inside a
  pure predicate. It is information only, because an intended generator is
  legitimate there.
- **Hover from the compiler.** Today the hover is built from the server's
  own source scan. `check --json` gains a `predicates` array with each
  predicate's verdict and condition, and the hover shows it:

  ```
  last/2: total when argument 1 is a proper list (length decreases)
  path/2: total by tabling over a finite domain
  solve/1: unsafe: recursion not proven total (call at line 41)
  ```
- **Quick fixes.** Add `name : unsafe.`; remove an unneeded `unsafe`; and,
  when the closest candidate failed only for lack of a floor, insert the
  suggested guard as a comment for the user to accept.

## Soundness notes

- **Finite terms.** The norms assume finite terms. Infera unifies with the
  occurs check (`src/Infera/Unify.hs`, and its compiled elision only where
  it is proven unnecessary), so there are no cyclic lists that never shrink.
  Any future rational-tree mode must disable these norms.
- **Pruning is harmless.** Cut, if-then-else and `once` only prune the
  search tree, so they never break a proof. Negation (`not G`) is total when
  `G` is.
- **Dynamic predicates are not proven.** `assert` can change their clauses
  at run time, and they already need `unsafe` for effects.
- **Attribute hooks.** Hooks that run user predicates when a variable is
  bound count as calls from the binding goal. CLP propagation ends because
  of its propagation budget, and labeling over finite domains is total.
- **Closures.** `call` and `maplist` with an unknown closure are calls to an
  unknown predicate, so a recursion that relies on them stays unproven.
  Today's call graph (`isUserCall` in `markGraphFacts`) sees only direct
  calls. Step 0 must close this gap before any verdict can be trusted.

## What the census shows

The 66 unproven user predicates, grouped by the rule that would prove them.
This grouping comes from their names and a sample read, not from running the
inference:

- **norm on a built argument:** `increasing`, `valid_path`, and std's
  `last`, `take`, `drop`;
- **linear integer measure, non-tail or counting up:** `factorial` (in two
  files), `fact`, `fib`, `even`/`odd`, the `board_rows`/`board_cells`
  family in `breadboard`, `rows`/`cells` in `jumpman`, `tile_rows` and
  `window_cols` in `minesweeper`, `header_cols`, `repeat_str`;
- **consumption through a callee:** `blanks` and `digits` in `std/dcg`
  (counted once per importing file), `place` in queens, `items` in lisp;
- **tabling over a finite domain:** the `path`/`reachable` predicates in
  seven files, and `price_path`;
- **partial, so `unsafe`:** the meta-interpreters (`solve`, `prove`,
  `try_rules`, `after_cut`, `bounded`, `cost`, `table_fix`), lisp's
  `eval_in`/`apply`, regex `match`/`closure`, `saturate`, `bfs`, `search`,
  stable matching's `propose`, `nat`;
- **reactive io:** `serve`, `repl`, `loop`, `wc_handle`.

## Steps

0. **Verdicts with no behaviour change.** Add `src/Infera/Termination.hs`
   with the verdict type, the SCC pass and the verifier. Re-express today's
   structural and counter-loop rules as its first candidates. Add
   statically known closures to the call graph. The census becomes a test:
   every predicate proven today must still be proven. Add the `check --json`
   `predicates` array and the hover.
1. **Norms and measures.** Built-argument norms, linear integer measures with
   guard floors, guard differences, sums, lexicographic order and SCC-wide
   measures.
2. **Size relations.** Per-mode size relations for user predicates, and
   hand-written relations for builtins and std. This step proves grammar
   recursion through nonterminals and the `select`-driven searches.
3. **Tabling and builtins.** Tabling over a finite domain, and the
   hand-written builtin verdicts.
4. **Diagnostics and `unsafe`.** The `partial-recursion` warning, the wider
   meaning of `unsafe` and its transitivity, the hint for unneeded markers,
   and the quick fixes. Switch the tabling default to the verdict. Clear the
   warnings in std and the examples: prove what is total, and mark what is
   partial `unsafe` with a comment saying why. Rerun every acceptance suite
   and the 2× gate, since the tabling default changes.
5. **Modes at call sites.** The `nonterminating-mode` information, using the
   groundness inference at each call.

Each step gets a dated section in this document when it lands.

## Open decisions

- **Severity:** a warning first, with an error later. Should
  `partial-recursion` become an error that stops loading, the way
  `unsafe-call` does?
- **Measure declarations:** leave them out until a real program needs one.
- **One marker:** should a predicate that is only partial keep its effect
  check by having two kinds of `unsafe`? This proposal says no, to keep a
  single marker.

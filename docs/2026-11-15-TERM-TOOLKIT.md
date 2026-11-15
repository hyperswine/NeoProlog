# Term toolkit

The Step 1 builtins operate on terms without arithmetic folding. They are
available in ordinary queries, through `call/N`, and in JIT-enabled programs.
The Core uses its existing trailed builtin boundary; these operations do not
have native JIT kernels.

| Declaration | Meaning |
| --- | --- |
| `functor : semidet (any: <=>) (atom: <=>) (int: <=>).` | Inspect a positive-arity non-list compound, or construct one when the term is free and name/arity are supplied. Constructed arguments are fresh and distinct. |
| `arg : nondet (int: <=>) (any: <=>) (any: <=>).` | Select a 1-based argument. A free index enumerates positions in ascending order, filtering by unification with the final argument. |
| `univ : semidet (any: <=>) (list any: <=>).` | Convert a compound to `[Name, Arg1, ...]`, or construct it from a proper list with a name and at least one argument. |
| `copy_term : semidet (any: <=>) (any: <=>).` | Copy a dereferenced term, freshening its variables while preserving repeated-variable sharing. Unify the result with the destination. |
| `term_variables : semidet (any: <=>) (list any: <=>).` | Collect distinct remaining variables in depth-first, left-to-right order. |
| `compare : semidet (atom: <=>) (any: <=>) (any: <=>).` | Unify the first argument with `lt`, `eq` or `gt`. |
| `clause : nondet (any: <=>) (any: <=>).` | Enumerate fresh head/body pairs of loaded user clauses and current branch-local asserted facts. |

These declarations are conservative relational signatures; `:sig NAME` shows
them. An incompatible output is ordinary failure.

## Structural traps

`functor`, `arg` and `univ` accept positive-arity non-list compounds only.
Lists, atomic/zero-arity terms, missing construction inputs, malformed or
improper construction lists, and invalid indexes raise a runtime `TypeError`.
`functor` construction is limited to 1,000,000 arguments, checked before host
allocation. An out-of-range `arg` index traps rather than silently failing.
The list used as `univ`'s representation is of course allowed.

These restrictions do not apply to `copy_term`, `term_variables` or `compare`:
they support lists, atomic terms and arbitrary nested structures.

## Identity, numeric order and constraints

Variables compare by runtime logical ID, which is only meaningful within the
current execution. The order is:

`Variable < Integer < Float < Character < Atom < String < Compound`.

Integers and floats are separate categories, so `compare lt 100 0.0` succeeds.
This avoids converting arbitrary integers to floating point. Float NaNs sort
after other floats and compare equal to each other. Compounds compare by
arity, name, then recursively by arguments. No comparison binds its operands.

`copy_term` copies structure and user attributes (Step 5), not the CLP store: copied unbound variables have
no constraints, and source constraints remain intact. Already bound values
are copied as values. `copy_term_nat` omits user attributes.

## Reflection

All loaded user predicates are visible, including imported/library predicates
under their existing qualified names. There is no export or public opt-in gate.
A free head enumerates predicates in program order and clauses in source order;
asserted facts follow static clauses (in key order, then assertion order).
Facts have body `true`; multi-goal bodies are right-associated conjunctions.
Head/body sharing is preserved and each answer has fresh clause variables.
Builtins have no user clauses and therefore fail reflection. Unloaded code is
not loaded by reflection. Assertions and retractions remain branch-local.

The current language represents `call true` differently from the literal goal
`true`; a meta-interpreter should handle the `true` body directly, as the
examples do. This change does not alter that pre-existing call convention.

## Examples and verification

- `examples/meta_vanilla.nprolog`: vanilla search, builtin leaves, depth bounds
  and proof trees (a structured explanation of why a goal succeeds).
- `examples/meta_cost.nprolog`: inference counting and budget exhaustion as
  ordinary failure.

Both interpret pure Horn clauses and conjunction; they do not claim to emulate
cut, effects or the engine's declaration commitments. The independent ground-variant table meta-interpreter now uses `std/assoc` in `examples/meta_tabled.nprolog`.

Generated Haskell tests construct expected functors, positions, variable
sharing, ordering and reflected answers independently of the implementation.
The parity fixture exercises the reference, earlier machine and Core,
including collection, retries and constrained inputs. The example runner
checks graph reachability, depth limits, proof trees and inference budgets
against a separate Python graph model in all four JIT/stream configurations.

For quick experiments:

```prolog
> functor (box a b) box 2?
> functor T box 2, arg 1 T a, arg 2 T b?
> univ T [box,a,b]?
> copy_term (box X X) (box A B), A = a, B = a, var X?
> term_variables (box X (box Y X)) [X,Y]?
> compare lt (box a) (box b)?
> clause (path a Y) Body?  # after loading meta_vanilla.nprolog
```

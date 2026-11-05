# Refactoring per-cycle unification and call work - 2026-11-05

Kind: design note and ranked plan. Follows
[`2026-11-04-UNIFICATION-HEAVY.md`](2026-11-04-UNIFICATION-HEAVY.md) and
[`2026-11-05-PER-CALL-WORK.md`](2026-11-05-PER-CALL-WORK.md) (`2d4e747`).

## Where per-cycle work still goes

After shallow backtracking (`shallowCandidates`), in-place structure building
(`buildStructure`) and narrowed clause selection (`pPrincipal`,
`pDecisionGroups`, `aiAll`), the remaining 3–4.5x gap against SWI-Prolog on
`zebra`, `deriv` and `primes` comes from six places where the engine still
repeats dynamic work on every reduction cycle instead of compiling it out at
load time or keeping it in flat state:

| Bottleneck | Module | Per-cycle cost today | Proposed refactor |
| --- | --- | --- | --- |
| Write-mode head matching | `Infera.Core.Run` (`streamHead`, `streamOperand`) | Escapes `ClauseStream` into recursive `unifyPattern`, `buildStructure` and `occursPattern` AST walks | Compile WAM write-mode instructions (`GET_STRUCT` jumping to a write-mode block on `tagRef`) with flattened structure templates and static occurs-check elision |
| Shallow candidate retry | `Infera.Core.Run` (`dispatchCandidates`, `shallowCandidates`) | Calls `saveArgs` up front; runs `allocFrame` before checking arg 0 on every failed candidate | Defer `saveArgs` until a head succeeds with remaining alternatives; test arg 0 before allocating or reuse a single pre-reserved frame slot block |
| Multi-pass clause selection | `Infera.Core.Compile` (`candidateClauses`) | Runs `principalKeys`, `decisionGroups`, `intersectCandidates` and `keepGuards` sequentially, re-dereferencing paths and recomputing shared guard expressions | Compile one load-time `DecisionTree` per predicate that switches once per inspected cell or guard expression |
| Boxed `Cont` chain & depth walk | `Infera.Core.Run` (`callPlain`, `contDepth`, `streamCode`) | Walks the `Cont` list on every call for `contDepth`; allocates boxed `CStream` and `CReturn` frames on the GHC heap | Maintain `rDEPTH` in a store register and move `CStream` / `CReturn` frames to an unboxed `IOUArray Int Int` control stack |
| Redundant base-pointer loads | `Infera.Core.Store`, `Infera.Core.Run` | `readCell`, `writeCell` and `deref` re-read `rCELLS` from `regs` on every word access during read-mode head matching and `unify` | Pass `Ptr Int` (`cellsPtr`) explicitly through non-allocating read-mode head matchers, `unify`, `equiv` and `occursIn` |
| Stream-to-JIT lowering | `Infera.Core.Jit` (`compileGeneralTailJit`) | Declines `zebra`, `deriv` and `primes` (`Nondet` or general compound arguments) | Lower `ClauseStream` and `DecisionTree` to `JitOp` for compound `GET_STRUCT` / `PUT_STRUCT`, shallow list scans (`mem/2`, `right_of/3`) and single-functor TRMC (`ins/4`, `remove/3`) |

---

## 1. Compiled write mode and static occurs-check elision in `ClauseStream`

### Current behaviour

`streamHead` and `streamOperand` in [`src/Infera/Core/Run.hs`](../src/Infera/Core/Run.hs)
only execute flat bytecode in read mode (`tag == tagStr`). Whenever
`opGetStruct`, `opGetListFirst`, `opUS` or `opUSF` meets an unbound variable
(`tag == tagRef`)—which happens on every output argument in `deriv`
(`d (times U V) X (add (times DU V) (times U DV))`) and tree insertion
(`ins/4`)—execution leaves the stream for the tree interpreter:

```haskell
| tag == tagRef -> do
    ok <- unifyPattern m base (streamSidePattern stream entry) arg
    if ok then streamHead m stream base after else pure streamFailed
```

That fallback walks the `Pattern` tree twice per unbound structure argument:

1. `buildStructure` / `fillArguments` traverses the `[Pattern]` tree, calling
   `reserveCells` separately for the parent structure and each nested
   sub-structure (three separate `reserveCells` calls for
   `add (times DU V) (times U DV)`).
2. `occursPattern` traverses the same `[Pattern]` tree again to check every
   `PSlot` and `PWord` against `valOf d` (6.5 M calls in `deriv`).
3. In body goals, `streamStructure` (`opPutStruct` / `opPushStruct`) calls
   `groundNowWord` on each pushed argument, re-reading functor words from the
   heap even when groundness is statically known or tracked in a bitmask.

### Refactor

1. **Inline write-mode stream blocks.** Replace the `SRefPattern` side-table
   escape in `opGetStruct` / `opGetListFirst` / `opUS` / `opUSF` with a
   compiled write-mode instruction span (or flat template offset) in
   `csCode`. When `tag == tagStr` with a matching functor, `opGetStruct` falls
   through to the read-mode `opU*` instructions and jumps to `after`; when
   `tag == tagRef`, it jumps to `writePc`.
2. **Single-reservation flattened compound templates.** A static nested
   `PStruct` tree of total size $M$ cells in a head or body can be flattened
   at compile time in [`src/Infera/Core/Compile.hs`](../src/Infera/Core/Compile.hs)
   into one contiguous allocation of $M$ cells (`reserveCells s M`), with
   internal child `STR` pointers computed as `strWord (baseAddr + relOffset)`.
   A single linear pass fills functor words, `PFirst` self-references, `PSlot`
   values and internal `STR` links.
3. **Static occurs-check elision.** A `PFirst` variable or constant in a newly
   constructed term can never contain the target `REF` cell. At compile time,
   collect the exact list of pre-existing `PSlot` offsets inside each head
   `PStruct`:
   - When that list is empty (e.g. `d (add U V) X (add DU DV)`), emit no
     occurs check at all—binding `valOf d` to the built structure is
     unconditionally acyclic.
   - When the list is non-empty (e.g. `V` in `add (times DU V) (times U DV)`),
     emit `opOccursSlot off` only for the unique repeated slots before
     allocating or binding the structure.

---

## 2. Deferred `saveArgs` and late frame allocation in `shallowCandidates`

### Current behaviour

In `dispatchCandidates` and `shallowCandidates`
([`src/Infera/Core/Run.hs`](../src/Infera/Core/Run.hs)):

1. `dispatchCandidates` calls `saved <- saveArgs s (pArity predicate)` *before*
   trying candidate 0. If all candidates except the last fail in their head,
   `shallowCandidates` drops `saved` via `setHeapTop s saved`, having paid to
   copy `argRegs` to the heap for nothing.
2. Head matching (`streamHead` and `matchHead`) only *reads* `argRegs`
   (`readArg`); it never writes to `argRegs` (`opArgPrep` and `opPut*` are
   body instructions that run only after `streamHead` succeeds).
3. Inside `shallowCandidates`, every candidate calls
   `base <- allocFrame s (clVars clause) (clInitSlots clause)` *before*
   `matchClauseHead`. In `zebra`, `mem (h red english _ _ _) Hs` tests five
   houses where four fail on the first or second field of `h/5`, allocating a
   frame and writing `markerWord` on each failed clause before testing arg 0.

### Refactor

1. **Move `saveArgs` into the head-match success branch.** Do not call
   `saveArgs` on entry to `dispatchCandidates`. In `shallowCandidates`, when
   candidate `k` (with `k + 1 < numElements ordinals`) succeeds in
   `matchClauseHead`:
   - If the head match allocated no heap cells and bound nothing (`H == h0` and
     `TR == tr0`), call `saved <- saveArgs s arity` and push the choice point
     with `hMark = saved + arity`.
   - Or reserve the `arity` save slots at `h0` without copying (`rH = h0 + arity`),
     and copy `argRegs` into `[h0 .. h0 + arity - 1]` only when a non-final
     candidate's head succeeds! That keeps `saved` below any heap cells built
     by the winning head while avoiding the `argRegs` copy when candidates fail
     down to the last clause.
2. **Hoist frame reservation across shallow retries.** Pre-compute
   `maxVars = maximum (map clVars clauses)` on `Pred`. Before entering
   `shallowCandidates`, run a single `ensureCells s (h0 + arity + maxVars + 1)`
   so individual candidate retries neither check capacity nor re-read `rCAP`,
   and only initialize `clInitSlots` once arg 0's outer tag/functor check
   passes (or inline `opGetFirst` / `opGetConst` / `opGetStruct` preamble
   before writing `markerWord`).

---

## 3. Single-pass compiled `DecisionTree` for clause selection

### Current behaviour

`candidateClauses` in [`src/Infera/Core/Compile.hs`](../src/Infera/Core/Compile.hs)
runs up to three separate passes on every indexed call:

1. `principalKeys` walks `pPrincipal`, dereferencing each selective argument
   and calling `intersectCandidates` (which scans both `UArray Int Int`
   ordinal vectors twice: once to count matches, once to build a list and
   allocate a new `UArray` when the subset is strictly smaller).
2. `decisionGroups` walks `pDecisionGroups`, re-dereferencing the root
   argument and calling `argumentAtPath` for each nested path, followed by
   further `intersectCandidates` calls.
3. `keepGuards` iterates over the surviving ordinals, calling `guardHolds` ->
   `guardInt` -> `argumentAtPath` for each clause. In `remove/3`
   (`0 is I % P` vs `X is I % P, X != 0`), both clauses evaluate `I % P` and
   dereference `arg 1 -> child 0` independently. In `d/3`, clauses 8 and 9
   (`d X X 1` and `d C X 0`) are open on arg 0, so every call to `d/3` gets a
   3-clause `Candidates` array from `principalKeys` and runs `decisionGroups`
   and `shallowCandidates`.

### Refactor

Compile `pIndex`, `pDecisions` and `pIntGuards` once at load time into a
single decision tree per predicate:

```haskell
data DecisionTree
  = DTLeaf !Candidates
  | DTSwitchArg !Int !(IM.IntMap DecisionTree) !(Map.Map Key DecisionTree) !DecisionTree
  | DTSwitchPath !Int ![Int] !(IM.IntMap DecisionTree) !DecisionTree
  | DTCompare !GuardValue !GuardValue !DecisionTree !DecisionTree !DecisionTree !DecisionTree
    -- ^ LT, EQ, GT (when both evaluate to immediate ints), and Miss (non-int/overflow)
```

- Every subset intersection is computed at **compile time** when building the
  tree; every `DTLeaf` holds a preallocated `Candidates` (`NoCandidate`,
  `OneCandidate !Int` or `Candidates !(UArray Int Int)`), eliminating runtime
  `intersectCandidates` and `keepGuards` allocation completely.
- Complementary arithmetic guards (`0 is I % P` vs `X is I % P, X != 0`, or
  `<` / `>` / repeated-head-variable `==` in `ins/4` and `look/3`) fuse into a
  single `DTCompare` node that evaluates `I % P` (or compares `K` with `K0`)
  **once** and branches directly to `OneCandidate ordinal`.

---

## 4. Unboxed control stack and register-tracked resolution depth

### Current behaviour

Every call in `callPlain` and `callDeclared`
([`src/Infera/Core/Run.hs`](../src/Infera/Core/Run.hs)) computes:

```haskell
let depth = contDepth cont + 1
if depth > maxResolutionDepth ...
```

where `contDepth` walks through any `CReturn` frames at the top of `cont`.
Furthermore:

- Every non-tail call in `streamCode` (`opCall`) allocates a 7-word boxed
  `CStream stream (pc + 3) base barrier depth next` constructor on the GHC
  heap.
- Every call that commits via `pSwitch` or declared determinism allocates a
  5-word boxed `CReturn entry guardBase check cont` constructor on the GHC
  heap (`callPlain` accounts for 41–50% of total GHC allocation in `zebra`,
  `deriv` and `primes`).

### Refactor

1. **Track depth as an unboxed parameter or register (`rDEPTH`).** Pass
   `!depth` directly into `callPredicate` / `callPlain` (incrementing on
   `opCall` / non-tail `GCall`, preserving on `opExecute` / tail `GCall`) so
   `contDepth` is never walked at call entry.
2. **Unboxed control stack (`csControl :: IOUArray Int Int`) or fused return
   fields in `CStream`.**
   - Short-term: embed `commitHeight :: !Int` (`-1` when none) directly in
     `CStream` (or carry the active commit height in an unboxed machine slot
     saved in `CStream`) so a committing call inside a streamed clause pushes
     no separate `CReturn` box when `check == Nothing`.
   - Medium-term: represent `CStream` and `CReturn` frames in a preallocated
     unboxed `IOUArray Int Int` stack (analogous to `Choices.csMarks`),
     reducing non-tail call continuation push/pop to unboxed array writes.

---

## 5. Hoist `cellsPtr` across non-allocating read-mode paths

### Current behaviour

In [`src/Infera/Core/Store.hs`](../src/Infera/Core/Store.hs), `readCell`,
`writeCell` and `deref` each read `rCELLS` from `regs s`:

```haskell
cellsPtr :: Store -> IO (Ptr Int)
cellsPtr s = intAsPtr <$> unsafeRead (regs s) rCELLS
```

During read-mode head matching (`streamHead` -> `streamOperands` ->
`streamOperand` -> `deref` / `readCell` / `writeFirst`), `unify`, `equiv` and
`occursIn`, **no cell allocation takes place**, so the pinned `cells` block
cannot grow and `cellsPtr` cannot change. Yet matching a 5-argument structure
`h/5` in `zebra` re-reads `rCELLS` from the `IOUArray` register file 15–20
times per head attempt.

### Refactor

Provide pointer-parameterised inner loops (`derefPtr :: Ptr Int -> Word' -> IO Word'`,
`unifyPtr :: Store -> Ptr Int -> Word' -> Word' -> IO Bool`,
`occursWalkPtr :: Store -> Ptr Int -> Int -> Word' -> IO Occ`, and
`streamHeadPtr` / `streamOperandsPtr`) that read `cells <- cellsPtr s` once at
entry and operate directly on `peekAt cells` / `pokeAt cells`, reloading
`cellsPtr s` only across a write-mode allocation that can call `growCells`.

---

## 6. Stream-and-decision JIT for unification-heavy predicates

As noted in [`2026-11-05-PER-CALL-WORK.md`](2026-11-05-PER-CALL-WORK.md), the
interpreter's irreducible floor in Haskell is ~4–5x SWI-Prolog per step due to
GHC function dispatch and tag switching. Two incremental extensions to
[`src/Infera/Core/Jit.hs`](../src/Infera/Core/Jit.hs) cover `zebra`, `primes`
and `bst` without requiring a full native WAM stack first:

1. **Shallow list-search kernels (`mem/2`, `right_of/3`, `sel/3`).** In
   `zebra`, most execution time is spent in `mem/2` and `right_of/3` scanning
   a 5-element list of `h/5` structures where 4 of the 5 elements fail
   shallowly in the head. A native kernel for predicates of the shape
   *base-head match on `[H | T]` + tail-recursive step on `T`* can run the
   entire shallow failure loop in native registers—unwinding trailed bindings
   from the pinned trail pointer when `H` fails to unify, and returning to
   Haskell with the remaining tail `T` in a single choice point only when an
   element succeeds.
2. **General single-functor TRMC (`ins/4`, `look/3`, `remove/3`).**
   `compileGeneralTailJit` already supports tail-recursion modulo cons
   (`ParamOutList`) over `cons/2` and `nil`. Generalising `ParamList` /
   `ParamOutList` to any single recursive functor (such as `t/4` in `bst`,
   where each recursive clause copies the untouched fields of `t K0 V0 L R`
   and sets the output register to the address of the recursive child slot
   `L1` or `R1`), together with `OpMod` in `compileBodyGoals`, admits
   `ins/4`, `look/3` and `remove/3` directly into native loop compilation.

---

## Suggested implementation order

1. **Deferred `saveArgs` + pointer-hoisted read-mode `streamHead` / `unify`**
   (small, self-contained in `Run.hs` and `Store.hs`; directly cuts per-attempt
   overhead in `zebra` and `deriv`).
2. **Compiled write mode + flattened structure templates + static occurs-check
   elision** in `Compile.hs` / `Ops.hs` / `Run.hs` (retires `unifyPattern` and
   `occursPattern` walks in `deriv` and `bst`).
3. **Single-pass `DecisionTree`** in `Compile.hs` (replaces `principalKeys` +
   `decisionGroups` + `keepGuards` + `intersectCandidates` in `deriv`,
   `primes` and `bst`).
4. **Explicit `depth` parameter + unboxed / fused `CStream` return frames** in
   `Run.hs` (eliminates the 41–50% GHC heap allocation in `callPlain`).
5. **General compound TRMC + shallow list-scan kernels** in `Jit.hs`.

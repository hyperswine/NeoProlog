# Pinned store blocks and register-cached base pointers - 2026-10-29 (report)

Step 1 of [WAM-JIT](2026-10-29-WAM-JIT.md), implemented the same day. The
cell, trail and bound-log arrays moved from `IORef (IOUArray Int Int)` to
pinned `ForeignPtr` blocks whose base addresses (and capacities) are cached
in unboxed register slots, so a cell access is one register read plus one
memory operation, hot loops hoist the base across iterations, and the
blocks have the stable addresses the JIT tier will need.

## What changed

[Store.hs](../src/Infera/Core/Store.hs):

* `Store` keeps `IORef`s holding the pinned `ForeignPtr`s (`cellsFP`,
  `trailFP`, `boundFP`) for ownership and growth only; the hot path never
  touches them. The boxed-constants table stays a boxed `IOArray`.
* New register slots: `rCELLS` (cells base, as an `Int`), `rTRAILB`,
  `rTRAILCAP`, `rBOUNDP`, `rBOUNDCAP`. The register file grew from 16 to 32
  entries; slots 0-15 are unchanged.
* `readCell`/`writeCell` read the base from the register slot and
  `peek`/`poke` one word; `deref`, `unwindTrail`, `allocCells`,
  `allocSlots`, `allocFrame`, `resetFrame`, `saveArgs`, `loadArgs`,
  `structureWord`, `structure2WithGround`, `pushTrail`, `recordBound` and
  `drainBound` fetch the base once per call instead of per element.
* Growth doubles into a new pinned block, copies the live prefix, and
  updates the `IORef` and both register slots together. The same 4x factor
  for cells and doubling for trail/bound as before.
* Exported `cellsPtr`, `trailPtr`, `boundPtr`, `peekAt`, `pokeAt` with the
  documented rule that a slot pointer is invalidated by any growth of that
  block.

[Run.hs](../src/Infera/Core/Run.hs): the six sites that reached into the
old record fields (minimize's trail scan, `checkInvariants`, and `collect`'s
root marking, pending-bound walk, slide, and trail compaction) use the new
pointers. Collection never grows a block, so it holds its pointers
throughout, as before.

No new dependency: the blocks are raw `mallocForeignPtrBytes`
allocations accessed through `Foreign.Storable`. A `Data.Vector` backing
would sit behind the same raw-pointer accessors, so it was left out rather
than added for its own sake.

## Correctness

The complete `infera-test` suite passes, including the `core-engine` parity
groups and every forced-collection group; the machine is byte-for-byte the
semantics it was before (same tags, same trail discipline, same collector).

## Measurements

Same host as the earlier reports, GHC 9.8.2, `-O1` library profile,
`bench/core-major --case C --batch 5 +RTS -T -RTS`, medians of five runs,
per-query CPU seconds. The baseline was re-measured with the two files
stashed rather than compared against the older batch-1 figures, so both
columns come from the same protocol.

| Case | Baseline ms | Now ms | Change | Per-query allocation |
| --- | ---: | ---: | ---: | ---: |
| core-nrev | 10.16 | 7.89 | -22% | 23.88 MB, unchanged |
| core-loop | 10.39 | 8.02 | -23% | 21.61 MB, unchanged |
| core-fib | 49.22 | 35.33 | -28% | 102.78 MB, unchanged |
| core-queens | 11.68 | 7.71 | -34% | 27.26 MB, unchanged |

GHC allocation per query is unchanged to within noise, as expected: the
change removes an indirection and enables base hoisting, it does not remove
allocations. The CPU gain is 22-34% across the four workloads. Day-to-day
drift on this machine was about 8% in earlier reports; the baseline and new
columns were interleaved within minutes of each other and the spreads
barely overlap (baseline nrev minimum 9.58 ms vs new-code maximum 9.10 ms).

## Notes for Step 2 and Step 3

* Pinning gives the JIT tier a stable heap address to hand to native code
  at call entry; growth between calls invalidates and is fine because a
  native span is leaf-per-call.
* The register-file slots 21-31 are free for JIT bookkeeping (for example a
  compiled-code cache pointer or fuel cell pointer) without growing it
  again.
* `INFERA_CORE_TRACE=1` invariant checking (`checkInvariants`) runs against
  the same pointers and passed on every trace-mode run of the suite.

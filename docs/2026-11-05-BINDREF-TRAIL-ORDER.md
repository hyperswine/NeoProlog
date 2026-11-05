# JBindRef: trail first, then write the cell

2026-11-05. Branch `fix/jit-bindref-trail-order` (off `main` at ae5fd44).

## The defect

The JIT IR op `JBindRef addr val bailoutLbl` binds `cells[addr] = val` and
trails the cell when it is older than the choice boundary (`addr < RHB`).
Both assemblers wrote the cell first and only then compared the trail top
with its capacity. On a full trail the op jumped to the bailout with the cell
written but not trailed. `invokeJitKernel` handles a bailout by unwinding the
trail to its entry mark and dropping the heap above the entry top, which does
not undo an untrailed binding. The old cell stayed bound, possibly to a
structure in the heap that had just been dropped.

It was found while building the list-search kernel (branch `perf/mem-kernel`,
docs/2026-11-05-SCAN-KERNEL.md): zebra failed at its 130th repetition, the
first time the trail filled between collections. That kernel works around it
by checking room before every bind (`roomFirst`).

## The fix

Both backends now emit, in order: compare `addr` with `RHB`; if trailing is
needed, load the trail capacity, branch to the bailout when the trail is
full, push `2*addr`, bump `RTR`; finally store the cell. The skip branch for
young cells lands on the store.

- AArch64 (`AsmA64.hs`): `cmp; b.ge +7; ldr cap; cmp; b.ge bail; lsl; str
  trail; add; str cell`. The old `replaceWord6` patch-up is gone: the `lsl`
  word is emitted in place.
- x86-64 (`AsmX64.hs`): the short `jge` skips the capacity check, its `jcc
  rel32` and the push, onto the 4-byte `mov [r14 + a*8], v`.

The scratch registers the push uses (x15/x16 on AArch64, r11 on x86-64) are
not the home of any IR register, so the value register survives until the
store.

## Was it reachable from the det kernels on main?

Not through any program, as far as the kernels go today. `invokeJitKernel`
declines unless 8 trail slots are free at entry (`entryTR + 8 > tCap`), and
every det kernel on `main` makes at most one trailed bind per call: the
caller's output variable, in the base clause or the first TRMC step. Cells a
kernel allocates sit above the entry heap top, which is the kernel's choice
boundary, so later binds in the same call are not trailed. A kernel that binds
more than 8 old cells per call (the scan kernel is the first) is what exposes
the order. The fix removes the trap for every kernel to come; the scan
kernel's `roomFirst` check becomes redundant once this lands under it.

## Tests

- `test/JitEncodingTest.hs`, new group `jit-native`: assembles a three-op
  unit with the host backend and runs it on hand-made state, over several
  address/value register pairs including spilled ones on x86-64. A bind on a
  full trail must return `jitBailout` with the cell untouched and `TR`
  unchanged; with room it trails `2*addr` then writes; above `HB` it writes
  without trailing. The full-trail case failed before the fix (cell = 99).
  It runs natively on AArch64 here and x86-64 on Linux CI; on other hosts it
  passes vacuously.
- `bindSkip` (x86-64 encodings, any host) now requires the op to end with the
  cell store and the short `jge` to land on it. It failed before the fix.
- `test/core/parity-jit.nprolog`: `bound_then_undone` binds a list of fresh
  variables through `sum_to` (a det kernel) under a choice point, fails back,
  and counts free variables; `bound_sum` keeps the bindings. Small sizes
  (300) there, because the reference engine is quadratic on this program
  (2000 variables: 20 s reference, 0.01 s core).
- `test/CoreTest.hs` `trail_fills_under_kernels`: the same queries at 6000 on
  the core engine alone, normally and with a collection limit of 1, against
  fixed answers. With `INFERA_JIT_XCHECK` 5992 of the 6000 `sum_to` calls ran
  natively; the other 8 were the entry guard declining near a full trail,
  which is why this case passes before the fix too (see above).

No measurements: this is a correctness fix.

## On main

Rebased onto `main` after the scan kernel merged. With `JBindRef` checking
room before the write, the scan kernel's own `roomFirst` check is redundant
and is removed; `test/core/parity-scan.nprolog`'s `fill 10000` (the zebra
failure in miniature) still passes, now through the op's own check.

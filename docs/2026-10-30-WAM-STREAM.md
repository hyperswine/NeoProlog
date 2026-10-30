# Load-time compilation and the clause instruction stream - 2026-10-30 (report)

Step 2 of [WAM-JIT](2026-10-29-WAM-JIT.md). Two halves landed:

* **Load-time compilation.** The intern tables became program-scoped, the
  compiled program became a shared image memoized on program identity, and
  `coreSupports` stopped building a machine to answer a yes/no question.
  This half has no semantic risk and removes the per-query compilation cost.
* **A flat instruction stream**, prototyped behind `INFERA_CORE_STREAM` and
  measured against the tree interpreter on the four standard workloads, as
  the plan requires. It is a clear win on the workload the plan exists for
  (reverse) and neutral on the others; the acceptance item it does **not**
  meet is GHC allocation on the tree path, and that is a driver-codegen
  effect rather than executed work. Details at
  [Open problems](#open-problems).

## Load-time compilation

The plan's prerequisites, with the corrections the implementation forced:

1. **The intern tables are program-scoped, and that includes the boxed
   constants.** `Symbols` now owns atoms, functors *and* the
   `IOArray Int Boxed` that `BOX` words index, because `constantWord` boxes
   every integer outside the 61-bit immediate range, every float and every
   string, and bakes the resulting index into `PWord`. A plan shared across
   queries whose `BOX` index meant one thing in the compiling store and
   something else in the next query's store would be a silently wrong
   constant. With the table in `Symbols`, `newStore` no longer allocates one,
   and `rBOX` became a counter beside the table instead of a store register
   (slot 4 of the register file is now unused). Interning grows the tables
   under one lock, because a store can now be built and run from more than
   one thread; the read paths take no lock.
2. **Compilation no longer needs a live store at all.** `Ctx` holds the
   program's `Symbols` instead of a `Store`, so `compileProgram` is pure with
   respect to query state. That is what makes `coreSupports` cheap.
3. **The memo is keyed on program identity, not a digest.** `P.Program` has
   no digest, and hashing `show program` would cost more than the compilation
   it saves. `programScope` keeps one entry holding
   `(StableName program, program, Symbols, ProgramImage)`; holding the
   `Program` in the entry is what makes identity a sound key, since the value
   cannot be collected and its address reused while the entry refers to it.
   `compileProgram` then assembles a per-query `CoreProgram` from the shared
   `ProgramImage` plus the query's own goals.
4. **`coreSupports` answers from the image.** It reads the program half from
   the memo, compiles only the query's goals, and starts no machine, so the
   double compilation on the fallback path is gone.

The memo was verified by counting: a benchmark that runs six queries against
one loaded program reports exactly one compilation. The cost it removes is the
one [PER-CALL-COSTS](2026-10-20-PER-CALL-COSTS.md) measured at about 0.09 ms
per query; measured here as a batch of queries against one program, the
earlier build compiled the whole program six times and this one compiles it
once, which moved the four standard workloads by 1-3% each - small, because
only the cheap workloads are close to that scale, but it is the whole of the
per-query compilation cost and not a fraction of it.

## The instruction stream

`Infera.Core.Ops` fixes the encoding; `Infera.Core.Compile` encodes each
clause at load; `Infera.Core.Run` interprets it. A stream is one `UArray Int
Int` per clause - an opcode word and its inline operands - plus a side table
of boxed values (`SRefCall` for a call target and its contract evidence,
`SRefEscape` for the goals that stay on the tree, `SRefPattern` for a
structure that has to be built rather than matched).

The fragment is:

| Group | Instructions |
| --- | --- |
| Head match | `GET_FIRST`, `GET_VAR`, `GET_CONST`, `GET_STRUCT`, `GET_LIST_FIRST`, and the `U_FIRST`/`U_VAR`/`U_CONST`/`U_STRUCT`/`U_LIST_FIRST` operands they carry |
| Argument construction | `PUT_*`, `PUSH_*` for the children of a nested structure, `ARG_PREP` |
| Control | `CALL`, `EXECUTE`, `PROCEED`, `CUT`, `FAIL`, `CHECK_BOUND`, `ESCAPED` |
| Unification | `DO_UNIFY` over a `PUT` pair |

Everything else - `or`, `if-then-else`, `not`, `once`, `findall`, `minimize`,
tabling, dynamic facts, leaf builtins, DCG goals - is `ESCAPED`: the VM hands
the **remaining `[Goal]` list** to `runGoals` with the same base, barrier,
depth and continuation, so no `Alt` or `Cont` constructor had to be
re-expressed and every clause still streams its head match.

Three implementation decisions worth recording:

* **`GOAL` was written, measured and removed.** Running a single-goal builtin
  (`is`, a comparison, a type check) as one instruction with the stream as its
  successor needs a fresh continuation and a side-table load, while the tree
  handles it in one `step'` branch. With arithmetic in the stream, `loop` and
  `fib` - the two arithmetic-heavy workloads - moved 10-30% the wrong way;
  with arithmetic escaping, they are within a few percent. The reason is
  structural: a flat stream removes *per-term* work (a list walk, a pattern
  tree walk), and `is`/`>` have none. Arithmetic in the stream belongs to
  fragment growth item 3, not to slice 0.
* **Argument construction uses the argument registers above the callee's
  arity as an operand stack**, which is what WAM uses the same registers for,
  so a nested structure costs `PUSH_*` operations and one `PUT_STRUCT` rather
  than a second register file. `ARG_PREP` sets the stack base once per call
  site.
* **A suspended stream keeps its whole activation block live in the
  collector.** Code is immutable and names slots by offset, so it cannot be
  detached into `PWord` operands the way a goal plan is. `CStream` therefore
  marks the block from its `markerWord` through `markerVars`, which keeps it
  contiguous through compaction (mark-compact preserves address order) and
  makes relocation a single forwarded base address. The predicted residency
  cost did not appear on the four standard workloads.

`INFERA_CORE_STREAM=0` runs the tree interpreter and is the escape hatch; the
default is the stream.

## Correctness

* `cabal test all` passes with the stream on and with it off. That includes
  every forced-collection group, the generated parity properties, CLP,
  tabling, tail-frame reuse and the slot/decision suites.
* `core-engine parity` over `test/core/*.nprolog` reports "all queries agree"
  in both modes, with and without `--gc-limit 1`.
* `core-engine parity` over `examples/facts`, `examples/facts2`,
  `examples/mathexpr` and `examples/v2_decls` agrees in both modes.
* The answers the benchmark verifies are checked against the reference oracle
  and an independent model in every run, and every reported number below is
  from a run whose `status` was `ok`.

## Measurements

Host as in the earlier reports (GHC 9.8.2, `aarch64-darwin`), library at the
project's `-O1` profile, `bench/core-major --case C --batch 5 +RTS -T -RTS`.
The two columns are the **same binary**, differing only in
`INFERA_CORE_STREAM`, because the machine drifted across this session - it is
shared, and its load average moved between 2 and 9 - so an across-build
comparison would not be trustworthy at this resolution.

| Case | Stream off | Stream on | Allocation | CPU (quiet host) |
| --- | ---: | ---: | ---: | ---: |
| core-nrev | 28.47 MB | 18.37 MB | -35% | -17% |
| core-loop | 29.46 MB | 29.46 MB | 0% | 0% |
| core-fib | 124.06 MB | 120.18 MB | -3% | ~0% |
| core-queens | 31.11 MB | 27.02 MB | -13% | -5% |

The allocation column is **exact**: it is identical to the byte across every
run of the same binary, so it is the reliable evidence here. The CPU column is
from a five-run median sequence taken while the host was quiet, with typical
per-run spreads of 5-8%; the same sequence repeated later at load average 9
could not resolve any CPU difference at all, so treat those percentages as
direction, not magnitude.

Reverse is the workload this plan exists for and it is the largest win: 35% of
the allocation and about 17% of the CPU. `nrev/2` and `app/3` are exactly head
matching plus structure construction, and the stream replaces a `matchHead`
list walk, a `unifyPattern`/`unifyCompound` dispatch and a
`buildArgs`/`buildArg`/`buildCompound` walk with a handful of instructions.

`loop` and `fib` are unchanged by construction, not by accident: see the
admissibility rule below. `queens` gains 13% of its allocation from `perm/2`,
`sel/3`, `safe/1` and `noatt/4`, whose heads are the only structure walking in
that workload.

### Admissibility: only stream where the stream removes work

The first version streamed every clause whose head was encodable, and `loop`
got slower: its body is `N > 0, N1 is N - 1, loop N1`, so the stream ran the
head match, hit `CHECK_BOUND` and escaped at the first goal - paying for the
dispatch and replacing nothing. `compileClause` now also requires that the
first goal the encoder would emit an instruction for is itself in the
fragment. A clause whose body escapes immediately is left entirely on the tree
interpreter, which is why `loop`'s allocation is identical in both columns
above rather than merely close. A fact still streams: its head match *is* the
work.

Two further refusals are per goal rather than per clause, and both are
correctness conditions rather than performance ones. An arithmetic argument
(`PArith`) is evaluated or built as data by a path the stream does not
implement, so a call or unification carrying one escapes. And the operand
stack is the argument registers above the callee's arity, so a call whose
patterns could push 1024 words is refused rather than allowed to run off the
end of the register file. The first of these is not hypothetical: an
intermediate version of the encoder replaced it with the size bound alone, so
every clause with an arithmetic argument became "encodable", emitted `FAIL`
for that argument, and failed silently. The minesweeper suite caught it in one
run, which is the argument for keeping the tree interpreter's whole suite as
the gate rather than a stream-specific sample.

## Open problems

**Allocation on the tree path.** With the stream compiled into the driver, a
run with `INFERA_CORE_STREAM=0` allocates 4.7-7.9 MB more per query than the
same query did before Step 2, and *with no stream compiled at all*
(`clStream = Nothing`) it allocates exactly the same 4.7-7.9 MB more. Removing
the interpreter's code from `Run.hs` restores the baseline to the byte
(23.789 MB for reverse, 21.535 MB for loop, the same figures the previous
report records). So the cost is not executed work: it tracks whether the
interpreter's code is present, and it is about one extra 8-9 word closure per
inference. It survives `-O2`, `-fmax-simplifier-iterations`, forcing
`INLINE` on the structure builders, moving the dispatch behind a `NOINLINE`
wrapper, and (tried and reverted) moving the interpreter into its own module
behind a record of driver primitives - that last one cost the stream 30% of
its speed through the record indirection, so it was reverted.

What is left is a GHC codegen question about this driver, not a semantic one,
and it is the first thing to resolve before the stream becomes the only
interpreter. Raising the profile does not answer it: at `-O2` both builds
allocate less, and the gap stays (24.03 MB against the pre-Step-2 build's
19.39 MB on reverse at `-O2`), while every number in the earlier reports would
become incomparable. Finding the lost optimisation is the work.

**Fragment growth.** In the plan's expected-value order, with the measured
correction that arithmetic is not worth its dispatch:

1. Structures as arguments (reverse/append already stream; this is about
   passing them to calls without an escape).
2. Multi-clause selection as a native jump table. Selection itself is
   untouched by this step and remains `candidateClauses`' allocation-free
   ordinal walk.
3. Single-goal builtins (`is`, comparisons, checks) as instructions - only
   once their dispatch is cheaper than a `step'` branch, which today it is
   not.
4. Control constructs (`or`, `if-then-else`, `once`, `not`) as instructions.
   Each needs an `Alt` variant pointing at a stream; `AltGoals`' age rule is
   the model.

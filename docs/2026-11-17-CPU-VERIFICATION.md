# Verifying the 8-bit CPU with Infera

Date: 17 November 2026. Executable example:
[`examples/8bitcpu.nprolog`](../examples/8bitcpu.nprolog).

Run the simulations, 20 finite proofs, three counterexamples and a backwards
ALU query:

```sh
infera examples/8bitcpu.nprolog
```

This demonstrates **exhaustive finite model checking**. A property is written
as a search for an input that violates it. If that finite search completes
without a counterexample, the property holds throughout its stated domain.
This is stronger than checking a few selected examples, but it is not a
proof of a physical CPU, an unbounded address space, or Infera's own soundness.
The model and the interpreter are part of the trusted base.

## A transition relation, not just a simulator

The state is `cpu PC A B Z C`: two byte registers, a zero flag and a carry
flag. PC is an integer address; it does **not** wrap at 256.

`execute Instruction Before After` defines one instruction independently of
memory. `rom Program PC Instruction` supplies named memories. `step Program
Before After` composes them, and `run Program Before Steps After` executes
exactly the supplied nonnegative integer number of steps. The original
`run Before Steps After` and `step Before After` arities select `addition`.
`trace Program Before Steps States` includes the initial state, so its list
has `Steps + 1` entries.

| instructions | result and flags |
|---|---|
| `lda I` | load `I mod 256` into A, update Z, clear C |
| `ldb I` | load B; preserve A and both flags |
| `add` | A becomes `(A+B) mod 256`; Z reports zero, C reports overflow |
| `sub` | A becomes wrapped `A-B`; update Z, clear C |
| `inc`, `dec` | wrapped increment/decrement; update Z; inc reports overflow, dec clears C |
| `mova` | copy B into A, update Z, clear C |
| `movb` | copy A into B; preserve both flags |
| `jmp`, `jz`, `jnz` | choose the next PC; preserve registers and flags |
| `nop` | advance PC; preserve registers and flags |
| `hlt` | leave the entire state unchanged |

Arithmetic inputs must be integers, and the verified register domains are
0 through 255. Invalid instructions and missing ROM addresses have no
transition. Subtraction deliberately does not expose a borrow flag.
`hlt` is an absorbing transition rather than a host-side stop command.

The expansion fixes a concrete bug in both CPU examples: `ldb` and `movb`
previously left the output zero flag anonymous. A free variable is not a
valid Boolean flag, and does not specify a deterministic machine state.
The new clauses preserve the input flag.

## Specify the ALU independently

The implementation uses integer arithmetic and modulo. Its specification
uses finite-domain constraints and a conservation law:

```prolog
alu_spec add A B R Z C <-
  [A,B,R] in 0..255, [Z,C] in 0..1,
  A + B #= R + 256 * C, reify (R #= 0) Z.
```

`A+B = R+256*C`, together with the byte and bit bounds, characterizes the
wrapped result and carry. Reification makes Z exactly the truth value of
`R=0`. Subtraction uses `R+B = A+256*Borrow`, with an existential Boolean
borrow; the CPU's exposed carry is still zero.

The specification also works backwards:

```prolog
> alu_spec add 255 B 0 1 1, label [B]?
B = 1
```

Here the result, zero flag and carry are known; the missing operand is
synthesized. `execute` itself uses `is`, so its arithmetic operands must be
known before execution. To search machine inputs, enumerate a finite domain
first rather than treating `is` as an inverse arithmetic solver.

## Prove a postcondition by excluding counterexamples

For addition, enumerate all 65,536 byte pairs, collect the complete answer
set, and reject anything other than one valid state satisfying the contract:

```prolog
counterexample add_contract (inputs A B got Answers) <-
  byte_value A, byte_value B, outcomes add (cpu 0 A B 0 0) Answers,
  not (Answers = [Next], one_valid Answers,
       Next = (cpu 1 R B Z C), alu_spec add A B R Z C).
```

The query `check add_contract Result` returns `Result = proved` when this
search is exhausted. A failure returns `refuted Witness`, including the
inputs and actual answers. `proof_suite Report` reports **every** registered
claim, including failures; it never silently omits unsuccessful proofs.
Unknown property names fail rather than returning `proved`.

The answer-set check matters. Writing only `execute ..., not Postcondition`
would overlook an input for which execution returned no answer. Likewise,
matching a free output flag against 0 could accidentally repair an incomplete
model while checking it. `one_valid` first requires a single, ground, valid
state; the frame properties use term identity rather than binding outputs.
The inverse checks require exactly one returned result as well.

## The 20 claims and their precise domains

A and B below range over all bytes unless stated otherwise. Register and
flag results are properties of the model, with no implicit assumptions about
real hardware. The input flag initialization is part of each contract.

| claim | domain and conclusion |
|---|---|
| `add_contract` | all 65,536 A/B pairs at PC=0, old Z=C=0; one valid next state, B preserved, PC advanced, ALU contract satisfied |
| `sub_contract` | the same domain for subtraction |
| `add_commutative` | all A/B pairs, old flags zero; result A and output flags commute; the entire CPU state does not, because B differs |
| `add_sub_inverse` | all A/B pairs; add then subtract restores A, with exactly one result; flags are not claimed to be inverses |
| `add_zero` | all A; adding zero preserves A and clears carry |
| `sub_self` | all A; subtracting A from itself gives zero with Z=1 and C=0 |
| `inc_contract` | all A, B=37, old flags zero; increment satisfies the addition-by-one contract |
| `dec_contract` | the same domain for subtraction by one |
| `inc_dec_inverse` | all A, B=37; increment then decrement restores A, including 255 |
| `dec_inc_inverse` | all A, B=37; decrement then increment restores A, including zero |
| `immediate_normalization` | every immediate from -256 through 511; three complete residue classes normalize into a byte with correct flags |
| `ldb_preserves` | all A/immediate byte pairs and all four Z/C combinations; old B=91, PC=0; only B and PC change |
| `movb_preserves` | all A/B pairs and all four Z/C combinations at PC=0; copy A into B and preserve flags |
| `nop_frame` | all A/B pairs and all four flag combinations at PC=0; only PC changes |
| `halt_frame` | all A/B pairs and all four flag combinations at PC=3; the complete state is preserved |
| `branch_contract` | all three branch forms, PCs/targets 0..7, all flags, A/B in {0,1,127,128,255}; exact branch destination and frame preservation |
| `transition_functional` | PCs 0..7, all flags, those five data representatives, every opcode, five load immediates and branch targets 0..7; exactly one ground valid next state |
| `countdown_rank` | all positive byte counters at PC=1, B=0, old flags zero; one three-instruction loop cycle decreases A by exactly one without leaving the byte domain |
| `countdown_all_inputs` | all 256 initial counter values from reset state; reach `cpu 4 0 0 1 0` in exactly `2+3*N` steps |
| `halt_absorbs` | the addition program's halted state, for every additional budget from 0 through 8; the state stays unchanged |

`transition_functional` and `branch_contract` explicitly use boundary data
representatives; they are not advertised as exhaustive over every register
combination. The ALU, frame and countdown domains in their own rows are
exhaustive. Combining finite claims is useful, but does not expand their
quantifiers automatically.

## Establish a ranking invariant for the countdown

The named program checks for zero **before** decrementing:

```text
0: lda N
1: jz 4
2: dec
3: jmp 1
4: hlt
```

At loop header PC=1, a positive A takes three instructions back to PC=1,
with A decreased by one. This is a nonnegative ranking function. Once A=0,
the zero flag causes the exit jump instead of wrapping to 255. The example
checks every positive byte header value and every complete initial run.
For N=2, the trace PCs are `0,1,2,3,1,2,3,1,4`.

The exact reach-halt budget is one load, N three-instruction cycles, and one
final taken zero jump: `2+3*N`. This includes N=0, which reaches halt in two
steps. The checker verifies the bounded traces; the ranking argument explains
why the bound is appropriate for all byte initial values.

A decreasing **simulation budget** alone proves that the simulator stops
working after that budget. It does not prove that the simulated program
halts. A program such as `jmp 0` can run for every finite budget. Reaching
the halt address and establishing the ranking invariant are separate claims.

## Make the verifier catch bugs

The example includes intentionally broken relations, without replacing the
correct CPU:

```prolog
> once (mutant_counterexample no_wrap Witness)?
Witness = input 255 got 256

> once (mutant_counterexample lost_carry Witness)?
Witness = inputs 1 255

> once (mutant_counterexample undefined_flag Witness)?
Witness = input 0
```

The first violates the byte bound. The second loses the carry in `1+255`.
The third reproduces the old free-zero-flag bug. These positive witnesses
show that the counterexample searches can actually find failures.

The regression runner goes further: it modifies the real `execute`/flag
rules, not just these demonstration mutants. It removes wrapping, deletes
addition, duplicates addition, loses carry, and leaves the load flag free.
The appropriate real proof must return `refuted` for all five mutations.
It also compares transitions against a separate Python implementation, so a
bug shared by a model predicate and its postcondition is less likely to hide.

```sh
python3 test/cpu_verification.py /path/to/infera --all-modes
```

## Limits and trust

These are completed finite searches, not proof certificates checked by a
small independent kernel. Their meaning depends on the encoded domains,
the instruction relation, arithmetic/CLP semantics and correct search
exhaustion. An error, interruption, or timeout is not a proof. Negation is
used only after the necessary input generators have supplied finite values.
The program runs untabled so duplicate transitions remain observable.

This model has no RAM, instruction encoding, interrupts, timing, undefined
hardware behavior or RTL. No result here establishes equivalence to a
physical implementation. General program termination, arbitrary PCs and
arbitrary-length temporal properties are outside these finite checks.

The few `unsafe` declarations acknowledge a conservative recursion-inference
gap: the checker cannot combine a ROM/state mode with the integer execution
budget for the whole verification dispatcher. They do not grant any proof;
the bounded domains and completed executions still have to be checked.


## Local validation

The acceptance runner passes in all four JIT/instruction-stream combinations.
In each mode it checks all 20 proof outcomes, rejects all five actual-rule
mutations, and compares 580,352 instruction transitions with the independent
Python model. That matrix includes both ALU operations over every byte pair
and all four incoming flag combinations, plus unary, immediate and branch
cases. It separately checks the named-program outcomes, all countdown initial
values, and flag preservation in the compact `my8bitcpu` companion.

The broader example runner passes 22 demonstrations in all four modes, and
the 54-file recursion census has no unacknowledged partial recursion. CI now
runs the CPU acceptance script; these recorded results are local, not an
observation of a completed remote CI run.

## Reusing the checks

Import `std/verify` explicitly. The CPU collects all successors with
`verify_outcomes Next (execute Op S Next) Answers`, then calls
`verify_one valid_state Answers`. The latter requires a singleton containing
a ground state before invoking the validator. A missing, duplicate or partly
unbound successor therefore fails this contract.

For a finite, pure generator of ground inputs, use
`verify_all Domain Violation Result`. The generator takes one argument.
The violation relation takes an input and a witness, succeeding when the
property fails. The result is `empty_domain`, `refuted Input Witness` for
the first failure in search order, or `proved` after exhausting the domain.
Both callbacks must terminate. The generator runs once to establish that
the domain is inhabited and again to search it.

In `examples/json_relation.nprolog`, run
`verify_all json_sample json_roundtrip_failure Result?` to generate text
and parse it back for each value in the sample. The witness includes the
generated texts and parsed values. A second check searches a small corpus
of malformed inputs for an unexpected successful parse.

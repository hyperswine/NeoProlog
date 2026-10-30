-- | Opcode words of a compiled clause stream.
--
-- A stream is one unboxed @Int@ array per clause: an opcode word followed by
-- that instruction's inline operands, laid out exactly as
-- [Compile](../src/Infera/Core/Compile.hs) emits them and as
-- [Run](../src/Infera/Core/Run.hs) decodes them. The encoding is deliberately
-- flat: a fetch is an indexed read, and an instruction never needs to look
-- anything up outside its operands except through the clause's side table of
-- boxed values (calls, escapes and single goals).
--
-- The instruction groups mirror the tree interpreter they shadow:
--
-- * @GET_*@ match one head argument, by argument position. A structure's
--   children are the following @UNIFY_*@ operands, in cell order.
-- * @PUT_*@ write one call argument register; @PUSH_*@ leave a value on the
--   operand stack the enclosing @PUT_STRUCT@ pops, which is the argument
--   registers above the callee's arity, as in WAM.
-- * @CALL@ continues in the stream and @EXECUTE@ in the caller's
--   continuation with the current activation offered for reuse, which is what
--   makes a trailing call a tail call.
-- * @ESCAPE@ and @GOAL@ are the two ways out of the fragment.
module Infera.Core.Ops
  ( -- * Control
    opProceed,
    opCheckBound,
    opCut,
    opFail,
    opCall,
    opExecute,
    opEscape,
    -- * Head matching
    opGetFirst,
    opGetVar,
    opGetConst,
    opGetStruct,
    opGetListFirst,
    opUF,
    opUV,
    opUC,
    opUS,
    opUSF,
    -- * Argument construction
    opArgPrep,
    opPutFirst,
    opPutVar,
    opPutConst,
    opPutStruct,
    opPushFirst,
    opPushVar,
    opPushConst,
    opPushStruct,
    opDoUnify,
  )
where

-- | The clause succeeded: continue with the clause's continuation.
opProceed :: Int
opProceed = 0

-- | Install any pending constraint binding, as @runGoals@ does between goals.
opCheckBound :: Int
opCheckBound = 1

-- | Cut to the clause's barrier.
opCut :: Int
opCut = 2

-- | Fail the clause.
opFail :: Int
opFail = 3

-- | @opCall side arity@: call, continue in the stream.
opCall :: Int
opCall = 4

-- | @opExecute side arity@: call in tail position, offer the frame for reuse.
opExecute :: Int
opExecute = 5

-- | @opEscape side@: run the remaining goals on the tree interpreter.
opEscape :: Int
opEscape = 6

-- | @opGetFirst arg off@: the argument is the first occurrence of a slot.
opGetFirst :: Int
opGetFirst = 7

-- | @opGetVar arg off@: unify the argument with a slot.
opGetVar :: Int
opGetVar = 8

-- | @opGetConst arg word@: unify the argument with a constant.
opGetConst :: Int
opGetConst = 9

-- | @opGetStruct arg side functor n next@: match a structure, @n@ operands
-- follow and @next@ is the offset after them.
opGetStruct :: Int
opGetStruct = 10

-- | @opGetListFirst arg side functor head tail@: a two-argument structure
-- whose arguments are both first occurrences, matched cell to cell.
opGetListFirst :: Int
opGetListFirst = 11

-- | @opUF off@: unify the operand with the first occurrence of a slot.
opUF :: Int
opUF = 12

-- | @opUV off@: unify the operand with a slot.
opUV :: Int
opUV = 13

-- | @opUC word@: unify the operand with a constant.
opUC :: Int
opUC = 14

-- | @opUS side functor n next@: unify the operand with a structure, @n@
-- operands follow and @next@ is the offset after them.
opUS :: Int
opUS = 15

-- | @opUSF side functor head tail next@: as @opGetListFirst@, as a unify
-- operand.
opUSF :: Int
opUSF = 16

-- | @opArgPrep arity@: the operand stack starts above the callee's arguments.
opArgPrep :: Int
opArgPrep = 17

-- | @opPutFirst arg off@: argument is the first occurrence of a slot.
opPutFirst :: Int
opPutFirst = 18

-- | @opPutVar arg off@: argument is the value of a slot.
opPutVar :: Int
opPutVar = 19

-- | @opPutConst arg word@: argument is a constant.
opPutConst :: Int
opPutConst = 20

-- | @opPutStruct arg functor n@: argument is a structure of @n@ pushed values.
opPutStruct :: Int
opPutStruct = 21

-- | @opPushFirst off@: push the first occurrence of a slot.
opPushFirst :: Int
opPushFirst = 22

-- | @opPushVar off@: push the value of a slot.
opPushVar :: Int
opPushVar = 23

-- | @opPushConst word@: push a constant.
opPushConst :: Int
opPushConst = 24

-- | @opPushStruct functor n@: push a structure of @n@ pushed values.
opPushStruct :: Int
opPushStruct = 25

-- | Unify the two argument registers a @PUT@ pair left in place.
opDoUnify :: Int
opDoUnify = 26

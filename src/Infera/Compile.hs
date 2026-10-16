-- | Clause allocation bytecode for first-order rules. Compilation preserves
-- source variable numbers and body order; activation adds its fresh-ID base
-- only when a 'UseVariable' instruction executes. No renamed 'Term' tree is
-- built by the VM.
--
-- Unsupported clauses retain the interpreted path. In particular, body cuts
-- must fall back even inside data: the interpreter's body renamer replaces
-- bare cuts recursively, rather than only when they are called.
module Infera.Compile
  ( Slot,
    Instruction (..),
    BodyCall (..),
    ClauseCode,
    codeVariableCount,
    codeSlotCount,
    codeInstructions,
    codeHead,
    codeBody,
    compileClause,
  )
where

import Infera.Syntax (Clause (..), Term (..), functorOf, termVarIds)

-- | Registers are local to one clause activation. Instructions define each
-- register exactly once, and compound children always name earlier registers.
type Slot = Int

data Instruction
  = UseVariable !Slot !Int
  | PutConstant !Slot !Term
  | PutCompound !Slot !String [Slot]
  deriving (Eq, Show)

-- | The original template is retained only for source lookup and tracing.
-- The key has the same representation as 'Infera.Error.PredKey'; compilation
-- depends on syntax alone and does not decide builtin precedence or lookup.
data BodyCall = BodyCall
  { bodySlot :: !Slot,
    bodyKey :: !(String, Int),
    bodyTemplate :: !Term
  }
  deriving (Eq, Show)

-- Keep both the constructor and record-update syntax private: an instruction
-- operand cannot refer forward, use an invalid local variable, or smuggle a
-- compound into PutConstant.
data ClauseCode = ClauseCode !Int !Int [Instruction] !Slot [BodyCall]
  deriving (Eq, Show)

codeVariableCount :: ClauseCode -> Int
codeVariableCount (ClauseCode count _ _ _ _) = count

codeSlotCount :: ClauseCode -> Int
codeSlotCount (ClauseCode _ count _ _ _) = count

codeInstructions :: ClauseCode -> [Instruction]
codeInstructions (ClauseCode _ _ instructions _ _) = instructions

codeHead :: ClauseCode -> Slot
codeHead (ClauseCode _ _ _ slot _) = slot

codeBody :: ClauseCode -> [BodyCall]
codeBody (ClauseCode _ _ _ _ body) = body

-- Reverse instructions make compilation linear in the source tree size.
data Builder = Builder !Int [Instruction]

-- | Compile facts and first-order bodies, preserving all scalar types and
-- nested data constructors. Ordinary builtins remain eligible; the machine
-- dispatches them through its existing builtin interface. Control and meta
-- calls, uncallable goals and malformed local IDs use the interpreter.
--
-- At least one fresh logical ID is reserved even for ground clauses, matching
-- the native interpreter's activation owner and fresh-counter convention.
compileClause :: Clause -> Maybe ClauseCode
compileClause clause
  | count < 0 || not (all validVariable variables) = Nothing
  | otherwise = do
      _ <- functorOf (clauseHead clause)
      if all firstOrderGoal (clauseBody clause) then pure () else Nothing
      (headSlot, afterHead) <- compileTerm (Builder 0 []) (clauseHead clause)
      (body, Builder slots instructions) <- compileBody afterHead (clauseBody clause)
      pure (ClauseCode (max 1 count) slots (reverse instructions) headSlot body)
  where
    count = clauseNVars clause
    variables = concatMap termVarIds (clauseHead clause : clauseBody clause)
    validVariable variable = variable >= 0 && variable < count

firstOrderGoal :: Term -> Bool
firstOrderGoal goal = case functorOf goal of
  Just (name, _) -> name `notElem` controlNames && withoutCuts goal
  Nothing -> False
  where
    controlNames =
      [ ",", ";", "->", "call", "once", "not", "findall", "forall",
        "minimize", "phrase", "emit", "phrase_from_file", "!", "$cut"
      ]
    withoutCuts (Atom "!") = False
    withoutCuts (Compound "$cut" _) = False
    withoutCuts (Compound _ arguments) = all withoutCuts arguments
    withoutCuts _ = True

compileBody :: Builder -> [Term] -> Maybe ([BodyCall], Builder)
compileBody builder [] = Just ([], builder)
compileBody builder (goal : rest) = do
  key <- functorOf goal
  (slot, next) <- compileTerm builder goal
  (calls, final) <- compileBody next rest
  pure (BodyCall slot key goal : calls, final)

compileTerm :: Builder -> Term -> Maybe (Slot, Builder)
compileTerm builder term = case term of
  Var variable -> emit builder (\slot -> UseVariable slot variable)
  Compound name arguments -> do
    (children, next) <- compileArguments builder arguments
    emit next (\slot -> PutCompound slot name children)
  scalar -> emit builder (\slot -> PutConstant slot scalar)

compileArguments :: Builder -> [Term] -> Maybe ([Slot], Builder)
compileArguments builder [] = Just ([], builder)
compileArguments builder (term : rest) = do
  (slot, next) <- compileTerm builder term
  (slots, final) <- compileArguments next rest
  pure (slot : slots, final)

emit :: Builder -> (Slot -> Instruction) -> Maybe (Slot, Builder)
emit (Builder next instructions) instruction
  | next == maxBound = Nothing
  | otherwise = Just (next, Builder (next + 1) (instruction next : instructions))

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
    HeadInstruction (..),
    BodyCall (..),
    ClauseCode,
    codeVariableCount,
    codeSlotCount,
    codeUnsharedSlotCount,
    codeInstructions,
    codeInstructionAt,
    codeHead,
    codeHeadInstructions,
    codeBody,
    compileClause,
  )
where

import Data.Array (Array, (!), listArray)
import qualified Data.Map.Strict as Map
import Data.Word (Word64)
import GHC.Float (castDoubleToWord64)
import Infera.Syntax (Clause (..), Term (..), functorOf, termVarIds)

-- | Registers are local to one clause activation. Instructions define each
-- register exactly once, and compound children always name earlier registers.
type Slot = Int

data Instruction
  = UseVariable !Slot !Int
  | PutConstant !Slot !Term
  | PutCompound !Slot !String [Slot]
  deriving (Eq, Show)

-- | Preorder head matching keeps input targets separate from construction
-- registers. A compound records its allocation slot, arity and instruction
-- width including itself. If its caller target is free, build that source
-- subtree and skip the remaining instructions in its width.
data HeadInstruction
  = HeadVariable !Int
  | HeadConstant !Slot !Term
  | HeadCompound !Slot !String !Int !Int
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
data ClauseCode = ClauseCode !Int !Int !Int [Instruction]
  (Array Slot Instruction) !Slot [HeadInstruction] [BodyCall]
  deriving (Eq, Show)

codeVariableCount :: ClauseCode -> Int
codeVariableCount (ClauseCode count _ _ _ _ _ _ _) = count

codeSlotCount :: ClauseCode -> Int
codeSlotCount (ClauseCode _ count _ _ _ _ _ _) = count

-- | Source-node count before variable/scalar register sharing.
codeUnsharedSlotCount :: ClauseCode -> Int
codeUnsharedSlotCount (ClauseCode _ _ count _ _ _ _ _) = count

codeInstructions :: ClauseCode -> [Instruction]
codeInstructions (ClauseCode _ _ _ instructions _ _ _ _) = instructions

-- | Constant-time access to the immutable construction plan, shared across
-- activations rather than rebuilding its instruction array for each call.
codeInstructionAt :: ClauseCode -> Slot -> Maybe Instruction
codeInstructionAt (ClauseCode _ count _ _ instructions _ _ _) slot
  | slot < 0 || slot >= count = Nothing
  | otherwise = Just (instructions ! slot)

codeHead :: ClauseCode -> Slot
codeHead (ClauseCode _ _ _ _ _ slot _ _) = slot

codeHeadInstructions :: ClauseCode -> [HeadInstruction]
codeHeadInstructions (ClauseCode _ _ _ _ _ _ instructions _) = instructions

codeBody :: ClauseCode -> [BodyCall]
codeBody (ClauseCode _ _ _ _ _ _ _ body) = body

-- Reverse instructions avoid quadratic list appends during compilation.
-- Share only local roots and immutable scalars, preserving float bits. Source
-- compounds keep distinct slots even when their printed forms are equal.
data CommonKey
  = VariableKey !Int | AtomKey !String | IntegerKey !Integer | FloatKey !Word64
  | CharacterKey !Char | StringKey !String
  deriving (Eq, Ord)

data Builder = Builder !Int !Int [Instruction] !(Map.Map CommonKey Slot)

data HeadNode
  = VariableNode !Int
  | ConstantNode !Slot !Term
  | CompoundNode !Slot !String [HeadNode]

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
      (headSlot, headNode, afterHead) <- compileTerm (Builder 0 0 [] Map.empty) (clauseHead clause)
      (body, Builder slots unshared instructions _) <- compileBody afterHead (clauseBody clause)
      let (_, headInstructions) = flattenHead headNode
          allocation = reverse instructions
      pure (ClauseCode (max 1 count) slots unshared allocation
        (listArray (0, slots - 1) allocation) headSlot (headInstructions []) body)
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
  (slot, _, next) <- compileTerm builder goal
  (calls, final) <- compileBody next rest
  pure (BodyCall slot key goal : calls, final)

compileTerm :: Builder -> Term -> Maybe (Slot, HeadNode, Builder)
compileTerm builder term = do
  visited <- visit builder
  case term of
    Var variable -> do
      (slot, next) <- common visited (VariableKey variable) (\target -> UseVariable target variable)
      pure (slot, VariableNode variable, next)
    Compound name arguments -> do
      (children, nodes, next) <- compileArguments visited arguments
      (slot, final) <- emit next (\target -> PutCompound target name children)
      pure (slot, CompoundNode slot name nodes, final)
    scalar -> do
      key <- scalarKey scalar
      (slot, next) <- common visited key (\target -> PutConstant target scalar)
      pure (slot, ConstantNode slot scalar, next)

compileArguments :: Builder -> [Term] -> Maybe ([Slot], [HeadNode], Builder)
compileArguments builder [] = Just ([], [], builder)
compileArguments builder (term : rest) = do
  (slot, node, next) <- compileTerm builder term
  (slots, nodes, final) <- compileArguments next rest
  pure (slot : slots, node : nodes, final)

visit :: Builder -> Maybe Builder
visit (Builder next unshared instructions commonSlots)
  | unshared == maxBound = Nothing
  | otherwise = Just (Builder next (unshared + 1) instructions commonSlots)

emit :: Builder -> (Slot -> Instruction) -> Maybe (Slot, Builder)
emit (Builder next unshared instructions commonSlots) instruction
  | next == maxBound = Nothing
  | otherwise = Just (next, Builder (next + 1) unshared (instruction next : instructions) commonSlots)

common :: Builder -> CommonKey -> (Slot -> Instruction) -> Maybe (Slot, Builder)
common builder@(Builder _ _ _ commonSlots) key instruction = case Map.lookup key commonSlots of
  Just slot -> Just (slot, builder)
  Nothing -> do
    (slot, Builder next unshared instructions previous) <- emit builder instruction
    pure (slot, Builder next unshared instructions (Map.insert key slot previous))

scalarKey :: Term -> Maybe CommonKey
scalarKey term = case term of
  Atom value -> Just (AtomKey value)
  IntLit value -> Just (IntegerKey value)
  FloatLit value -> Just (FloatKey (castDoubleToWord64 value))
  CharLit value -> Just (CharacterKey value)
  StrLit value -> Just (StringKey value)
  _ -> Nothing

flattenHead :: HeadNode -> (Int, [HeadInstruction] -> [HeadInstruction])
flattenHead node = case node of
  VariableNode variable -> (1, (HeadVariable variable :))
  ConstantNode slot scalar -> (1, (HeadConstant slot scalar :))
  CompoundNode slot name children ->
    let combine child (remainingWidth, following) =
          let (childWidth, childInstructions) = flattenHead child
           in (childWidth + remainingWidth, childInstructions . following)
        (childrenWidth, instructions) = foldr combine (0, id) children
        totalWidth = 1 + childrenWidth
     in (totalWidth, (HeadCompound slot name (length children) totalWidth :) . instructions)

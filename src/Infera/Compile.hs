-- | Clause and control bytecode. Compilation preserves
-- source variable numbers and body order; activation adds its fresh-ID base
-- only when a 'UseVariable' instruction executes. No renamed 'Term' tree is
-- built by the VM.
--
-- Body cuts are rewritten recursively, including ordinary data. Control nodes
-- carry immutable code and local-variable sets; only reached invocation leaves
-- and operands have construction plans.
module Infera.Compile
  ( Slot,
    Instruction (..),
    HeadInstruction (..),
    BodyCall (..),
    GoalOperand (..),
    GoalInstruction (..),
    GoalCode,
    goalCall,
    goalInstructions,
    goalRoot,
    goalRegisterCount,
    goalVariables,
    goalSuffixVariables,
    DataOperand (..),
    DataInstruction (..),
    DataPlan,
    dataTemplate,
    dataVariables,
    dataLocalIds,
    dataLocalCount,
    dataRuntimeInstructions,
    dataRuntimeRoot,
    dataInstructions,
    dataRoot,
    dataRegisterCount,
    ControlCode,
    ControlInstruction (..),
    CutOwner (..),
    controlTemplate,
    controlVariables,
    controlSuffixVariables,
    controlView,
    ClauseCode,
    codeVariableCount,
    codeSlotCount,
    codeUnsharedSlotCount,
    codeInstructions,
    codeInstructionAt,
    codeHead,
    codeHeadInstructions,
    codeBody,
    codeGoals,
    codeControls,
    compileClause,
  )
where

import Data.Array (Array, (!), listArray)
import qualified Data.IntMap.Strict as IM
import qualified Data.IntSet as IS
import Data.List (foldl')
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
  | PutOwner !Slot
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

-- | Logical locals never consume a construction register. Temporary operands
-- address a physical register, which may be reused after its last read.
data GoalOperand = Local !Int | Temporary !Int
  deriving (Eq, Show)

data GoalInstruction
  = GoalConstant !Int !Term
  | GoalOwner !Int
  | GoalCompound !Int !String [GoalOperand]
  deriving (Eq, Show)

-- The suffix sets share persistent IntSet subtrees. Keeping an eager list of
-- every future local at every goal would be quadratic for large bodies.
data GoalCode = GoalCode !BodyCall [GoalInstruction] !GoalOperand !Int
  !IS.IntSet !IS.IntSet
  deriving (Eq, Show)

goalCall :: GoalCode -> BodyCall
goalCall (GoalCode call _ _ _ _ _) = call

goalInstructions :: GoalCode -> [GoalInstruction]
goalInstructions (GoalCode _ instructions _ _ _ _) = instructions

goalRoot :: GoalCode -> GoalOperand
goalRoot (GoalCode _ _ root _ _ _) = root

goalRegisterCount :: GoalCode -> Int
goalRegisterCount (GoalCode _ _ _ count _ _) = count

goalVariables :: GoalCode -> IS.IntSet
goalVariables (GoalCode _ _ _ _ variables _) = variables

goalSuffixVariables :: GoalCode -> IS.IntSet
goalSuffixVariables (GoalCode _ _ _ _ _ variables) = variables

-- | Runtime locals index this plan's compact source-ID layout. They never
-- contain logical IDs or heap addresses. Temporary registers retain the
-- ordinary last-use allocation scheme.
data DataOperand = DataLocal !Int | DataTemporary !Int
  deriving (Eq, Show)

data DataInstruction
  = DataConstant !Int !Term
  | DataOwner !Int
  | DataCompound !Int !String [DataOperand]
  deriving (Eq, Show)

-- Data operands and ordinary invocation leaves store one dense construction
-- plan. The source-ID list and array share the same immutable layout: the VM
-- requests logical roots in list order, while compatibility accessors decode
-- dense operands through the array. Control ancestors carry neither a plan
-- nor a heap address.
data DataPlan = DataPlan !Term [DataInstruction] !DataOperand !Int !IS.IntSet
  [Int] !Int !(Array Int Int)
  deriving (Eq, Show)

dataTemplate :: DataPlan -> Term
dataTemplate (DataPlan template _ _ _ _ _ _ _) = template

dataLocalIds :: DataPlan -> [Int]
dataLocalIds (DataPlan _ _ _ _ _ locals _ _) = locals

dataLocalCount :: DataPlan -> Int
dataLocalCount (DataPlan _ _ _ _ _ _ count _) = count

dataRuntimeInstructions :: DataPlan -> [DataInstruction]
dataRuntimeInstructions (DataPlan _ instructions _ _ _ _ _ _) = instructions

dataRuntimeRoot :: DataPlan -> DataOperand
dataRuntimeRoot (DataPlan _ _ root _ _ _ _ _) = root

-- | Source-oriented compatibility view, decoded lazily from the single
-- stored runtime plan. Normal materialization uses the dense accessors.
dataInstructions :: DataPlan -> [GoalInstruction]
dataInstructions (DataPlan _ instructions _ _ _ _ _ locals) = map instruction instructions
  where
    instruction (DataConstant register scalar) = GoalConstant register scalar
    instruction (DataOwner register) = GoalOwner register
    instruction (DataCompound register name children) =
      GoalCompound register name (map (sourceOperand locals) children)

dataRoot :: DataPlan -> GoalOperand
dataRoot (DataPlan _ _ root _ _ _ _ locals) = sourceOperand locals root

sourceOperand :: Array Int Int -> DataOperand -> GoalOperand
sourceOperand locals (DataLocal local) = Local (locals ! local)
sourceOperand _ (DataTemporary register) = Temporary register

dataRegisterCount :: DataPlan -> Int
dataRegisterCount (DataPlan _ _ _ registers _ _ _ _) = registers

dataVariables :: DataPlan -> IS.IntSet
dataVariables (DataPlan _ _ _ _ variables _ _ _) = variables

data CutOwner = LocalBase | LiteralInteger !Integer
  deriving (Eq, Show)

data ControlInstruction
  = Invoke !DataPlan !(Maybe (String, Int))
  | Sequence [ControlCode]
  | Alternative !ControlCode !ControlCode
  | Cut !CutOwner
  | Once !ControlCode
  | Not !ControlCode
  | If !ControlCode !ControlCode !(Maybe ControlCode)
  | FindAll !DataPlan !ControlCode !DataPlan
  | Call !DataPlan [DataPlan]
  deriving (Eq, Show)

data ControlCode = ControlCode !Term !IS.IntSet !IS.IntSet !ControlInstruction
  deriving (Eq, Show)

controlTemplate :: ControlCode -> Term
controlTemplate (ControlCode template _ _ _) = template

controlVariables :: ControlCode -> IS.IntSet
controlVariables (ControlCode _ variables _ _) = variables

controlSuffixVariables :: ControlCode -> IS.IntSet
controlSuffixVariables (ControlCode _ _ variables _) = variables

controlView :: ControlCode -> ControlInstruction
controlView (ControlCode _ _ _ instruction) = instruction

-- Keep both the constructor and record-update syntax private: an instruction
-- operand cannot refer forward, use an invalid local variable, or smuggle a
-- compound into PutConstant.
data ClauseCode = ClauseCode !Int !Int !Int [Instruction]
  (Array Slot Instruction) !Slot [HeadInstruction] [BodyCall] [GoalCode] [ControlCode]
  deriving (Eq, Show)

codeVariableCount :: ClauseCode -> Int
codeVariableCount (ClauseCode count _ _ _ _ _ _ _ _ _) = count

codeSlotCount :: ClauseCode -> Int
codeSlotCount (ClauseCode _ count _ _ _ _ _ _ _ _) = count

-- | Source-node count before variable/scalar register sharing.
codeUnsharedSlotCount :: ClauseCode -> Int
codeUnsharedSlotCount (ClauseCode _ _ count _ _ _ _ _ _ _) = count

codeInstructions :: ClauseCode -> [Instruction]
codeInstructions (ClauseCode _ _ _ instructions _ _ _ _ _ _) = instructions

-- | Constant-time access to the immutable construction plan, shared across
-- activations rather than rebuilding its instruction array for each call.
codeInstructionAt :: ClauseCode -> Slot -> Maybe Instruction
codeInstructionAt (ClauseCode _ count _ _ instructions _ _ _ _ _) slot
  | slot < 0 || slot >= count = Nothing
  | otherwise = Just (instructions ! slot)

codeHead :: ClauseCode -> Slot
codeHead (ClauseCode _ _ _ _ _ slot _ _ _ _) = slot

codeHeadInstructions :: ClauseCode -> [HeadInstruction]
codeHeadInstructions (ClauseCode _ _ _ _ _ _ instructions _ _ _) = instructions

codeBody :: ClauseCode -> [BodyCall]
codeBody (ClauseCode _ _ _ _ _ _ _ body _ _) = body

codeGoals :: ClauseCode -> [GoalCode]
codeGoals (ClauseCode _ _ _ _ _ _ _ _ goals _) = goals

codeControls :: ClauseCode -> [ControlCode]
codeControls (ClauseCode _ _ _ _ _ _ _ _ _ controls) = controls

-- Reverse instructions avoid quadratic list appends during compilation.
-- Share only local roots and immutable scalars, preserving float bits. Source
-- compounds keep distinct slots even when their printed forms are equal.
data CommonKey
  = VariableKey !Int | OwnerKey | AtomKey !String | IntegerKey !Integer | FloatKey !Word64
  | CharacterKey !Char | StringKey !String
  deriving (Eq, Ord)

data Builder = Builder !Int !Int [Instruction] !(Map.Map CommonKey Slot)

data HeadNode
  = VariableNode !Int
  | ConstantNode !Slot !Term
  | CompoundNode !Slot !String [HeadNode]

-- | Compile facts, ordinary bodies and native control nodes, preserving
-- scalar types and raw local IDs. Dynamic/uncallable leaves remain native
-- invocation nodes, so their existing runtime checks decide their behavior.
-- Malformed local IDs and uncallable heads retain the interpreter fallback.
--
-- At least one fresh logical ID is reserved even for ground clauses, matching
-- the native interpreter's activation owner and fresh-counter convention.
compileClause :: Clause -> Maybe ClauseCode
compileClause clause
  | count < 0 || not (all validVariable variables) = Nothing
  | otherwise = do
      _ <- functorOf (clauseHead clause)
      (headSlot, headNode, afterHead) <- compileTerm (Builder 0 0 [] Map.empty) (clauseHead clause)
      (body, Builder slots unshared instructions _) <- compileBody afterHead (clauseBody clause)
      controls <- mapM compileControl (clauseBody clause)
      let (_, headInstructions) = flattenHead headNode
          allocation = reverse instructions
      pure (ClauseCode (max 1 count) slots unshared allocation
        (listArray (0, slots - 1) allocation) headSlot (headInstructions []) body
        (suffixGoals (map compatibilityGoal controls)) (suffixControls controls))
  where
    count = clauseNVars clause
    variables = concatMap termVarIds (clauseHead clause : clauseBody clause)
    validVariable variable = variable >= 0 && variable < count

compileBody :: Builder -> [Term] -> Maybe ([BodyCall], Builder)
compileBody builder [] = Just ([], builder)
compileBody builder (goal : rest) = do
  let key = compatibilityKey goal
  (slot, next) <- compileBodyTerm builder goal
  (calls, final) <- compileBody next rest
  pure (BodyCall slot key goal : calls, final)

compatibilityKey :: Term -> (String, Int)
compatibilityKey = maybe ("$dynamic", -1) id . functorOf

-- Body rewriting is recursive even in data. Owner is a dynamic scalar, kept
-- separate from source literals so its activation base cannot be guessed or
-- accidentally shared with an integer literal at compile time.
compileBodyTerm :: Builder -> Term -> Maybe (Slot, Builder)
compileBodyTerm builder term = do
  visited <- visit builder
  case term of
    Atom "!" -> do
      ownerVisited <- visit visited
      (owner, next) <- common ownerVisited OwnerKey PutOwner
      emit next (\slot -> PutCompound slot "$cut" [owner])
    Var variable -> common visited (VariableKey variable) (\slot -> UseVariable slot variable)
    Compound name arguments -> do
      (children, next) <- bodyArguments visited arguments
      emit next (\slot -> PutCompound slot name children)
    scalar -> do
      key <- scalarKey scalar
      common visited key (\slot -> PutConstant slot scalar)
  where
    bodyArguments current [] = Just ([], current)
    bodyArguments current (argument : rest) = do
      (slot, next) <- compileBodyTerm current argument
      (slots, final) <- bodyArguments next rest
      pure (slot : slots, final)

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

goalFromPlan :: DataPlan -> GoalCode
goalFromPlan plan =
  let template = dataTemplate plan
      key = compatibilityKey template
      physicalRoot = dataRoot plan
      rootRegister = case physicalRoot of Local local -> local; Temporary register -> register
   in GoalCode (BodyCall rootRegister key template) (dataInstructions plan)
        physicalRoot (dataRegisterCount plan) (dataVariables plan) IS.empty

-- Ordinary top-level leaves share their already compiled data plan. Full
-- control-wrapper plans are compatibility oracles only and are compiled
-- lazily when codeGoals/materializeNext is requested. The checked whole-body
-- construction plan bounds every individual goal's nodes/registers, and the
-- private lowering preserves defined SSA operands, so failure here indicates
-- an internal compiler invariant violation rather than unsupported input.
compatibilityGoal :: ControlCode -> GoalCode
compatibilityGoal control = case controlView control of
  Invoke plan _ -> goalFromPlan plan
  _ -> case compileDataPlan (controlTemplate control) of
    Just plan -> goalFromPlan plan
    Nothing -> error "Infera.Compile: validated compatibility plan failed"

compileDataPlan :: Term -> Maybe DataPlan
compileDataPlan template = do
  (rootSlot, Builder _ _ reversed _) <- compileBodyTerm (Builder 0 0 [] Map.empty) template
  (virtual, roots) <- virtualGoal (reverse reversed)
  root <- IM.lookup rootSlot roots
  (instructions, physicalRoot, registers) <- allocateGoal virtual root
  let variables = IS.fromList (termVarIds template)
      localIds = IS.toAscList variables
      localCount = IS.size variables
      localIndices = IM.fromDistinctAscList (zip localIds [0 ..])
      operand (Local local) = DataLocal <$> IM.lookup local localIndices
      operand (Temporary register) = Just (DataTemporary register)
      instruction (GoalConstant register scalar) = Just (DataConstant register scalar)
      instruction (GoalOwner register) = Just (DataOwner register)
      instruction (GoalCompound register name children) =
        DataCompound register name <$> mapM operand children
  denseInstructions <- mapM instruction instructions
  denseRoot <- operand physicalRoot
  pure (DataPlan template denseInstructions denseRoot registers variables
    localIds localCount (listArray (0, localCount - 1) localIds))

-- Erase variable move instructions before physical allocation. Source locals
-- are resolved through their stable IDs only when this goal materializes.
virtualGoal :: [Instruction] -> Maybe ([GoalInstruction], IM.IntMap GoalOperand)
virtualGoal = go [] IM.empty
  where
    go instructions roots [] = Just (reverse instructions, roots)
    go instructions roots (instruction : rest) = case instruction of
      UseVariable slot local -> go instructions (IM.insert slot (Local local) roots) rest
      PutConstant slot scalar -> go (GoalConstant slot scalar : instructions)
        (IM.insert slot (Temporary slot) roots) rest
      PutOwner slot -> go (GoalOwner slot : instructions)
        (IM.insert slot (Temporary slot) roots) rest
      PutCompound slot name children -> do
        operands <- mapM (\child -> IM.lookup child roots) children
        go (GoalCompound slot name operands : instructions)
          (IM.insert slot (Temporary slot) roots) rest

-- Read every child using the old assignment, retire its final uses, then
-- assign the destination from the free pool. The runtime must likewise read
-- every child address before overwriting a recycled destination register.
allocateGoal :: [GoalInstruction] -> GoalOperand
  -> Maybe ([GoalInstruction], GoalOperand, Int)
allocateGoal instructions root = do
  let countOperand counts (Local _) = counts
      countOperand counts (Temporary temporary) = IM.insertWith (+) temporary (1 :: Int) counts
      operands (GoalConstant _ _) = []
      operands (GoalOwner _) = []
      operands (GoalCompound _ _ children) = children
      uses = foldl' countOperand IM.empty (root : concatMap operands instructions)
      resolve _ local@(Local _) = Just local
      resolve assignments (Temporary temporary) = Temporary <$> IM.lookup temporary assignments
      release (assignments, remaining, free) operand = case operand of
        Local _ -> Just (assignments, remaining, free)
        Temporary temporary -> do
          count <- IM.lookup temporary remaining
          register <- IM.lookup temporary assignments
          if count <= 0 then Nothing else if count == 1
            then Just (IM.delete temporary assignments, IM.delete temporary remaining, IS.insert register free)
            else Just (assignments, IM.insert temporary (count - 1) remaining, free)
      claim next free = case IS.minView free of
        Just (register, remaining) -> Just (register, next, remaining)
        Nothing | next < maxBound -> Just (next, next + 1, free)
        _ -> Nothing
      step (built, assignments, remaining, free, next) instruction = do
        let children = operands instruction
        physicalChildren <- mapM (resolve assignments) children
        (retained, usesLeft, available) <- foldMaybe release (assignments, remaining, free) children
        (destination, following, pool) <- claim next available
        let (virtualDestination, physical) = case instruction of
              GoalConstant temporary scalar -> (temporary, GoalConstant destination scalar)
              GoalOwner temporary -> (temporary, GoalOwner destination)
              GoalCompound temporary name _ -> (temporary, GoalCompound destination name physicalChildren)
        pure (physical : built, IM.insert virtualDestination destination retained, usesLeft, pool, following)
  (reversed, assignments, _, _, registers) <- foldMaybe step ([], IM.empty, uses, IS.empty, 0) instructions
  physicalRoot <- resolve assignments root
  pure (reverse reversed, physicalRoot, registers)

foldMaybe :: (state -> value -> Maybe state) -> state -> [value] -> Maybe state
foldMaybe _ state [] = Just state
foldMaybe step state (value : rest) = step state value >>= \next -> foldMaybe step next rest

suffixGoals :: [GoalCode] -> [GoalCode]
suffixGoals = snd . foldr add (IS.empty, [])
  where
    add (GoalCode call instructions root registers variables _) (following, goals) =
      let live = IS.union variables following
       in (live, GoalCode call instructions root registers variables live : goals)

compileControl :: Term -> Maybe ControlCode
compileControl template = do
  (instruction, variables) <- case template of
    Compound "," [left, right] -> do
      a <- compileControl left
      b <- compileControl right
      pure (Sequence [a, b], IS.union (controlVariables a) (controlVariables b))
    Compound ";" [Compound "->" [condition, yes], no] -> do
      c <- compileControl condition
      y <- compileControl yes
      n <- compileControl no
      pure (If c y (Just n), IS.unions (map controlVariables [c, y, n]))
    Compound ";" [left, right] -> do
      a <- compileControl left
      b <- compileControl right
      pure (Alternative a b, IS.union (controlVariables a) (controlVariables b))
    Compound "->" [condition, yes] -> do
      c <- compileControl condition
      y <- compileControl yes
      pure (If c y Nothing, IS.union (controlVariables c) (controlVariables y))
    Atom "!" -> pure (Cut LocalBase, IS.empty)
    Compound "$cut" [IntLit owner] -> pure (Cut (LiteralInteger owner), IS.empty)
    Compound "once" [child] -> do
      code <- compileControl child
      pure (Once code, controlVariables code)
    Compound "not" [child] -> do
      code <- compileControl child
      pure (Not code, controlVariables code)
    Compound "findall" [value, child, target] -> do
      valuePlan <- compileDataPlan value
      code <- compileControl child
      targetPlan <- compileDataPlan target
      pure (FindAll valuePlan code targetPlan,
        IS.unions [dataVariables valuePlan, controlVariables code, dataVariables targetPlan])
    Compound "call" (callable : arguments) -> do
      callablePlan <- compileDataPlan callable
      argumentPlans <- mapM compileDataPlan arguments
      pure (Call callablePlan argumentPlans,
        IS.unions (map dataVariables (callablePlan : argumentPlans)))
    _ -> do
      plan <- compileDataPlan template
      pure (Invoke plan (functorOf template), dataVariables plan)
  pure (ControlCode template variables variables instruction)

suffixControls :: [ControlCode] -> [ControlCode]
suffixControls = snd . foldr add (IS.empty, [])
  where
    add (ControlCode template variables _ instruction) (following, controls) =
      let live = IS.union variables following
       in (live, ControlCode template variables live instruction : controls)

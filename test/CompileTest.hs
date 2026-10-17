{-# LANGUAGE OverloadedStrings #-}

-- The compiler's public contract is a closed, postorder register program.
-- Decode that contract independently of the heap VM so register mistakes,
-- unsupported syntax and changes to raw source identities are visible here.
module CompileTest (compileGroup) where

import Control.Monad (foldM, forM_)
import qualified Data.IntMap.Strict as IM
import qualified Data.IntSet as IS
import Data.List (nub)
import Data.Maybe (isNothing, listToMaybe)
import Data.Word (Word64)
import GHC.Float (castDoubleToWord64, castWord64ToDouble)
import Hedgehog hiding (Var)
import qualified Hedgehog.Gen as Gen
import qualified Hedgehog.Range as Range
import Infera.Compile
import Infera.Syntax
import Infera.Unify (renameBody, replaceCuts)

data Observed
  = OAtom String | OVar VarId | OInt Integer | OFloat Word64
  | OChar Char | OString String | OCompound String [Observed]
  deriving (Eq, Show)

observe :: Term -> Observed
observe term = case term of
  Atom value -> OAtom value
  Var value -> OVar value
  IntLit value -> OInt value
  FloatLit value -> OFloat (castDoubleToWord64 value)
  CharLit value -> OChar value
  StrLit value -> OString value
  Compound name arguments -> OCompound name (map observe arguments)

destination :: Instruction -> Slot
destination instruction = case instruction of
  UseVariable slot _ -> slot
  PutConstant slot _ -> slot
  PutOwner slot -> slot
  PutCompound slot _ _ -> slot

-- This decoder uses only the documented instruction/register interface.
-- Forward references, repeated destinations and non-scalar constants fail.
decode :: ClauseCode -> Maybe [Term]
decode = decodeWithOwner 0

decodeWithOwner :: Integer -> ClauseCode -> Maybe [Term]
decodeWithOwner owner code = do
  registers <- foldM step IM.empty (codeInstructions code)
  mapM (\slot -> IM.lookup slot registers) (codeHead code : map bodySlot (codeBody code))
  where
    step registers instruction
      | IM.member (destination instruction) registers = Nothing
      | otherwise = do
          term <- case instruction of
            UseVariable _ variable
              | variable >= 0 && variable < codeVariableCount code -> Just (Var variable)
              | otherwise -> Nothing
            PutConstant _ constant -> case constant of
              Var _ -> Nothing
              Compound _ _ -> Nothing
              scalar -> Just scalar
            PutOwner _ -> Just (IntLit owner)
            PutCompound slot name children
              | all (< slot) children -> Compound name <$> mapM (\child -> IM.lookup child registers) children
              | otherwise -> Nothing
          pure (IM.insert (destination instruction) term registers)

-- Decode the independent preorder matcher, checking every subtree width and
-- its correspondence to the separately cached construction plan.
decodeHead :: ClauseCode -> Maybe Term
decodeHead code = do
  (term, slot, _, remaining) <- node (codeHeadInstructions code)
  if null remaining && slot == codeHead code then Just term else Nothing
  where
    variables = IM.fromList [(variable, slot) | UseVariable slot variable <- codeInstructions code]
    node (HeadVariable variable : rest) = do
      slot <- IM.lookup variable variables
      pure (Var variable, slot, 1, rest)
    node (HeadConstant slot scalar : rest) = do
      instruction <- codeInstructionAt code slot
      case instruction of
        PutConstant destination' actual
          | destination' == slot && observe actual == observe scalar -> pure (scalar, slot, 1, rest)
        _ -> Nothing
    node (HeadCompound slot name arity width : rest) = do
      (children, slots, widths, remaining) <- nodes arity rest
      instruction <- codeInstructionAt code slot
      case instruction of
        PutCompound destination' actual arguments
          | destination' == slot && actual == name && arguments == slots
            && width == 1 + sum widths ->
              pure (Compound name children, slot, width, remaining)
        _ -> Nothing
    node [] = Nothing
    nodes 0 rest = Just ([], [], [], rest)
    nodes count rest
      | count < 0 = Nothing
      | otherwise = do
          (term, slot, width, next) <- node rest
          (terms, slots, widths, remaining) <- nodes (count - 1) next
          pure (term : terms, slot : slots, width : widths, remaining)

nodeCount :: Term -> Int
nodeCount (Compound _ arguments) = 1 + sum (map nodeCount arguments)
nodeCount _ = 1

bodyNodeCount :: Term -> Int
bodyNodeCount (Atom "!") = 2
bodyNodeCount (Compound _ arguments) = 1 + sum (map bodyNodeCount arguments)
bodyNodeCount _ = 1

-- Physical registers may be overwritten. Resolve all child values from the
-- old register map before installing a constructor into a recycled slot.
decodeGoal :: GoalCode -> Maybe Term
decodeGoal = decodeGoalWithOwner 0

decodeGoalWithOwner :: Integer -> GoalCode -> Maybe Term
decodeGoalWithOwner owner goal =
  decodeConstruction owner (goalRegisterCount goal) (goalInstructions goal) (goalRoot goal)

decodeData :: Integer -> DataPlan -> Maybe Term
decodeData owner plan =
  decodeConstruction owner (dataRegisterCount plan) (dataInstructions plan) (dataRoot plan)

decodeConstruction :: Integer -> Int -> [GoalInstruction] -> GoalOperand -> Maybe Term
decodeConstruction owner count instructions root = do
  registers <- foldM step IM.empty instructions
  operand registers root
  where
    valid register = register >= 0 && register < count
    operand _ (Local variable) = Just (Var variable)
    operand registers (Temporary register)
      | valid register = IM.lookup register registers
      | otherwise = Nothing
    step registers instruction = do
      (destination', term) <- case instruction of
        GoalConstant register scalar -> case scalar of
          Var _ -> Nothing
          Compound _ _ -> Nothing
          _ -> Just (register, scalar)
        GoalOwner register -> Just (register, IntLit owner)
        GoalCompound register name children -> do
          values <- mapM (operand registers) children
          pure (register, Compound name values)
      if valid destination' then Just (IM.insert destination' term registers) else Nothing

genScalar :: Gen Term
genScalar = Gen.choice
  [ Atom <$> Gen.element ["nil", "leaf", "true", "!", "\955"],
    IntLit <$> Gen.integral (Range.linear (-100) 100),
    FloatLit <$> Gen.element
      [-1 / 0, -2.5, -0.0, 0.0, 1.5, 1 / 0, castWord64ToDouble 0x7ff8000000000042],
    CharLit <$> Gen.element ['a', '\955'],
    StrLit <$> Gen.element ["", "kept", "\955"]
  ]

genTerm :: Int -> Int -> Gen Term
genTerm count depth
  | depth <= 0 = leaf
  | otherwise = Gen.frequency
      [ (4, leaf),
        (3, Compound <$> Gen.element ["box", "cons", "plus", ";", "->", "call"]
          <*> Gen.list (Range.linear 0 3) (genTerm count (depth - 1)))
      ]
  where
    leaf
      | count <= 0 = genScalar
      | otherwise = Gen.frequency
          [(3, genScalar), (2, Var <$> Gen.int (Range.linear 0 (count - 1)))]

genClause :: Gen Clause
genClause = do
  count <- Gen.int (Range.linear 0 6)
  headTerm <- Gen.choice
    [ pure (Atom "generated"),
      Compound "generated" <$> Gen.list (Range.linear 0 4) (genTerm count 3)
    ]
  body <- Gen.list (Range.linear 0 4) $
    Compound <$> Gen.element ["helper", "unify", "is", "in", "write", "unknown"]
      <*> Gen.list (Range.linear 0 3) (genTerm count 3)
  pure (Clause headTerm body count)

prop_generated_register_program_preserves_raw_clause :: Property
prop_generated_register_program_preserves_raw_clause = withTests 250 . property $ do
  clause <- forAll genClause
  code <- evalMaybe (compileClause clause)
  decoded <- evalMaybe (decode code)
  headTerm <- evalMaybe (decodeHead code)
  map observe decoded === map observe (clauseHead clause : map (renameBody 0) (clauseBody clause))
  observe headTerm === observe (clauseHead clause)
  codeVariableCount code === max 1 (clauseNVars clause)
  codeSlotCount code === length (codeInstructions code)
  codeUnsharedSlotCount code === nodeCount (clauseHead clause) + sum (map bodyNodeCount (clauseBody clause))
  length (codeHeadInstructions code) === nodeCount (clauseHead clause)
  assert (codeSlotCount code <= codeUnsharedSlotCount code)
  map destination (codeInstructions code) === [0 .. codeSlotCount code - 1]
  map (observe . bodyTemplate) (codeBody code) === map observe (clauseBody clause)
  map (Just . bodyKey) (codeBody code) === map functorOf (clauseBody clause)
  let goals = codeGoals code
      variables = map (IS.fromList . termVarIds) (clauseBody clause)
  physical <- evalMaybe (mapM decodeGoal goals)
  map observe physical === map observe (map (renameBody 0) (clauseBody clause))
  map (observe . bodyTemplate . goalCall) goals === map observe (clauseBody clause)
  map (Just . bodyKey . goalCall) goals === map functorOf (clauseBody clause)
  map goalVariables goals === variables
  map goalSuffixVariables goals === init (scanr IS.union IS.empty variables)
  forM_ goals $ \goal ->
    assert (goalRegisterCount goal <= length (goalInstructions goal))

unit :: PropertyT IO () -> Property
unit = withTests 1 . property

prop_control_and_recursive_cut_lowering :: Property
prop_control_and_recursive_cut_lowering = unit $ do
  forM_
    [ ",", ";", "->", "call", "once", "not", "findall", "forall", "minimize",
      "phrase", "emit", "phrase_from_file", "!", "$cut"
    ] $ \name -> do
      code <- evalMaybe (compileClause (Clause (Atom "p") [Compound name []] 0))
      length (codeControls code) === 1
  forM_ [Atom "!", Compound "$cut" [IntLit 42]] $ \cut ->
    forM_ [cut, Compound "helper" [Compound "box" [cut]], Compound "unify" [Var 0, cut]] $ \goal ->
      do
        let clause = Clause (Compound "p" [Var 0, Atom "!"]) [goal] 1
        code <- evalMaybe (compileClause clause)
        raw <- evalMaybe (decodeWithOwner 77 code)
        physical <- evalMaybe (mapM (decodeGoalWithOwner 77) (codeGoals code))
        -- This source-plan decoder keeps local variable numbers unchanged;
        -- only the dynamic cut-owner operand receives the supplied value.
        map observe raw === map observe [clauseHead clause, replaceCuts 77 goal]
        map observe physical === map observe [replaceCuts 77 goal]
  forM_
    [ (Compound "," [Atom "true", Atom "fail"], "sequence"),
      (Compound ";" [Atom "true", Atom "fail"], "alternative"),
      (Compound ";" [Compound "->" [Atom "true", Atom "fail"], Atom "true"], "if"),
      (Compound ";" [Var 0, Atom "true"], "alternative"),
      (Atom "!", "cut-local"),
      (Compound "$cut" [IntLit (-7)], "cut-literal"),
      (Compound "$cut" [Var 0], "invoke"),
      (Compound "once" [Atom "true"], "once"),
      (Compound "not" [Atom "true"], "not"),
      (Compound "findall" [Var 0, Atom "true", Var 1], "findall"),
      (Compound "call" [Var 0, Atom "a"], "call"),
      (Compound "unify" [Var 0, Var 1], "builtin"),
      (Compound "all_different" [Var 0], "builtin"),
      (Compound "unify" [Var 0], "invoke"),
      (Atom "unify", "invoke")
    ] $ \(template, expected) -> do
      code <- evalMaybe (compileClause (Clause (Atom "p") [template] 2))
      control <- evalMaybe (listToMaybe (codeControls code))
      controlKind control === expected
  where
    controlKind code = case controlView code of
      Invoke _ _ -> "invoke" :: String
      BuiltinCall _ _ _ -> "builtin"
      Sequence _ -> "sequence"
      Alternative _ _ -> "alternative"
      Cut LocalBase -> "cut-local"
      Cut (LiteralInteger _) -> "cut-literal"
      Once _ -> "once"
      Not _ -> "not"
      If _ _ _ -> "if"
      FindAll _ _ _ -> "findall"
      Call _ _ -> "call"

prop_malformed_variables_reject_and_dynamic_leaves_compile :: Property
prop_malformed_variables_reject_and_dynamic_leaves_compile = unit $ do
  forM_
    [ Clause (Atom "p") [] (-1),
      Clause (Compound "p" [Var (-1)]) [] 1,
      Clause (Compound "p" [Var 1]) [] 1,
      Clause (Atom "p") [Compound "helper" [Var 0]] 0,
      Clause (Var 0) [] 1,
      Clause (IntLit 1) [] 0
    ] $ \clause -> assert (isNothing (compileClause clause))
  forM_ [Var 0, IntLit 1, FloatLit 1.5, StrLit "helper", CharLit 'x'] $ \goal ->
    do
      code <- evalMaybe (compileClause (Clause (Compound "p" [Var 0]) [goal] 1))
      control <- evalMaybe (listToMaybe (codeControls code))
      case controlView control of
        Invoke plan Nothing -> do
          raw <- evalMaybe (decodeData 0 plan)
          observe raw === observe goal
        _ -> failure

prop_first_order_data_and_scalar_identities_remain_distinct :: Property
prop_first_order_data_and_scalar_identities_remain_distinct = unit $ do
  let payload = castWord64ToDouble 0x7ff8000000000042
      clause = Clause (Compound "p" [Var 0, Var 0])
        [ Compound "helper"
            [ Compound ";" [Compound "call" [Var 0], Compound "->" [Atom "true", Atom "false"]],
              Atom "true", Compound "true" [], FloatLit payload, FloatLit (-0.0), FloatLit 0.0
            ],
          Compound "write" [Var 0]
        ] 1
  code <- evalMaybe (compileClause clause)
  decoded <- evalMaybe (decode code)
  map observe decoded === map observe (clauseHead clause : clauseBody clause)
  map bodyKey (codeBody code) === [("helper", 6), ("write", 1)]
  codeVariableCount code === 1
  fact <- evalMaybe (compileClause (Clause (Atom "fact") [] 0))
  codeVariableCount fact === 1
  codeBody fact === []
  codeSlotCount fact === 1

prop_register_sharing_retains_scalar_bits_and_distinct_constructors :: Property
prop_register_sharing_retains_scalar_bits_and_distinct_constructors = unit $ do
  let nanA = FloatLit (castWord64ToDouble 0x7ff8000000000042)
      nanB = FloatLit (castWord64ToDouble 0x7ff8000000000043)
      zero = FloatLit 0.0
      negativeZero = FloatLit (-0.0)
      clause = Clause (Compound "p"
        [Var 0, Var 0, nanA, nanA, nanB, zero, negativeZero,
         Atom "same", Atom "same", IntLit 7, IntLit 7,
         Compound "box" [Var 0], Compound "box" [Var 0]])
        [Compound "helper" [Var 0, Var 0, nanA, zero, negativeZero]] 1
  code <- evalMaybe (compileClause clause)
  decoded <- evalMaybe (decode code)
  decodedHead <- evalMaybe (decodeHead code)
  physical <- evalMaybe (mapM decodeGoal (codeGoals code))
  map observe decoded === map observe (clauseHead clause : clauseBody clause)
  observe decodedHead === observe (clauseHead clause)
  map observe physical === map observe (clauseBody clause)
  let instructions = codeInstructions code
      constants = [observe scalar | PutConstant _ scalar <- instructions]
  length [() | UseVariable _ 0 <- instructions] === 1
  length [() | PutCompound _ "box" _ <- instructions] === 2
  length constants === length (nub constants)
  forM_ [nanA, nanB, zero, negativeZero] $ \scalar ->
    length (filter (== observe scalar) constants) === 1
  assert (codeSlotCount code < codeUnsharedSlotCount code)
  assert (isNothing (codeInstructionAt code (-1)))
  assert (isNothing (codeInstructionAt code (codeSlotCount code)))

prop_per_goal_register_lifetimes_and_future_local_roots :: Property
prop_per_goal_register_lifetimes_and_future_local_roots = unit $ do
  let nested = foldr (\_ child -> Compound "box" [child]) (Var 0) [1 .. 200 :: Int]
      clause = Clause (Compound "p" [Var 0])
        [ Compound "helper" [nested],
          Compound "helper" [Compound "pair" [Var 1, Var 1]],
          Atom "fail", Compound "helper" [Var 2]
        ] 3
  code <- evalMaybe (compileClause clause)
  let goals = codeGoals code
  first <- evalMaybe (listToMaybe goals)
  physical <- evalMaybe (mapM decodeGoal goals)
  map observe physical === map observe (clauseBody clause)
  map goalRegisterCount goals === [1, 1, 1, 1]
  map goalSuffixVariables goals === map IS.fromList [[0, 1, 2], [1, 2], [2], [2]]
  assert (length (goalInstructions first) > 200)
  assert (codeSlotCount code > 200)
  -- Every constructor in the first goal can overwrite the child's final-use
  -- register, while source-local variables never occupy temporary registers.
  forM_ (goalInstructions first) $ \instruction -> case instruction of
    GoalCompound destination' _ _ -> destination' === 0
    GoalConstant _ _ -> failure
    GoalOwner _ -> failure

compileGroup :: Group
compileGroup = Group "clause compiler"
  [ ("generated_register_program_preserves_raw_clause", prop_generated_register_program_preserves_raw_clause),
    ("control_and_recursive_cut_lowering", prop_control_and_recursive_cut_lowering),
    ("malformed_variables_reject_and_dynamic_leaves_compile", prop_malformed_variables_reject_and_dynamic_leaves_compile),
    ("first_order_data_and_scalar_identities_remain_distinct", prop_first_order_data_and_scalar_identities_remain_distinct),
    ("register_sharing_retains_scalar_bits_and_distinct_constructors", prop_register_sharing_retains_scalar_bits_and_distinct_constructors),
    ("per_goal_register_lifetimes_and_future_local_roots", prop_per_goal_register_lifetimes_and_future_local_roots)
  ]

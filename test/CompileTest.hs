{-# LANGUAGE OverloadedStrings #-}

-- The compiler's public contract is a closed, postorder register program.
-- Decode that contract independently of the heap VM so register mistakes,
-- unsupported syntax and changes to raw source identities are visible here.
module CompileTest (compileGroup) where

import Control.Monad (foldM, forM_)
import qualified Data.IntMap.Strict as IM
import Data.Maybe (isNothing)
import Data.Word (Word64)
import GHC.Float (castDoubleToWord64, castWord64ToDouble)
import Hedgehog hiding (Var)
import qualified Hedgehog.Gen as Gen
import qualified Hedgehog.Range as Range
import Infera.Compile
import Infera.Syntax

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
  PutCompound slot _ _ -> slot

-- This decoder uses only the documented instruction/register interface.
-- Forward references, repeated destinations and non-scalar constants fail.
decode :: ClauseCode -> Maybe [Term]
decode code = do
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
            PutCompound slot name children
              | all (< slot) children -> Compound name <$> mapM (\child -> IM.lookup child registers) children
              | otherwise -> Nothing
          pure (IM.insert (destination instruction) term registers)

genScalar :: Gen Term
genScalar = Gen.choice
  [ Atom <$> Gen.element ["nil", "leaf", "true", "\955"],
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
  map observe decoded === map observe (clauseHead clause : clauseBody clause)
  codeVariableCount code === max 1 (clauseNVars clause)
  codeSlotCount code === length (codeInstructions code)
  map destination (codeInstructions code) === [0 .. codeSlotCount code - 1]
  map (observe . bodyTemplate) (codeBody code) === map observe (clauseBody clause)
  map (Just . bodyKey) (codeBody code) === map functorOf (clauseBody clause)

unit :: PropertyT IO () -> Property
unit = withTests 1 . property

prop_control_and_nested_cuts_fall_back :: Property
prop_control_and_nested_cuts_fall_back = unit $ do
  forM_
    [ ",", ";", "->", "call", "once", "not", "findall", "forall", "minimize",
      "phrase", "emit", "phrase_from_file", "!", "$cut"
    ] $ \name ->
      assert (isNothing (compileClause (Clause (Atom "p") [Compound name []] 0)))
  forM_ [Atom "!", Compound "$cut" [IntLit 42]] $ \cut ->
    forM_ [cut, Compound "helper" [Compound "box" [cut]], Compound "unify" [Var 0, cut]] $ \goal ->
      assert (isNothing (compileClause (Clause (Compound "p" [Var 0]) [goal] 1)))

prop_malformed_variables_and_uncallable_goals_fall_back :: Property
prop_malformed_variables_and_uncallable_goals_fall_back = unit $ do
  forM_
    [ Clause (Atom "p") [] (-1),
      Clause (Compound "p" [Var (-1)]) [] 1,
      Clause (Compound "p" [Var 1]) [] 1,
      Clause (Atom "p") [Compound "helper" [Var 0]] 0,
      Clause (Var 0) [] 1,
      Clause (IntLit 1) [] 0
    ] $ \clause -> assert (isNothing (compileClause clause))
  forM_ [Var 0, IntLit 1, FloatLit 1.5, StrLit "helper", CharLit 'x'] $ \goal ->
    assert (isNothing (compileClause (Clause (Compound "p" [Var 0]) [goal] 1)))

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

compileGroup :: Group
compileGroup = Group "clause compiler"
  [ ("generated_register_program_preserves_raw_clause", prop_generated_register_program_preserves_raw_clause),
    ("control_and_nested_cuts_fall_back", prop_control_and_nested_cuts_fall_back),
    ("malformed_variables_and_uncallable_goals_fall_back", prop_malformed_variables_and_uncallable_goals_fall_back),
    ("first_order_data_and_scalar_identities_remain_distinct", prop_first_order_data_and_scalar_identities_remain_distinct)
  ]

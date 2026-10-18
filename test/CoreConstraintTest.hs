{-# LANGUAGE OverloadedStrings #-}
module CoreConstraintTest (coreConstraintGroup) where

import Control.Monad (forM_)
import qualified Data.IntMap.Strict as IM
import Data.List (sort)
import Hedgehog hiding (Var)
import qualified Hedgehog.Gen as Gen
import qualified Hedgehog.Range as Range
import Infera hiding (Answer, solveQuery)
import qualified Infera.Core.Run as Run
import Infera.Engine.Alpha (alphaBindings, alphaOutput, alphaText)
import qualified Infera.Engine.Reference as Reference

data Event = Answer [(String, Term)] [String] String
  | Problem String | Exhausted | Cut Int | Incomplete Term
  deriving (Eq, Show)

observe :: Query -> Search -> [Event]
observe query = map event
  where
    event (Found state) = let answer = projectAnswer query state in
      Answer (alphaBindings (queryNVars query) (answerBindings answer)) (answerResiduals answer) (alphaOutput (answerOutput answer))
    event (BranchError err) = Problem (alphaText (show err))
    event BranchExhausted = Exhausted
    event (CutMarker owner) = Cut owner
    event (ConsumedIncomplete key) = Incomplete key

native :: Int -> Program -> Query -> IO Search
native limit program query = do
  (_, first) <- Run.runCoreWith limit program query
  let drain action = do
        step <- action
        case step of
          Run.Stop -> pure []
          Run.Yield item next -> (item :) <$> drain next
          Run.Abandon reason -> fail ("native CLP abandoned: " ++ reason)
  drain first

parity :: Bool -> Program -> Query -> PropertyT IO Search
parity completeStore program query = do
  let expected = Reference.solveQuery program query
  results <- evalIO (native 1 program query)
  observe query results === observe query expected
  ordinary <- evalIO (native 32768 program query)
  observe query ordinary === observe query expected
  if completeStore then
    [ssStore state | Found state <- results] === [ssStore state | Found state <- expected]
    else pure ()
  pure results

prop_generated_labeling :: Property
prop_generated_labeling = withTests 100 . property $ do
  maximum' <- forAll (Gen.int (Range.linear 0 6))
  threshold <- forAll (Gen.int (Range.linear 0 12))
  let source = "[X, Y] in 0.." ++ show maximum' ++ ", X + Y #<= " ++ show threshold ++ ", label [X, Y]?"
  program <- evalEither (loadProgramText "<- notable.")
  query <- evalEither (parseQuery source)
  results <- parity True program query
  let values = [(x, y) | Found state <- results,
        let bindings = answerBindings (projectAnswer query state),
        Just (IntLit x) <- [lookup "X" bindings], Just (IntLit y) <- [lookup "Y" bindings]]
      model = [(toInteger x, toInteger y) | x <- [0 .. maximum'], y <- [0 .. maximum'], x + y <= threshold]
  -- First-fail can change the Cartesian enumeration order, but not its set.
  sort values === sort model

prop_generated_optima :: Property
prop_generated_optima = withTests 100 . property $ do
  maximum' <- forAll (Gen.int (Range.linear 1 5))
  coefficient <- forAll (Gen.int (Range.linear (-2) 3))
  let source = "[X, Y] in 0.." ++ show maximum' ++ ", C #= " ++ show coefficient ++ " * X + Y, labeling [min C] [X, Y]?"
  program <- evalEither (loadProgramText "<- notable.")
  query <- evalEither (parseQuery source)
  results <- parity True program query
  let costs = [cost | Found state <- results, Just (IntLit cost) <- [lookup "C" (answerBindings (projectAnswer query state))]]
      optimum = minimum [toInteger (coefficient * x + y) | x <- [0 .. maximum'], y <- [0 .. maximum']]
  costs === [optimum]

prop_boundaries :: Property
prop_boundaries = withTests 1 . property $ do
  program <- evalEither (loadProgramText "<- notable. pause.")
  forM_
    [ "label X?", "label [a, X | Tail]?", "label [X]?",
      "X in 1..3, Y = X, label [Y, X, Y], pause?",
      "X in 1..3, (label [X], pause ; X = 9), pause?",
      "X in 1..3, findall X (label [X], pause) L?",
      "X in 1..3, once (label [X]), pause?",
      "X in 1..3, not (label [X], X = 4), pause?",
      "X in 1..3, labeling [min X] [X | Tail]?",
      "X in 1..3, labeling [min X] [a]?",
      "X in 1..3, labeling [min Cost] [X]?",
      "X in 1..3, labeling [min 1.5] [X]?",
      "X in 1..3, labeling [max X] [X]?",
      "X in 1..3, labeling [min (1 / 0)] [X]?",
      "X in 0..2, Y #= 1 / (X * (X - 1)), labeling [min X] [X, Y]?",
      "X in 1..3, C #= (0 - X), (labeling [min C] [X], pause ; X = 8)?",
      "X in 1..3, Y in 1..3, X != Y, label [X, Y], pause?",
      "X in 0..3, reify (X #> 1) B, label [X], pause?",
      "[X, Y] in 0..2, all_different [X, Y], labeling [min X] [X, Y], pause?"
    ] $ \text -> do
      annotate text
      query <- evalEither (parseQuery text)
      _ <- parity False program query
      pure ()

prop_fixture :: Property
prop_fixture = withTests 1 . property $ do
  loaded <- evalIO (loadFile "test/core/parity-native-clp.nprolog")
  (program, queries) <- evalEither loaded
  forM_ queries $ \query -> do
    annotate (show (queryGoals query))
    _ <- parity False program query
    pure ()

prop_residual_store :: Property
prop_residual_store = withTests 1 . property $ do
  program <- evalEither (loadProgramText "<- notable.")
  forM_ ["[X, Y] in 0..4, X #< Y?", "X != Y?", "X #= Y, Y in 1..3?",
    "X in 0..2, reify (X #= 1) B?", "all_different [X, Y]?", "X #= 999999999999999999999999999?"] $ \text -> do
      query <- evalEither (parseQuery text)
      results <- parity True program query
      forM_ [ssStore state | Found state <- results] $ \store ->
        assert (all (>= 0) (IM.keys (stSubst store)))

coreConstraintGroup :: Group
coreConstraintGroup = Group "native core constraints and labeling"
  [ ("generated labeling matches reference and independent grid", prop_generated_labeling),
    ("generated optimization retains exact first optimum and store", prop_generated_optima),
    ("labeling boundaries controls errors and rollback", prop_boundaries),
    ("native constraint fixture", prop_fixture),
    ("residual stores retain every scheduler field", prop_residual_store)
  ]

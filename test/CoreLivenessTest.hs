{-# LANGUAGE OverloadedStrings #-}

module CoreLivenessTest (coreLivenessGroup) where

import Control.Monad (forM_)
import Control.Exception (evaluate)
import qualified Data.IntMap.Strict as IM
import Hedgehog hiding (Var)
import qualified Hedgehog.Gen as Gen
import qualified Hedgehog.Range as Range
import Infera hiding (Answer, solveQuery)
import qualified Infera.CLP as CLP
import qualified Infera.Core as Core
import qualified Infera.Core.Run as Run
import qualified Infera.Core.Store as Store
import Infera.Engine.Alpha (alphaOutput, alphaTerms, alphaText)
import qualified Infera.Engine.Reference as Reference

unit :: PropertyT IO () -> Property
unit = withTests 1 . property

data Observation
  = Answer [Term] [String] String
  | Problem String
  | Other String
  deriving (Eq, Show)

-- Compare projected heap terms as well as their rendered residuals,
-- up to a consistent renaming of the internal variables of each answer;
-- rendering alone could hide a wrongly shared variable.
observed :: Query -> Search -> [Observation]
observed query = map item
  where
    item (Found state) =
      let subst = CLP.stSubst (ssStore state)
          answer = Reference.projectAnswer query state
       in Answer (alphaTerms (queryNVars query) [deepWalk subst (Var v) | v <- [0 .. queryNVars query - 1]])
            (Reference.answerResiduals answer) (alphaOutput (ssOutput state))
    item (BranchError problem) = Problem (alphaText (show problem))
    item BranchExhausted = Other "exhausted"
    item (CutMarker owner) = Other ("cut " ++ show owner)
    item (ConsumedIncomplete key) = Other ("incomplete " ++ show key)

direct :: Int -> Program -> Query -> IO Search
direct limit program query = do
  (_, first) <- Run.runCoreWith limit program query
  drain first
  where
    drain action = do
      step <- action
      case step of
        Run.Stop -> pure []
        Run.Yield item next -> (item :) <$> drain next
        Run.Abandon reason -> fail reason

prop_fixture :: Property
prop_fixture = unit $ do
  loaded <- evalIO (loadFile "test/core/parity-liveness.nprolog")
  (program, queries) <- evalEither loaded
  forM_ queries $ \query -> do
    annotate (show (queryGoals query))
    let reference = observed query (Reference.solveQuery program query)
    forM_ [1, 16, Store.initialCollectLimit] $ \limit -> do
      annotate ("collection limit " ++ show limit)
      items <- evalIO (direct limit program query)
      observed query items === reference

prop_generated_slots :: Property
prop_generated_slots = withTests 100 . property $ do
  size <- forAll (Gen.int (Range.linear 1 24))
  at <- forAll (Gen.int (Range.linear 0 (size - 1)))
  let names = ["X" ++ show i | i <- [0 .. size - 1]]
      fields = unwords names
      source = unlines
        [ "<- notable.", "pause.", "choose a.", "choose b.",
          "p Out <- Junk = (wide " ++ fields ++ "), pause, Out = (pair " ++ names !! at ++ " " ++ names !! at ++ "), pause, (choose " ++ names !! at ++ " ; pause), pause."
        ]
  program <- evalEither (loadProgramText source)
  query <- evalEither (parseQuery "p Out?")
  let expected = observed query (Reference.solveQuery program query)
  items <- evalIO (direct 1 program query)
  observed query items === expected

prop_retained_answers :: Property
prop_retained_answers = unit $ do
  loaded <- evalIO (loadFile "test/core/parity-liveness.nprolog")
  (program, _) <- evalEither loaded
  query <- evalEither (parseQuery "branch Out?")
  other <- evalEither (parseQuery "constraint_undo Out?")
  items <- case Core.solveQueryWith 1 program query of
    Just stream -> pure stream
    Nothing -> annotate "core rejected the retained-answer query" >> failure
  another <- case Core.solveQueryWith 1 program other of
    Just stream -> pure stream
    Nothing -> annotate "core rejected the interleaved query" >> failure
  let first = take 1 (observed query items)
  saved <- evalIO (evaluate (length (show first)))
  assert (saved > 0)
  observed other another === observed other (Reference.solveQuery program other)
  observed query items === observed query (Reference.solveQuery program query)
  first === take 1 (observed query items)

prop_sparse_identity_rollback :: Property
prop_sparse_identity_rollback = unit $ do
  result <- evalIO $ do
    symbols <- Store.newSymbols
    store <- Store.newStore symbols
    _ <- Store.allocCells store 3
    Store.replaceLogicalIds store 3 (IM.fromList [(0, 101), (1, 203), (2, 307)])
    Store.setFreshId store 308
    first <- mapM (Store.logicalId store) [0 .. 2]
    -- Names above a rolled-back heap top are forgotten; fresh slots are
    -- unnamed until something names them.
    Store.setHeapTop store 1
    slot <- Store.allocSlots store 2
    named <- Store.nameCell store slot
    second <- mapM (Store.logicalId store) [0, slot, slot + 1]
    -- The fresh counter never moves back: a later name is new.
    Store.setHeapTop store 0
    _ <- Store.allocCells store 2
    again <- Store.nameCell store 1
    third <- mapM (Store.logicalId store) [0, 1]
    pure (first, named, second, again, third)
  result === ([Just 101, Just 203, Just 307], 308, [Just 101, Just 308, Nothing], 309, [Nothing, Just 309])

prop_dead_graph_reclaimed :: Property
prop_dead_graph_reclaimed = unit $ do
  loaded <- evalIO (loadFile "test/core/parity-liveness.nprolog")
  (program, _) <- evalEither loaded
  forM_ [100, 300] $ \size -> do
    query <- evalEither (parseQuery ("dead_sibling " ++ show size ++ " Out, churn 4000?"))
    (items, (collections, live, reclaimed)) <- evalIO $ do
      (_, first, stats) <- Run.runCoreWithStats 1 program query
      let drain action = do
            step <- action
            case step of
              Run.Stop -> pure []
              Run.Yield item next -> (item :) <$> drain next
              Run.Abandon reason -> fail reason
      items <- drain first
      counters <- stats
      pure (items, counters)
    map (Reference.showAnswer . Reference.projectAnswer query) [state | Found state <- items] === ["Out = done"]
    annotateShow (size, collections, live, reclaimed)
    assert (collections > 1)
    -- A whole retained activation would keep Junk's 3*size list cells.
    -- The suspended use of Out now retains only its own cell/aliases.
    assert (live < 64)
    assert (reclaimed > 3 * size)

coreLivenessGroup :: Group
coreLivenessGroup = Group "core activation liveness"
  [ ("fixture", prop_fixture),
    ("generated_slots", prop_generated_slots),
    ("retained_answers", prop_retained_answers),
    ("sparse_identity_rollback", prop_sparse_identity_rollback),
    ("dead_graph_reclaimed", prop_dead_graph_reclaimed)
  ]

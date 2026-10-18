{-# LANGUAGE OverloadedStrings #-}

-- Selection may reject only a proven failure. Its ordered stream must agree
-- with ordinary, unindexed execution, including errors and fresh variables.
module CoreDecisionTest (coreDecisionGroup) where

import Control.Monad (forM_, unless)
import Data.IORef
import qualified Data.IntMap.Strict as IM
import qualified Data.Map.Strict as Map
import Hedgehog hiding (Var)
import qualified Hedgehog.Gen as Gen
import qualified Hedgehog.Range as Range
import Infera hiding (solveQuery)
import qualified Infera.Core as Core
import qualified Infera.Core.Compile as Compile
import qualified Infera.Core.Store as Store
import qualified Infera.Engine.Reference as Reference

data Observed = Observed [String] [String] Bool [Int] deriving (Eq, Show)

observe :: Query -> Search -> Observed
observe query items =
  let summary = summarizeSearch query items
   in Observed
        [showAnswer answer ++ concatMap renderOutputEvent (reverse (answerOutput answer))
          | answer <- summaryAnswers summary]
        (map showSolveError (summaryErrors summary))
        (summaryExhausted summary)
        [Reference.ssFresh state | Reference.Found state <- items]

programOf :: String -> PropertyT IO Program
programOf = either (\err -> annotate err >> failure) pure . loadProgramText

queryOf :: String -> PropertyT IO Query
queryOf = either (\err -> annotate err >> failure) pure . parseQuery

assertParity :: Program -> Program -> Query -> PropertyT IO ()
assertParity indexed unindexed query = do
  let expected = observe query (Reference.solveQuery unindexed query)
  observe query (Reference.solveQuery indexed query) === expected
  forM_ [indexed, unindexed] $ \program -> do
    case Core.solveQuery program query of
      Nothing -> failure
      Just items -> observe query items === expected
    case Core.solveQueryWith 1 program query of
      Nothing -> failure
      Just items -> observe query items === expected
    outcome <- evalIO (Core.coreOutcome program query)
    case outcome of
      Left reason -> annotate reason >> failure
      Right _ -> pure ()

selected :: Program -> PredKey -> [Term] -> Bool -> PropertyT IO [Int]
selected program key args constrained = evalIO $ do
  symbols <- Store.newSymbols
  store <- Store.newStore symbols
  let query = Query [] [] 0
  compiled <- Compile.compileProgram store program query
  case compiled of
    Left reason -> fail (show reason)
    Right code -> do
      predicate <- readIORef (Compile.cpPreds code Map.! key)
      vars <- newIORef IM.empty
      forM_ (zip [0 ..] args) $ \(i, term) -> Store.importTerm store vars term >>= Store.writeArg store i
      Store.writeReg store Store.rCLP (if constrained then 1 else 0)
      Compile.candidateClauses store predicate

pathSource :: String
pathSource = unlines
  [ "<- notable.",
    "pick : nondet (any) (any) (any).",
    "pick (box (tag a)) left alpha.",
    "pick (box (tag a)) right beta.",
    "pick (box (tag b)) right gamma.",
    "pick (box (pair a b)) right pair.",
    "pick (box (tag a b)) right arity.",
    "pick X right open.",
    "pick (box (tag X)) S fallback."
  ]

prop_compiled_paths :: Property
prop_compiled_paths = withTests 1 . property $ do
  program <- programOf pathSource
  plain <- programOf ("<- noindex.\n" ++ pathSource)
  let nested term = Compound "box" [Compound "tag" [term]]
      args = [nested (Atom "a"), Atom "right", Var 0]
  selected program ("pick", 3) args False >>= (=== [1, 5, 6])
  selected program ("pick", 3) [nested (Var 1), Atom "right", Var 0] False >>= (=== [1, 2, 5, 6])
  -- Constraints keep the established principal-key decisions, without
  -- crossing any additional head bindings or leading body guards.
  selected program ("pick", 3) args True >>= (=== [1, 2, 3, 4, 5, 6])
  selected plain ("pick", 3) args False >>= (=== [0 .. 6])
  forM_ ["pick (box (tag a)) right R?", "pick (box (tag X)) right R?",
      "pick (box (tag a b)) right R?", "pick X right R?", "pick X X R?"] $ \source ->
    queryOf source >>= assertParity program plain

prop_generated_guards :: Property
prop_generated_guards = withTests 100 . property $ do
  n <- forAll (Gen.int (Range.constant (-20) 20))
  cuts <- forAll (Gen.list (Range.constant 2 8) (Gen.int (Range.constant (-15) 15)))
  let source = unlines
        (["<- notable.", "choose : nondet (any) (any)."] ++
          ["choose N R <- N < (" ++ show cutoff ++ "), R = k" ++ show i ++ "."
            | (i, cutoff) <- zip [0 :: Int ..] cuts])
  program <- programOf source
  plain <- programOf ("<- noindex.\n" ++ source)
  selected program ("choose", 2) [IntLit (toInteger n), Var 0] False
    >>= (=== [i | (i, cutoff) <- zip [0 ..] cuts, n < cutoff])
  selected program ("choose", 2) [IntLit (toInteger n), Var 0] True >>= (=== [0 .. length cuts - 1])
  query <- queryOf ("choose (" ++ show n ++ ") R?")
  assertParity program plain query

prop_generated_patterns :: Property
prop_generated_patterns = withTests 100 . property $ do
  tag <- forAll (Gen.element ["a", "b", "c"])
  side <- forAll (Gen.element ["left", "right"])
  free <- forAll Gen.bool
  let source = unlines
        (["<- notable.", "lookup : nondet (any) (any) (any)."] ++
          ["lookup (box (tag " ++ k ++ ")) " ++ s ++ " (answer " ++ k ++ " " ++ s ++ ")."
            | k <- ["a", "b", "c"], s <- ["left", "right"]] ++
          ["lookup X right open.", "lookup (box X) Y fallback."])
  program <- programOf source
  plain <- programOf ("<- noindex.\n" ++ source)
  query <- queryOf ("lookup (box (tag " ++ (if free then "K" else tag) ++ ")) " ++ side ++ " R?")
  assertParity program plain query

prop_scalar_decisions :: Property
prop_scalar_decisions = withTests 1 . property $ do
  let source = unlines
        ["<- notable.", "scalar : nondet (any) (any).",
         "scalar (box 0.0) zero.", "scalar (box (-0.0)) negative_zero.",
         "scalar (box 1152921504606846976) big.", "scalar (box \"text\") string.",
         "scalar (box 'x') character.", "scalar X open."]
  program <- programOf source
  plain <- programOf ("<- noindex.\n" ++ source)
  forM_ ["scalar (box 0.0) R?", "scalar (box (-0.0)) R?",
      "scalar (box 1152921504606846976) R?", "scalar (box \"text\") R?",
      "scalar (box 'x') R?", "scalar (box X) R?"] $ \sourceQuery ->
    queryOf sourceQuery >>= assertParity program plain
  selected program ("scalar", 2) [Compound "box" [FloatLit (0 / 0)], Var 0] False >>= (=== [0 .. 5])

prop_fixture :: Property
prop_fixture = withTests 1 . property $ do
  loaded <- evalIO (loadFile "test/core/parity-decisions.nprolog")
  case loaded of
    Left err -> annotate err >> failure
    Right (program, queries) -> do
      unless (not (null queries)) failure
      forM_ queries $ \query -> do
        annotate (show (queryGoals query))
        assertParity program program query

coreDecisionGroup :: Group
coreDecisionGroup = Group "compiled clause decisions"
  [("compiled_paths", prop_compiled_paths), ("generated_guards", prop_generated_guards),
   ("generated_patterns", prop_generated_patterns), ("scalar_decisions", prop_scalar_decisions),
   ("decision_fixture", prop_fixture)]

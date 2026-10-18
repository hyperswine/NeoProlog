{-# LANGUAGE OverloadedStrings #-}

-- | Ordered parity against an explicitly disabled delta evaluator, with a
-- separate graph-closure oracle. A leading true preserves logical execution
-- while making every self-recursive rule fail the fast-path proof.
module CoreDeltaTest (coreDeltaGroup) where

import Control.Monad (forM_)
import qualified Data.IntMap.Strict as IM
import Data.List (sort)
import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import Hedgehog hiding (Var, check)
import qualified Hedgehog.Gen as Gen
import qualified Hedgehog.Range as Range
import Infera hiding (solveQuery)
import qualified Infera.Core as Core
import qualified Infera.Core.Delta as Delta
import Infera.Engine.Alpha (alphaOutput, alphaText)
import qualified Infera.Engine.Reference as Reference

unit :: PropertyT IO () -> Property
unit = withTests 1 . property

legacyTables :: Program -> Program
legacyTables program = program {progPreds = Map.map disable (progPreds program)}
  where
    disable predicate = predicate {predClauses = IM.map prefix (predClauses predicate)}
    prefix clause = clause {clauseBody = Atom "true" : clauseBody clause}

type Observation = ([(String, String)], [String], Bool)

observe :: Query -> Reference.Search -> Observation
observe query items =
  let summary = summarizeSearch query items
   in ([(alphaText (showAnswer answer), alphaOutput (answerOutput answer)) | answer <- summaryAnswers summary],
       map (alphaText . showSolveError) (summaryErrors summary), summaryExhausted summary)

compareTables :: String -> String -> PropertyT IO QuerySummary
compareTables source text = do
  annotate source
  annotate text
  program <- evalEither (loadProgramText source)
  query <- evalEither (parseQuery text)
  let legacy = legacyTables program
      expected = observe query (Reference.solveQuery legacy query)
  case (Core.solveQuery program query, Core.solveQuery legacy query, Core.solveQueryWith 1 program query) of
    (Just items, Just full, Just collected) -> do
      observe query items === expected
      observe query full === expected
      observe query collected === expected
      pure (summarizeSearch query items)
    _ -> failure

node :: Int -> String
node n = "n" ++ show n

closure :: [(Int, Int)] -> Int -> [Term]
closure edges start = map (Atom . node) . Set.toAscList $ settle Set.empty
  where
    settle reached =
      let next = Set.union reached (Set.fromList [b | (a, b) <- edges, a == start || Set.member a reached])
       in if next == reached then reached else settle next

prop_graph_closure :: Property
prop_graph_closure = withTests 200 . property $ do
  size <- forAll (Gen.int (Range.linear 1 7))
  edges <- forAll (Gen.subsequence [(a, b) | a <- [0 .. size - 1], b <- [0 .. size - 1]])
  start <- forAll (Gen.int (Range.linear 0 (size - 1)))
  recursiveFirst <- forAll Gen.bool
  duplicate <- forAll Gen.bool
  indexed <- forAll Gen.bool
  let facts = ["edge " ++ node a ++ " " ++ node b ++ "." | (a, b) <- edges]
      base = "path X Y <- edge X Y."
      recursive = "path X Y <- path X Z, edge Z Y."
      source = unlines ([if indexed then "<- index." else "<- noindex.", "edge _ _ <- fail."]
        ++ facts ++ [fact | duplicate, fact <- facts]
        ++ if recursiveFirst then [recursive, base] else [base, recursive])
  classify "cyclic graph" (any (uncurry (==)) edges)
  classify "duplicate derivations" duplicate
  summary <- compareTables source ("path " ++ node start ++ " Result?")
  sort [term | answer <- summaryAnswers summary, Just term <- [lookup "Result" (answerBindings answer)]]
    === sort (closure edges start)
  summaryErrors summary === []
  summaryExhausted summary === False

prop_multiple_rules :: Property
prop_multiple_rules = withTests 100 . property $ do
  size <- forAll (Gen.int (Range.linear 1 5))
  red <- forAll (Gen.subsequence [(a, b) | a <- [0 .. size - 1], b <- [0 .. size - 1]])
  blue <- forAll (Gen.subsequence [(a, b) | a <- [0 .. size - 1], b <- [0 .. size - 1]])
  let source = unlines (["red _ _ <- fail.", "blue _ _ <- fail."]
        ++ ["red " ++ node a ++ " " ++ node b ++ "." | (a, b) <- red]
        ++ ["blue " ++ node a ++ " " ++ node b ++ "." | (a, b) <- blue]
        ++ ["path X Y <- path X Z, red Z Y.", "path X Y <- red X Y.",
            "path X Y <- path X Z, blue Z Y.", "path X Y <- blue X Y."])
      expected = sort ["From = " ++ node a ++ ", To = " ++ show term | a <- [0 .. size - 1], term <- closure (red ++ blue) a]
  summary <- compareTables source "path From To?"
  sort (map showAnswer (summaryAnswers summary)) === expected
  summaryErrors summary === []
  summaryExhausted summary === False

prop_open_and_shared_answers :: Property
prop_open_and_shared_answers = unit $ do
  let source = unlines
        ["p Pair Y <- p Pair Z, step Z Y.", "p (pair a a) first.", "p (pair X X) open.",
         "step first second.", "step open shared.", "step second third."]
  forM_ ["p (pair X X) Result?", "p (pair X Y) Result?", "Pair = pair X Y, X = Y, p Pair Result?", "p (pair a X) Result?"] $ \text -> do
    summary <- compareTables source text
    [term | answer <- summaryAnswers summary, Just term <- [lookup "Result" (answerBindings answer)]]
      === map Atom ["first", "open", "second", "shared", "third"]
  open <- compareTables (unlines ["p X Y <- p X Z, relation Z Y.", "p seed X.", "relation left right.", "relation right done."])
    "p seed Result?"
  map showAnswer (summaryAnswers open) === ["true.", "Result = right", "Result = done"]

prop_proof_boundary :: Property
prop_proof_boundary = unit $ do
  let check source expected = do
        program <- evalEither (loadProgramText source)
        predicate <- maybe failure pure (lookupPred ("p", 1) program)
        Delta.recursiveClauses program predicate (Compound "p" [Var 0]) === expected
      accepted = unlines ["p X <- p Y, step Y X.", "p first.", "step first second.", "step second third."]
  check accepted (Just [0])
  forM_ ["p X <- true, p X. p first.",
         "p X <- p Y, p X. p first.",
         "p X <- p Y, not (step Y X). p first. step a b.",
         "p X <- p Y, X #= Y. p 1.",
         "p X <- p Y, step Y X. p first. step X X <- p X.",
         "p : semidet (atom: <=>). p X <- p X. p first.",
         "p : table unsafe. p X <- p Y, write Y, X = Y. p first.",
         "p X <- p Y, step Y X. p first. step : dynamic. step a b.",
         "p X <- p Y, step Y X. p first. step : semidet (atom: =>) (atom: <=). step a b."]
    (`check` Nothing)
  program <- evalEither (loadProgramText "p X Y <- p Y X. p a b.")
  predicate <- maybe failure pure (lookupPred ("p", 2) program)
  Delta.recursiveClauses program predicate (Compound "p" [Atom "a", Var 0]) === Nothing

prop_fallback_observations :: Property
prop_fallback_observations = unit $ do
  forM_ [("p X <- q X. q X <- p X. p first. q second.", "p Result?"),
         ("path X Y <- path X Z, path Z Y. path a b. path b c.", "path a Result?"),
         ("path X Y <- edge X Z, path Z Y. path X Y <- edge X Y. edge a b. edge b c.", "path a Result?"),
         ("p X <- p Y, X #= Y, X in 0..2. p 1.", "p Result?"),
         ("p : semidet (atom: <=>). p X <- p X. p first. p second.", "p Result?"),
         ("p X <- p X. p answer. p X <- missing X.", "p Result?"),
         ("p : table unsafe. p X <- p Y, X = Y. p answer <- write seen.", "p Result?"),
         ("p : table unsafe. p X <- p Y, !, X = Y. p first. p second.", "p Result?")]
    (\(source, text) -> () <$ compareTables source text)

prop_iteration_exhaustion :: Property
prop_iteration_exhaustion = unit $ do
  summary <- compareTables "p : table. p (next X) <- p X. p zero." "p Result?"
  summaryExhausted summary === True
  length (summaryAnswers summary) === Reference.maxTableIterations + 1

-- The facade can replay through the legacy machine when a construct is
-- unsupported. Check this acceptance query by draining the core directly,
-- so passing ordered parity cannot hide such a replay.
prop_native_path :: Property
prop_native_path = unit $ do
  program <- evalEither (loadProgramText (unlines
    ["path X Y <- path X Z, edge Z Y.", "path X Y <- edge X Y.",
     "edge a b.", "edge b c.", "edge c d."]))
  query <- evalEither (parseQuery "findall X (path a X) L, path a b, not (path d a)?")
  Core.coreSupports program query === Nothing
  outcome <- evalIO (Core.coreOutcome program query)
  outcome === Right 1

coreDeltaGroup :: Group
coreDeltaGroup = Group "core incremental tabling"
  [("generated graph closure with ordered full-fixpoint parity", prop_graph_closure),
   ("generated multiple rules and open variants", prop_multiple_rules),
   ("open answers and structured aliases survive collection", prop_open_and_shared_answers),
   ("delta proof excludes contracts effects CLP and unsafe recursion", prop_proof_boundary),
   ("full fixpoint fallback keeps errors output cut and dependencies", prop_fallback_observations),
   ("iteration exhaustion keeps the final answer batch", prop_iteration_exhaustion),
   ("delta acceptance runs entirely on core", prop_native_path)]

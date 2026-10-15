{-# LANGUAGE OverloadedStrings #-}

-- The general linear-table evaluator is retained as the reference. An inert
-- leading true makes a recursive clause ineligible for answer-batch evaluation
-- without changing its logical answers, clause order, effects or resolution
-- depth. Graph closure supplies a separate, non-engine answer-set oracle.
module TablingTest (tablingGroup) where

import Data.List (sort)
import qualified Data.IntMap.Strict as IM
import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import Hedgehog hiding (Var)
import qualified Hedgehog.Gen as Gen
import qualified Hedgehog.Range as Range
import Infera

unit :: PropertyT IO () -> Property
unit = withTests 1 . property

legacyTables :: Program -> Program
legacyTables program = program {progPreds = Map.map disable (progPreds program)}
  where
    disable predicate = predicate
      {predClauses = IM.map prefix (predClauses predicate)}
      where
        prefix clause = clause {clauseBody = Atom "true" : clauseBody clause}

type Observation = ([(String, [OutputEvent])], [SolveError], Bool)

observe :: QuerySummary -> Observation
observe summary =
  ([(showAnswer answer, answerOutput answer) | answer <- summaryAnswers summary],
   map normalize (summaryErrors summary), summaryExhausted summary)
  where
    normalize (InstantiationError term) = InstantiationError (canonical term)
    normalize (CLPTypeError term) = CLPTypeError (canonical term)
    normalize (TypeError description term) = TypeError description (canonical term)
    normalize err = err
    canonical = fst . canonicalize emptySubst

compareTables :: String -> String -> PropertyT IO QuerySummary
compareTables source text = do
  annotate source
  program <- evalEither (loadProgramText source)
  query <- evalEither (parseQuery text)
  let actual = solveAll program query
  observe actual === observe (solveAll (legacyTables program) query)
  pure actual

node :: Int -> String
node value = "n" ++ show value

closure :: [(Int, Int)] -> Int -> [Term]
closure edges start = map (Atom . node) . Set.toAscList $
  settle (Set.fromList [b | (a, b) <- edges, a == start])
  where
    settle reached =
      let next = Set.union reached (Set.fromList [b | (a, b) <- edges, Set.member a reached])
       in if next == reached then reached else settle next

prop_delta_graph_closure :: Property
prop_delta_graph_closure = withTests 300 . property $ do
  size <- forAll (Gen.int (Range.linear 1 7))
  edges <- forAll (Gen.subsequence [(a, b) | a <- [0 .. size - 1], b <- [0 .. size - 1]])
  start <- forAll (Gen.int (Range.linear 0 (size - 1)))
  recursiveFirst <- forAll Gen.bool
  duplicateFacts <- forAll Gen.bool
  let recursive = "path X Y <- path X Z, edge Z Y."
      base = "path X Y <- edge X Y."
      facts = ["edge " ++ node a ++ " " ++ node b ++ "." | (a, b) <- edges]
      source = unlines $
        ["edge _ _ <- fail."] ++ facts ++ [fact | duplicateFacts, fact <- facts]
        ++ if recursiveFirst then [recursive, base] else [base, recursive]
  classify "cycle" (any (uncurry (==)) edges)
  classify "duplicate edge facts" duplicateFacts
  summary <- compareTables source ("path " ++ node start ++ " Target?")
  let actual = [term | answer <- summaryAnswers summary,
                      Just term <- [lookup "Target" (answerBindings answer)]]
  sort actual === sort (closure edges start)
  summaryErrors summary === []
  summaryExhausted summary === False

prop_delta_multiple_rules_and_variants :: Property
prop_delta_multiple_rules_and_variants = withTests 150 . property $ do
  size <- forAll (Gen.int (Range.linear 1 5))
  red <- forAll (Gen.subsequence [(a, b) | a <- [0 .. size - 1], b <- [0 .. size - 1]])
  blue <- forAll (Gen.subsequence [(a, b) | a <- [0 .. size - 1], b <- [0 .. size - 1]])
  let source = unlines $
        ["red _ _ <- fail.", "blue _ _ <- fail."]
        ++ ["red " ++ node a ++ " " ++ node b ++ "." | (a, b) <- red]
        ++ ["blue " ++ node a ++ " " ++ node b ++ "." | (a, b) <- blue]
        ++ ["path X Y <- path X Z, red Z Y.",
            "path X Y <- red X Y.",
            "path X Y <- path X Z, blue Z Y.",
            "path X Y <- blue X Y."]
      expected = sort ["From = " ++ node a ++ ", To = " ++ show term
                      | a <- [0 .. size - 1], term <- closure (red ++ blue) a]
  summary <- compareTables source "path From To?"
  sort (map showAnswer (summaryAnswers summary)) === expected
  summaryErrors summary === []
  summaryExhausted summary === False

prop_delta_open_answers :: Property
prop_delta_open_answers = unit $ do
  summary <- compareTables (unlines
    ["p X Y <- p X Z, relation Z Y.",
     "p seed X.",
     "relation left right.",
     "relation right done."]) "p seed Result?"
  map showAnswer (summaryAnswers summary) === ["true.", "Result = right", "Result = done"]

prop_delta_index_policies :: Property
prop_delta_index_policies = unit $ do
  mapM_ (\indexed -> do
      let source = unlines
            [if indexed then "<- index." else "<- noindex.",
             "edge a b.", "edge b c.", "edge c d.", "edge a c.",
             "path X Y <- path X Z, edge Z Y.", "path X Y <- edge X Y."]
      program <- evalEither (loadProgramText source)
      case lookupPred ("path", 2) program of
        Just predicate -> predIsIndexed program predicate === indexed
        Nothing -> failure
      summary <- compareTables source "path a Result?"
      map showAnswer (summaryAnswers summary) === ["Result = b", "Result = c", "Result = d"]
      summaryErrors summary === []
      summaryExhausted summary === False
    ) [False, True]

prop_delta_structured_aliases :: Property
prop_delta_structured_aliases = unit $ do
  let source = unlines
        ["p Pair Y <- p Pair Z, step Z Y.",
         "p (pair a a) first.", "p (pair X X) open.",
         "step first second.", "step open shared.", "step second third."]
  -- The self-call retains each structured variant exactly. Include an open
  -- answer whose repeated variable aliases query fields, plus a query alias
  -- already established before the table is entered.
  mapM_ (\text -> do
      summary <- compareTables source text
      [term | answer <- summaryAnswers summary,
              Just term <- [lookup "Result" (answerBindings answer)]] ===
        map Atom ["first", "open", "second", "shared", "third"]
      summaryErrors summary === []
      summaryExhausted summary === False
    ) ["p (pair X X) Result?", "p (pair X Y) Result?",
       "Pair = pair X Y, X = Y, p Pair Result?", "p (pair a X) Result?"]

prop_delta_inferred_suffix_contract :: Property
prop_delta_inferred_suffix_contract = unit $ do
  let source = unlines
        ["p X Y <- p X Z, step Z Y.", "p root a.",
         "step a b.", "step b c.", "step c d.", "step d d."]
  program <- evalEither (loadProgramText source)
  case lookupPred ("step", 2) program of
    Just predicate -> do
      predDecls predicate === []
      sigDet (predInferred predicate) === Semidet
      sigSwitch (predInferred predicate) === [0]
    Nothing -> failure
  -- Each recursive answer grounds the helper's switch input. Its inferred
  -- commitment must remain sound when only newly discovered answers are used.
  summary <- compareTables source "p root Result?"
  map showAnswer (summaryAnswers summary) === map ("Result = " ++) ["a", "b", "c", "d"]
  summaryErrors summary === []
  summaryExhausted summary === False

prop_tabling_fallback_shapes :: Property
prop_tabling_fallback_shapes = unit $ do
  mutual <- compareTables (unlines
    ["p X <- q X.", "q X <- p X.", "p first.", "q second."]) "p Result?"
  sort (map showAnswer (summaryAnswers mutual)) === ["Result = first", "Result = second"]
  nonlinear <- compareTables (unlines
    ["path X Y <- path X Z, path Z Y.", "path a b.", "path b c."]) "path a Result?"
  sort (map showAnswer (summaryAnswers nonlinear)) === ["Result = b", "Result = c"]
  differentVariant <- compareTables (unlines
    ["path X Y <- edge X Z, path Z Y.", "path X Y <- edge X Y.",
     "edge a b.", "edge b c."]) "path a Result?"
  sort (map showAnswer (summaryAnswers differentVariant)) === ["Result = b", "Result = c"]
  constrained <- compareTables (unlines
    ["p X <- p Y, X #= Y, X in 0..2.", "p 1."]) "p Result?"
  map showAnswer (summaryAnswers constrained) === ["Result = 1"]
  declared <- compareTables (unlines
    ["p : semidet (atom: <=>).", "p X <- p X.", "p first.", "p second."])
    "p Result?"
  map showAnswer (summaryAnswers declared) === ["Result = first"]

prop_tabling_fallback_observations :: Property
prop_tabling_fallback_observations = unit $ do
  errors <- compareTables (unlines
    ["p X <- p X.", "p answer.", "p X <- missing X."]) "p Result?"
  summaryErrors errors === [UnknownPredicate ("missing", 1)]
  outputs <- compareTables (unlines
    ["p : table unsafe.", "p X <- p Y, X = Y.", "p answer <- write seen."])
    "p Result?"
  map answerOutput (summaryAnswers outputs) === [[WriteEvent "seen"]]
  cut <- compareTables (unlines
    ["p : table unsafe.", "p X <- p Y, !, X = Y.", "p first.", "p second."])
    "p Result?"
  sort (map showAnswer (summaryAnswers cut)) === ["Result = first", "Result = second"]

prop_delta_resolution_exhaustion :: Property
prop_delta_resolution_exhaustion = unit $ do
  program <- evalEither (loadProgramText (unlines
    ["p X <- p Y, edge Y X.", "p root.", "p X <- helper X.",
     "edge root next.", "helper X <- deeper X.", "deeper other."]))
  query <- evalEither (parseQuery "p Result?")
  let run fuel candidate = summarizeSearch query
        (solveGoals (mkEnv candidate) fuel (initialState (queryNVars query)) (queryGoals query))
  mapM_ (\fuel -> do
      annotateShow fuel
      observe (run fuel program) === observe (run fuel (legacyTables program))
      summaryExhausted (run fuel program) === True
    ) [0, 1, 2]

prop_delta_iteration_exhaustion :: Property
prop_delta_iteration_exhaustion = unit $ do
  summary <- compareTables "p : table.\np (next X) <- p X.\np zero." "p Result?"
  summaryExhausted summary === True
  length (summaryAnswers summary) === 301

tablingGroup :: Group
tablingGroup = Group "incremental tabling"
  [("delta table answers vs ordered legacy and graph closure", prop_delta_graph_closure),
   ("multiple delta rules and unbound variants", prop_delta_multiple_rules_and_variants),
   ("delta tables retain open answers", prop_delta_open_answers),
   ("delta answers retain order with and without indexing", prop_delta_index_policies),
   ("delta tables retain structured aliases and open answers", prop_delta_structured_aliases),
   ("delta suffix helpers retain inferred conditional determinism", prop_delta_inferred_suffix_contract),
   ("mutual nonlinear different-variant and CLP fallback", prop_tabling_fallback_shapes),
   ("tabling fallback retains errors output and cuts", prop_tabling_fallback_observations),
   ("delta fallback retains resolution exhaustion", prop_delta_resolution_exhaustion),
   ("delta tables retain iteration exhaustion", prop_delta_iteration_exhaustion)]

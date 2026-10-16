-- | Public solver facade over the explicit abstract machine.
-- The reference implementation remains available for parity tests.
module Infera.Engine
  ( -- * State and results
    OutputEvent (..),
    SolverState (..),
    SearchItem (..),
    Search,
    Env (..),
    mkEnv,
    initialState,
    maxResolutionDepth,

    -- * Solving
    solveGoals,
    solveGoal,
    solveQuery,

    -- * Answers
    Answer (..),
    QuerySummary (..),
    projectAnswer,
    summarizeSearch,
    solveAll,
    showAnswer,
    renderOutputEvent,
    runInfera,
    loadProgramText,
  )
where

import Infera.Engine.Reference hiding (solveGoal, solveGoals, solveQuery, solveAll, runInfera)
import qualified Infera.Machine.Control as Machine
import Infera.Program (Program)
import Infera.Syntax (Query, Term, parseQuery)
import Infera.Error (showSolveError)

solveGoal :: Env -> Int -> SolverState -> Term -> Search
solveGoal environment fuel state goal = Machine.solveGoals environment fuel state [goal]

solveGoals :: Env -> Int -> SolverState -> [Term] -> Search
solveGoals = Machine.solveGoals

solveQuery :: Program -> Query -> Search
solveQuery = Machine.solveQuery

solveAll :: Program -> Query -> QuerySummary
solveAll program query = summarizeSearch query (solveQuery program query)

runInfera :: String -> String -> Either String [String]
runInfera programSrc querySrc = do
  prog <- loadProgramText programSrc
  q <- parseQuery querySrc
  let summary = solveAll prog q
      answers = summaryAnswers summary
      errors = summaryErrors summary
      exhausted = summaryExhausted summary
      rendered = concatMap renderAnswerWithOutput answers
  pure $ case rendered of
    _ : _ -> rendered ++ ["Search depth limit reached; more solutions may exist." | exhausted]
    [] -> case errors of
      err : _ -> ["Error: " ++ showSolveError err]
      []
        | exhausted -> ["Search depth limit reached; the query was not proven false."]
        | otherwise -> ["false."]
  where
    renderAnswerWithOutput answer =
      let output = concatMap renderOutputEvent (answerOutput answer)
       in [output | not (null output)] ++ [showAnswer answer]

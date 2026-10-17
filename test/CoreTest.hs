{-# LANGUAGE OverloadedStrings #-}
-- | Ordered parity of the core engine with the reference and the machine on
-- the checked-in parity programs: every inline query must produce the same
-- rendered answers, output, distinct errors and exhaustion flag.
module CoreTest (coreGroup) where

import Control.Monad (forM_, unless)
import Data.String (fromString)
import Hedgehog
import Infera hiding (solveQuery)
import qualified Infera.Core as Core
import qualified Infera.Engine.Reference as Reference
import qualified Infera.Machine.Control as Machine

parityFiles :: [FilePath]
parityFiles = ["test/core/parity-basic.nprolog", "test/core/parity-edge.nprolog"]

data Observed = Observed [String] [String] Bool deriving (Eq, Show)

observe :: Query -> Search -> Observed
observe query items =
  let summary = summarizeSearch query items
   in Observed
        [showAnswer a ++ outputOf a | a <- summaryAnswers summary]
        (map showSolveError (summaryErrors summary))
        (summaryExhausted summary)
  where
    outputOf a = case answerOutput a of
      [] -> ""
      events -> " | output: " ++ show (concatMap renderOutputEvent (reverse events))

prop_parity :: FilePath -> Property
prop_parity file = withTests 1 . property $ do
  loaded <- evalIO (loadFile file)
  case loaded of
    Left err -> annotate err >> failure
    Right (program, queries) -> do
      unless (not (null queries)) $ annotate "no queries" >> failure
      forM_ queries $ \query -> do
        let shown = unwords (map show (queryGoals query))
        annotate shown
        case Core.solveQuery program query of
          Nothing -> annotate (maybe "" id (Core.coreSupports program query)) >> failure
          Just items -> do
            observe query items === observe query (Reference.solveQuery program query)
            observe query items === observe query (Machine.solveQuery program query)
            -- Collect at nearly every call: relocation must be invisible.
            case Core.solveQueryWith 1 program query of
              Nothing -> failure
              Just stressed -> observe query stressed === observe query items

-- | A construct outside the subset makes the facade fall back rather than
-- fail, and a runtime abandonment continues the same stream.
prop_fallback :: Property
prop_fallback = withTests 1 . property $ do
  let source = unlines ["<- notable.", "p : dynamic.", "q X <- X = 1."]
  program <- either (\e -> annotate e >> failure) pure (loadProgramText source)
  query <- either (\e -> annotate e >> failure) pure (parseQuery "q X?")
  Core.coreSupports program query === Just "dynamic declarations"
  observe query (Core.solveQueryOrFallback program query) === observe query (Reference.solveQuery program query)
  let constrained = unlines ["<- notable.", "r X Y <- X != Y, X = 1, Y = 2."]
  program' <- either (\e -> annotate e >> failure) pure (loadProgramText constrained)
  query' <- either (\e -> annotate e >> failure) pure (parseQuery "r A B?")
  Core.coreSupports program' query' === Nothing
  observe query' (Core.solveQueryOrFallback program' query') === observe query' (Reference.solveQuery program' query')

coreGroup :: Group
coreGroup = Group "core engine"
  ([(fromString ("parity_" ++ file), prop_parity file) | file <- parityFiles]
    ++ [("fallback", prop_fallback)])

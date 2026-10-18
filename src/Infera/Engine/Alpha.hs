-- | Equivalence of answers up to renaming of variables.
--
-- The identity of an internal variable is an implementation detail of each
-- engine: the reference numbers variables as it renames clauses, while the
-- core names a variable only when it first leaves the heap. Engines agree
-- when their answers, output and errors are equal after a consistent
-- renaming of the variables inside each answer. Query variables keep their
-- ids, because the query names them.
module Infera.Engine.Alpha
  ( alphaTerms,
    alphaBindings,
    alphaText,
    alphaOutput,
  )
where

import Data.Char (isAlphaNum, isDigit)
import qualified Data.IntMap.Strict as IM
import Infera.Engine.Reference (OutputEvent, renderOutputEvent)
import Infera.Syntax (Term (..), VarId)

-- | Rename every variable at or above @queryVars@ by order of first
-- occurrence across the list, starting at @queryVars@.
alphaTerms :: Int -> [Term] -> [Term]
alphaTerms queryVars terms = snd (foldl step (IM.empty, []) terms)
  where
    step (table, acc) t = let (table', t') = rename table t in (table', acc ++ [t'])
    rename table term = case term of
      Var v
        | v < queryVars -> (table, term)
        | otherwise -> case IM.lookup v table of
            Just w -> (table, Var w)
            Nothing ->
              let w = queryVars + IM.size table :: VarId
               in (IM.insert v w table, Var w)
      Compound f as ->
        let (table', as') = renameAll table as
         in (table', Compound f as')
      _ -> (table, term)
    renameAll table [] = (table, [])
    renameAll table (a : as) =
      let (table', a') = rename table a
          (table'', as') = renameAll table' as
       in (table'', a' : as')

-- | 'alphaTerms' over the values of an answer's named bindings.
alphaBindings :: Int -> [(String, Term)] -> [(String, Term)]
alphaBindings queryVars bindings = zip (map fst bindings) (alphaTerms queryVars (map snd bindings))

-- | Output events rendered as one text, with 'alphaText' names.
alphaOutput :: [OutputEvent] -> String
alphaOutput = alphaText . concatMap renderOutputEvent

-- | Rename the printed variable names @_G<id>@ in rendered text by order of
-- first occurrence. A name is recognised only at a token boundary.
alphaText :: String -> String
alphaText = go IM.empty True
  where
    go _ _ [] = []
    go table boundary ('_' : 'G' : rest@(d : _))
      | boundary && isDigit d =
          let (digits, after) = span isDigit rest
              v = read digits :: Int
              (table', w) = case IM.lookup v table of
                Just k -> (table, k)
                Nothing -> let k = IM.size table in (IM.insert v k table, k)
           in "_G'" ++ show w ++ go table' False after
    go table _ (c : rest) = c : go table (not (isAlphaNum c || c == '_')) rest

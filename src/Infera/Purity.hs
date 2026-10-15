-- | The effect discipline: clauses of predicates that are not declared
-- @unsafe@ may not perform effects or call unsafe predicates.  Queries and
-- directives are the program's entry points and are exempt.
module Infera.Purity
  ( impureBuiltinKeys,
    isImpureBuiltin,
    unsafeGoals,
    clauseViolations,
    programViolations,
    describeViolation,
  )
where

import qualified Data.IntMap.Strict as IM
import Infera.Error (PredKey, showPredKey)
import Infera.Program
import Infera.Syntax

-- | Builtins that perform effects or break the logical reading.
impureBuiltinKeys :: [PredKey]
impureBuiltinKeys =
  [ ("write", 1), ("writeln", 1), ("print", 1), ("nl", 0), ("emit", 1),
    ("read_file", 2), ("phrase_from_file", 2),
    ("assert", 1), ("retract", 1), ("retractall", 1),
    ("!", 0)
  ]

isImpureBuiltin :: PredKey -> Bool
isImpureBuiltin k = k `elem` impureBuiltinKeys

-- | Goals in a body that are only allowed inside an unsafe predicate: impure
-- builtins and calls to unsafe user predicates.  Control constructs and
-- goal-taking builtins are looked through; @call@ with a statically known
-- target is resolved, a variable target cannot be checked.
unsafeGoals :: Program -> [Term] -> [Term]
unsafeGoals prog = concatMap goal
  where
    goal t = case t of
      Compound f [a, b] | f `elem` [",", ";", "->", "forall"] -> goal a ++ goal b
      Compound f [g] | f `elem` ["not", "once"] -> goal g
      Compound "findall" [_, g, _] -> goal g
      Compound "minimize" [_, g] -> goal g
      Compound "call" (callee : extra) -> case callee of
        Atom f -> goal (Compound f extra)
        Compound f as -> goal (Compound f (as ++ extra))
        _ -> []
      Compound "phrase" [nt, input] -> case nt of
        Atom f -> goal (Compound f [input, Atom "nil"])
        Compound f as -> goal (Compound f (as ++ [input, Atom "nil"]))
        _ -> []
      _ -> case functorOf t of
        Just key
          | isImpureBuiltin key -> [t]
          | Just p <- lookupPred key prog, predIsUnsafe prog p -> [t]
          | Nothing <- lookupPred key prog, nameHasFlag prog (fst key) FlagUnsafe -> [t]
        _ -> []

-- | Offending goals of a clause, or nothing when its predicate is unsafe.
clauseViolations :: Program -> Clause -> [Term]
clauseViolations prog cl = case clauseKey cl >>= (`lookupPred` prog) of
  Just p | predIsUnsafe prog p -> []
  _ -> unsafeGoals prog (clauseBody cl)

-- | Every violation in the program: (predicate, offending goal).
programViolations :: Program -> [(PredKey, Term)]
programViolations prog =
  [ (predKey p, g)
  | p <- programPreds prog,
    not (predIsUnsafe prog p),
    cl <- IM.elems (predClauses p),
    g <- unsafeGoals prog (clauseBody cl)
  ]

describeViolation :: Program -> PredKey -> Term -> String
describeViolation prog key g =
  let what = case functorOf g of
        Just k
          | k == ("!", 0) -> "cut"
          | isImpureBuiltin k -> showPredKey k ++ " performs an effect"
          | Just p <- lookupPred k prog, predIsUnsafe prog p -> showPredKey k ++ " is declared unsafe"
          | otherwise -> showPredKey k ++ " is unsafe"
        Nothing -> show g
   in what ++ " but " ++ showPredKey key ++ " is not declared unsafe (add `" ++ fst key ++ " : unsafe.`)"

-- | Compiler-owned diagnostics shared by the CLI and language server.
module Infera.Diagnostic
  ( Severity (..), Diagnostic (..), checkFile, checkSource, diagnose,
    renderDiagnostic, diagnosticsJSON,
  ) where

import Data.Char (ord)
import qualified Data.IntMap.Strict as IM
import Data.List (intercalate, nub)
import qualified Data.Map.Strict as Map
import Data.Maybe (fromMaybe, isJust)
import Infera.Error (showPredKey)
import Infera.Arith (arithOps, evalArithSafe)
import Infera.Infer (builtinDet)
import Infera.Module (loadLocatedFile, loadLocatedWithSources)
import Infera.Program
import Infera.Purity (clauseViolations, describeViolation)
import Infera.Syntax
import Infera.Unify (Subst, deepWalk, termVars, unifyPlain, walk)
import Numeric (showHex)

data Severity = Error | Warning | Information deriving (Eq, Show)

data Diagnostic = Diagnostic
  { diagnosticSpan :: SourceSpan,
    diagnosticSeverity :: Severity,
    diagnosticCode :: String,
    diagnosticMessage :: String
  } deriving (Eq, Show)

checkFile :: FilePath -> IO [Diagnostic]
checkFile path = do
  result <- loadLocatedFile path
  pure (diagnoseLoaded result)

checkSource :: FilePath -> String -> [(FilePath, String)] -> IO [Diagnostic]
checkSource path src dependencies =
  diagnoseLoaded <$> loadLocatedWithSources (dependencies ++ [(path, src)]) path

diagnoseLoaded :: Either (SourceSpan, String) [LocatedTopLevel] -> [Diagnostic]
diagnoseLoaded result = case result of
  Left (loc, message) -> [Diagnostic loc Error "load-error" message]
  Right items -> diagnose items

diagnose :: [LocatedTopLevel] -> [Diagnostic]
diagnose items = concatMap inspect items
  where
    prog = buildProgram (map locatedItem items)
    defined = [predKey p | p <- programPreds prog, not (IM.null (predClauses p))]
    firstClauseSpans = Map.fromListWith (\_ first -> first)
      [(key, locatedSpan item) | item <- items, TLClause cl <- [locatedItem item], Just key <- [clauseKey cl]]
    emit item severity code message = Diagnostic (locatedSpan item) severity code message
    inspect item = case locatedItem item of
      TLClause cl ->
        shadowedBuiltin item cl ++ calls item (clauseBody cl)
          ++ singletons item (clauseHead cl : clauseBody cl)
          ++ headSort item cl ++ effects item cl ++ performance item cl
      -- Query variables are answer variables: a variable used once names an
      -- answer to report, so it is never a singleton mistake.
      TLQuery q -> calls item (queryGoals q) ++ labelingHints item [] (queryGoals q)
      TLDecl d ->
        let key = (declName d, length (declArgs d))
            flagsOnly = null (declArgs d) && declDet d == Nothing
            flags = declFlags d
         in [emit item Error "declaration-without-clauses" ("declaration for " ++ showPredKey key ++ " has no matching clauses")
            | not flagsOnly, key `notElem` defined]
              ++ [emit item Warning "conflicting-flags" "declaration contains both enabling and disabling flags"
                 | (FlagTable `elem` flags && FlagNoTable `elem` flags)
                    || (FlagIndex `elem` flags && FlagNoIndex `elem` flags)]
      _ -> []
    -- Builtins are matched before user clauses, so clauses for a builtin's
    -- name and arity never run. Reported once, on the first such clause head.
    shadowedBuiltin item cl = case clauseKey cl of
      Just key@(name, arity)
        | isBuiltin key, Map.lookup key firstClauseSpans == Just (locatedSpan item) ->
            [Diagnostic (fromMaybe (locatedSpan item) (locatedHeadSpan item)) Warning "shadowed-builtin"
              ("clauses for " ++ showPredKey key ++ " never run: " ++ showPredKey key
                ++ " is a builtin and calls always go to the builtin; "
                ++ (if locatedIsDCG item
                      then "a DCG rule adds two arguments, so rename the nonterminal (for example my_" ++ name ++ ")"
                      else "rename the predicate (for example " ++ showPredKey ("my_" ++ name, arity) ++ ")"))]
      _ -> []
    effects item cl = case clauseKey cl of
      Just key -> [emit item Error "unsafe-call" (describeViolation prog key g) | g <- clauseViolations prog cl]
      Nothing -> []
    performance item cl = nonTailHint item cl ++ indexingHint item cl
      ++ labelingHints item (termVars (clauseHead cl)) (clauseBody cl)
    nonTailHint item _ | locatedIsDCG item = []
    nonTailHint item cl = case clauseKey cl of
      Nothing -> []
      Just key ->
        [ atGoal item call "perf-non-tail-recursion"
            "This self-recursive call is followed by more work. Consider an accumulator to put recursion last when the same answers and order can be preserved."
        | call <- take 1 (nonTailCalls key (clauseBody cl)) ]
    indexingHint item cl = case clauseKey cl >>= (`lookupPred` prog) of
      Just p
        | not (locatedIsDCG item), (_, arity) <- predKey p, arity > 0,
          predIsIndexed prog p, not (predIsDynamic prog p),
          IM.size (predClauses p) > 1,
          Map.lookup (predKey p) firstClauseSpans == Just (locatedSpan item),
          all sameHeadKey (transposeArguments p) ->
            [Diagnostic (fromMaybe (locatedSpan item) (locatedHeadSpan item)) Information "perf-unselective-index"
              "These clauses have the same head key in every argument, so the current argument indexes cannot select between them. Distinct outer constructors or scalar tags can allow earlier clause selection."]
      _ -> []
    atGoal item goalTerm code message = Diagnostic (goalSpan item goalTerm) Information code message
    labelingHints item headVars goals = go emptyPrefix (concatMap straightConjunction goals)
      where
        go _ [] = []
        go prefix (g : rest) =
          let vars = labeledVariables (prefixSubst prefix) g
              later = [constraint | constraint <- rest, isConstraint constraint,
                any (`elem` vars) (termVars (deepWalk (prefixSubst prefix) constraint))]
              orderHint =
                [atGoal item g "perf-labeling-before-constraints"
                  "A later constraint uses variables already labeled. If it is intended to restrict the search, consider posting it first; check that reordering preserves the intended answers and effects."
                | prefixReachable prefix, not (null vars), not (null later)]
              unbounded = [v | v <- vars, definitelyUnbounded headVars prefix v]
              domainHint =
                [atGoal item g "perf-unbounded-labeling"
                  ("Labeling requires finite integer domains; " ++ intercalate ", " (map (variableName item) unbounded)
                    ++ " " ++ (if length unbounded == 1 then "is a fresh variable without" else "are fresh variables without")
                    ++ " preceding finite bounds. Add domains before labeling.")
                | not (null unbounded)]
           in orderHint ++ domainHint ++ go (advancePrefix prefix g) rest
    singletons item terms =
      let occurrences = concatMap variables terms
       in [emit item Warning "singleton-variable" ("singleton variable " ++ name ++ " (use _ or _" ++ name ++ " if intended)")
          | (name, v) <- locatedNames item, take 1 name /= "_", length (filter (== v) occurrences) == 1]
    headSort item cl = case clauseKey cl >>= (`lookupPred` prog) of
      Just p | not (null (predDecls p)), all (incompatible (arguments (clauseHead cl))) (predDecls p) ->
        [emit item Warning "head-sort-mismatch" "clause head cannot match any declared argument sorts"]
      _ -> []
    calls item = concatMap (goal item)
    goal item t = case t of
      Compound f [a, b] | f `elem` [",", ";", "->", "forall"] -> calls item [a, b]
      Compound f [g] | f `elem` ["not", "once"] -> goal item g
      Compound "findall" [_, g, _] -> goal item g
      Compound "minimize" [_, g] -> goal item g
      Compound "call" (callee : extra) -> case callee of
        Atom f -> goal item (Compound f extra)
        Compound f as -> goal item (Compound f (as ++ extra))
        Var _ -> [] -- dynamic targets cannot be checked statically
        _ -> [emit item Error "not-callable" "call target is not callable"]
      Compound "phrase" [nt, input] -> case nt of
        Atom f -> goal item (Compound f [input, Atom "nil"])
        Compound f as -> goal item (Compound f (as ++ [input, Atom "nil"]))
        _ -> []
      Var _ -> []
      _ -> case functorOf t of
        Nothing -> [emit item Error "not-callable" ("goal is not callable: " ++ show t)]
        Just key@(name, arity)
          | isBuiltin key -> []
          | nameHasFlag prog name FlagDynamic -> []
          | key `elem` defined -> case lookupPred key prog of
              Just p | not (null (predDecls p)), all (incompatible (arguments t)) (predDecls p) ->
                [emit item Error "call-sort-mismatch" ("literal arguments of " ++ showPredKey key ++ " conflict with every declared signature")]
              _ -> []
          | otherwise ->
              let alternatives = nub ([k | k@(n, _) <- defined, n == name]
                    ++ [(name, a) | a <- [0 .. max 6 arity], isBuiltin (name, a)])
               in [if null alternatives
                    then emit item Error "undefined-predicate" ("undefined predicate: " ++ showPredKey key)
                    else emit item Error "wrong-arity" ("no clauses for " ++ showPredKey key ++ "; available: " ++ intercalate ", " (map showPredKey alternatives))]
    isBuiltin ("call", n) = n >= 1
    isBuiltin (n, a) = isJust (builtinDet n a)
    incompatible args sig = or (zipWith (\arg spec -> definitelyWrong (argSort spec) arg) args (sigArgs sig))

arguments :: Term -> [Term]
arguments (Compound _ args) = args
arguments _ = []

-- Performance advice deliberately stays syntactic. It does not run a query,
-- choose a mode, or assume that a predicate's arguments are ground at entry.
-- In particular an unknown call invalidates the fresh-variable analysis.
goalSpan :: LocatedTopLevel -> Term -> SourceSpan
goalSpan item t = case [loc | (goalTerm, loc) <- locatedGoalSpans item, goalTerm == t] of
  [loc] -> loc
  _ -> locatedSpan item

variableName :: LocatedTopLevel -> VarId -> String
variableName item v = fromMaybe ("_G" ++ show v) (lookup v [(n, name) | (name, n) <- locatedNames item])

nonTailCalls :: PredKey -> [Term] -> [Term]
nonTailCalls key goals = concat (zipWith inspect (replicate (max 0 (length goals - 1)) False ++ [True]) goals)
  where
    inspect tailPosition t = case t of
      Compound "," [a, b] -> inspect False a ++ inspect tailPosition b
      Compound ";" [a, b] -> inspect tailPosition a ++ inspect tailPosition b
      Compound "->" [a, b] -> inspect False a ++ inspect tailPosition b
      Compound f [g] | f `elem` ["not", "once"] -> inspect False g
      Compound "findall" [_, g, _] -> inspect False g
      Compound "minimize" [_, g] -> inspect False g
      Compound "forall" [a, b] -> inspect False a ++ inspect False b
      Compound "call" [g] -> inspect tailPosition g
      Compound "call" (callee : extra) -> case callee of
        Atom f -> direct tailPosition t (f, length extra)
        Compound f as -> direct tailPosition t (f, length as + length extra)
        _ -> []
      Compound "phrase" [nt, _] -> case nt of
        Atom f -> direct tailPosition t (f, 2)
        Compound f as -> direct tailPosition t (f, length as + 2)
        _ -> []
      _ -> maybe [] (direct tailPosition t) (functorOf t)
    direct tailPosition t called = [t | not tailPosition, called == key]

transposeArguments :: Pred -> [[Term]]
transposeArguments p =
  [[arguments (clauseHead cl) !! i | cl <- IM.elems (predClauses p)] | i <- [0 .. snd (predKey p) - 1]]

sameHeadKey :: [Term] -> Bool
sameHeadKey [] = False
sameHeadKey (first : rest) = all ((== indexKey first) . indexKey) rest

straightConjunction :: Term -> [Term]
straightConjunction (Compound "," [a, b]) = straightConjunction a ++ straightConjunction b
straightConjunction t = [t]

labelArgument :: Term -> Maybe Term
labelArgument (Compound f [xs]) | f `elem` ["label", "labeling"] = Just xs
labelArgument (Compound "labeling" [Compound "cons" [Compound "min" [_], Atom "nil"], xs]) = Just xs
labelArgument _ = Nothing

labeledVariables :: Subst -> Term -> [VarId]
labeledVariables s t = case labelArgument (deepWalk s t) of
  Nothing -> []
  Just list -> case unfoldCons (deepWalk s list) of
    (xs, Nothing) | all scalar xs -> nub (concatMap termVars xs)
    _ -> [] -- Open lists and ill-typed elements need runtime information.
  where
    scalar (Var _) = True
    scalar (IntLit _) = True
    scalar _ = False

isConstraint :: Term -> Bool
isConstraint (Compound f args) = (f, length args) `elem`
  [("in", 2), ("int_eq", 2), ("fd_ne", 2), ("fd_le", 2), ("fd_lt", 2),
   ("fd_ge", 2), ("fd_gt", 2), ("neq", 2), ("all_different", 1),
   ("all_distinct", 1), ("reify", 2)]
isConstraint _ = False

data LabelPrefix = LabelPrefix
  { prefixSubst :: Subst,
    prefixBounds :: IM.IntMap (Bool, Bool),
    prefixUncertain :: [VarId],
    prefixOpaque :: Bool,
    prefixReachable :: Bool
  }

emptyPrefix :: LabelPrefix
emptyPrefix = LabelPrefix IM.empty IM.empty [] False True

mergeBounds :: (Bool, Bool) -> (Bool, Bool) -> (Bool, Bool)
mergeBounds (lo, hi) (lo', hi') = (lo || lo', hi || hi')

normalizePrefix :: LabelPrefix -> LabelPrefix
normalizePrefix prefix = prefix
  { prefixBounds = IM.fromListWith mergeBounds
      [(w, bounds) | (v, bounds) <- IM.toList (prefixBounds prefix), Var w <- [walk s (Var v)]],
    prefixUncertain = nub (concatMap (termVars . deepWalk s . Var) (prefixUncertain prefix))
  }
  where s = prefixSubst prefix

definitelyUnbounded :: [VarId] -> LabelPrefix -> VarId -> Bool
definitelyUnbounded headVars prefix v =
  prefixReachable prefix && not (prefixOpaque prefix)
    && v `notElem` prefixUncertain prefix
    && v `notElem` concatMap (termVars . deepWalk (prefixSubst prefix) . Var) headVars
    && IM.findWithDefault (False, False) v (prefixBounds prefix) /= (True, True)

advancePrefix :: LabelPrefix -> Term -> LabelPrefix
advancePrefix prefix original
  | not (prefixReachable prefix) = prefix
  | otherwise = case deepWalk s original of
      Atom "true" -> prefix
      Atom "!" -> prefix
      Atom "fail" -> prefix {prefixReachable = False}
      Compound "unify" [a, b] -> bind a b
      Compound "is" [a, b@(IntLit _)] -> bind a b
      Compound "in" [targets, Compound "range" [lo, hi]]
        | Just lower <- finiteBound lo, Just upper <- finiteBound hi ->
            prefix {prefixBounds = foldr (\v -> IM.insertWith mergeBounds v (lower, upper))
              (prefixBounds prefix) (termVars targets)}
      t | isConstraint t -> prefix {prefixUncertain = nub (termVars t ++ prefixUncertain prefix)}
      _ -> prefix {prefixOpaque = True}
  where
    s = prefixSubst prefix
    bind a b
      | hasArithmetic a || hasArithmetic b = prefix {prefixOpaque = True}
      | otherwise = case unifyPlain s a b of
          Nothing -> prefix {prefixReachable = False}
          Just s' -> normalizePrefix (prefix {prefixSubst = s'})
    hasArithmetic (Compound f as) =
      (f `elem` ["neg", "abs"] && length as == 1)
        || (f `elem` filter (`notElem` ["neg", "abs"]) arithOps && length as == 2)
        || any hasArithmetic as
    hasArithmetic _ = False
    finiteBound (IntLit _) = Just True
    finiteBound (Atom "inf") = Just False
    finiteBound (Atom "sup") = Just False
    finiteBound _ = Nothing

variables :: Term -> [VarId]
variables (Var v) = [v]
variables (Compound _ args) = concatMap variables args
variables _ = []

-- Variables provide no evidence of a sort conflict. Constructor terms are
-- known to be incompatible with scalar sorts even if their fields are open.
definitelyWrong :: Sort -> Term -> Bool
definitelyWrong SAny _ = False
definitelyWrong SNone _ = False
definitelyWrong _ (Var _) = False
definitelyWrong s t@(Compound f _) | f `elem` arithOps =
  case evalArithSafe IM.empty t of
    Right (Just value) -> definitelyWrong s value
    _ -> False
definitelyWrong (SList s) (Compound "cons" [h, t]) = definitelyWrong s h || definitelyWrong (SList s) t
definitelyWrong (SList _) (Atom "nil") = False
definitelyWrong s t = not $ case (s, t) of
  (SInt, IntLit _) -> True
  (SFloat, FloatLit _) -> True
  (SNum, IntLit _) -> True
  (SNum, FloatLit _) -> True
  (SStr, StrLit _) -> True
  (SChar, CharLit _) -> True
  (SAtom, Atom _) -> True
  _ -> False

renderDiagnostic :: Diagnostic -> String
renderDiagnostic d =
  let loc = diagnosticSpan d
   in spanFile loc ++ ":" ++ show (spanLine loc) ++ ":" ++ show (spanColumn loc)
        ++ ": " ++ severityText (diagnosticSeverity d) ++ " [" ++ diagnosticCode d ++ "]: " ++ diagnosticMessage d

severityText :: Severity -> String
severityText Error = "error"
severityText Warning = "warning"
severityText Information = "information"

diagnosticsJSON :: [Diagnostic] -> String
diagnosticsJSON ds = "[" ++ intercalate "," (map render ds) ++ "]"
  where
    render d =
      let loc = diagnosticSpan d
          pos l c = "{\"line\":" ++ show (max 0 (l - 1)) ++ ",\"character\":" ++ show (max 0 (c - 1)) ++ "}"
       in "{\"file\":" ++ jsonString (spanFile loc)
            ++ ",\"severity\":" ++ jsonString (severityText (diagnosticSeverity d))
            ++ ",\"code\":" ++ jsonString (diagnosticCode d)
            ++ ",\"message\":" ++ jsonString (diagnosticMessage d)
            ++ ",\"range\":{\"start\":" ++ pos (spanLine loc) (spanColumn loc)
            ++ ",\"end\":" ++ pos (spanEndLine loc) (spanEndColumn loc) ++ "}}"

jsonString :: String -> String
jsonString s = "\"" ++ concatMap escape s ++ "\""
  where
    escape '"' = "\\\""
    escape '\\' = "\\\\"
    escape c | ord c < 32 = let h = showHex (ord c) "" in "\\u" ++ replicate (4 - length h) '0' ++ h
    escape c = [c]

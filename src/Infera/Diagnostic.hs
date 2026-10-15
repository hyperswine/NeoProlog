-- | Compiler-owned diagnostics shared by the CLI and language server.
module Infera.Diagnostic
  ( Severity (..), Diagnostic (..), checkFile, checkSource, diagnose,
    renderDiagnostic, diagnosticsJSON,
  ) where

import Data.Char (ord)
import qualified Data.IntMap.Strict as IM
import Data.List (intercalate, nub)
import Data.Maybe (isJust)
import Infera.Error (showPredKey)
import Infera.Arith (arithOps, evalArithSafe)
import Infera.Infer (builtinDet)
import Infera.Module (loadLocatedFile, loadLocatedWithSources)
import Infera.Program
import Infera.Purity (clauseViolations, describeViolation)
import Infera.Syntax
import Numeric (showHex)

data Severity = Error | Warning deriving (Eq, Show)

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
    emit item severity code message = Diagnostic (locatedSpan item) severity code message
    inspect item = case locatedItem item of
      TLClause cl ->
        calls item (clauseBody cl) ++ singletons item (clauseHead cl : clauseBody cl)
          ++ headSort item cl ++ effects item cl
      TLQuery q -> calls item (queryGoals q) ++ singletons item (queryGoals q)
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
    effects item cl = case clauseKey cl of
      Just key -> [emit item Error "unsafe-call" (describeViolation prog key g) | g <- clauseViolations prog cl]
      Nothing -> []
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

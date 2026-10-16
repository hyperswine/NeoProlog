-- | The predicate table: clauses grouped by name/arity, per-argument indexes,
-- declared and inferred signatures, and per-predicate flags.
module Infera.Program
  ( PredKey,
    IndexKey (..),
    indexKey,
    ArgIndex (..),
    Signature (..),
    defaultSignature,
    Pred (..),
    Program (..),
    emptyProgram,
    addClause,
    addDecl,
    addDirective,
    buildProgram,
    lookupPred,
    programPreds,
    candidateClauses,
    predIsTabled,
    predIsIndexed,
    predDeclaredKeys,
    effectiveFlags,
    nameHasFlag,
    predIsUnsafe,
    predIsDynamic,
    dynamicNames,
    addFiles,
  )
where

import Data.IntMap.Strict (IntMap)
import qualified Data.IntMap.Strict as IM
import Data.IntSet (IntSet)
import qualified Data.IntSet as IS
import Data.List (foldl')
import Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map
import Infera.Error (PredKey)
import Infera.Machine.Trace.Types (SourceMap, emptySourceMap)
import Infera.Syntax

-- ─── INDEXING ────────────────────────────────────────────────────────────────

data IndexKey
  = IKAtom String
  | IKInt Integer
  | IKFloat Double
  | IKChar Char
  | IKStr String
  | IKFun String Int
  deriving (Eq, Ord, Show)

-- | Principal functor of a (dereferenced) term; Nothing for variables.
indexKey :: Term -> Maybe IndexKey
indexKey (Atom a) = Just (IKAtom a)
indexKey (IntLit n) = Just (IKInt n)
indexKey (FloatLit d) = Just (IKFloat d)
indexKey (CharLit c) = Just (IKChar c)
indexKey (StrLit s) = Just (IKStr s)
indexKey (Compound f as) = Just (IKFun f (length as))
indexKey (Var _) = Nothing

-- | Index for one argument position.
data ArgIndex = ArgIndex
  { -- | clauses whose head has this principal functor at the position
    aiKeyed :: Map IndexKey IntSet,
    -- | clauses with a variable at the position (match anything)
    aiOpen :: IntSet
  }
  deriving (Show)

buildIndex :: Int -> IntMap Clause -> [ArgIndex]
buildIndex arity clauses = [indexFor i | i <- [0 .. arity - 1]]
  where
    indexFor i =
      foldl' (addTo i) (ArgIndex Map.empty IS.empty) (IM.toList clauses)
    addTo i (ArgIndex keyed open) (ci, cl) =
      case headArg i cl of
        Nothing -> ArgIndex keyed (IS.insert ci open)
        Just t -> case indexKey t of
          Nothing -> ArgIndex keyed (IS.insert ci open)
          Just k -> ArgIndex (Map.insertWith IS.union k (IS.singleton ci) keyed) open
    headArg i cl = case clauseHead cl of
      Compound _ as | i < length as -> Just (as !! i)
      _ -> Nothing

-- | Candidate clause numbers (in clause order) for a call whose arguments
-- have the given principal functors (Nothing = unbound).
candidateClauses :: Pred -> [Maybe IndexKey] -> [Int]
candidateClauses p keys =
  case [restrict ai k | (ai, Just k) <- zip (predIndex p) keys] of
    [] -> IM.keys (predClauses p)
    (s : ss) -> IS.toAscList (foldl' IS.intersection s ss)
  where
    restrict (ArgIndex keyed open) k =
      IS.union open (Map.findWithDefault IS.empty k keyed)

-- ─── SIGNATURES AND PREDICATES ───────────────────────────────────────────────

-- | A mode signature.  'sigSwitch' lists argument positions (0-based) that
-- must be ground at call time for the determinism category to be trusted;
-- it is only populated for inferred signatures.
data Signature = Signature
  { sigDet :: Det,
    sigArgs :: [ArgSpec],
    sigSwitch :: [Int]
  }
  deriving (Show, Eq)

-- | The most general signature: any sort, in/out, nondet.
defaultSignature :: Int -> Signature
defaultSignature arity = Signature Nondet (replicate arity (ArgSpec SAny ModeInOut)) []

data Pred = Pred
  { predKey :: PredKey,
    predClauses :: IntMap Clause,
    predIndex :: [ArgIndex],
    -- | Declared mode signatures (alternatives), in declaration order.
    predDecls :: [Signature],
    -- | Flags from declarations.
    predFlags :: [Flag],
    -- | Inferred signature (filled in by "Infera.Infer").
    predInferred :: Signature,
    -- | Whether the predicate can reach itself through calls.
    predRecursive :: Bool,
    -- | Whether the predicate (transitively) performs output.
    predPure :: Bool,
    -- | Whether every direct self-call recurses on a proper subterm of the
    -- corresponding head argument (list walkers, tree walkers).  Such
    -- predicates always terminate and are not tabled by default.
    predStructural :: Bool
  }
  deriving (Show)

newPred :: PredKey -> Pred
newPred k@(_, arity) =
  Pred
    { predKey = k,
      predClauses = IM.empty,
      predIndex = replicate arity (ArgIndex Map.empty IS.empty),
      predDecls = [],
      predFlags = [],
      predInferred = defaultSignature arity,
      predRecursive = False,
      predPure = True,
      predStructural = False
    }

data Program = Program
  { progPreds :: Map PredKey Pred,
    -- | Predicate keys in order of first definition.
    progOrder :: [PredKey],
    -- | Flags from declarations that name a predicate without arguments or
    -- determinism (@gen : notable.@); they apply to every arity.
    progNameFlags :: Map String [Flag],
    -- | Contents of files named by literal @read_file@ / @phrase_from_file@
    -- goals, read when the program was loaded (the engine is pure).
    progFiles :: Map String String,
    -- | Global defaults set by @<- table.@ / @<- notable.@ etc.
    progTableDefault :: Bool,
    progIndexDefault :: Bool,
    -- | Original clause/goal identities. Runtime tracing keeps this metadata
    -- separate from the term templates and never changes public errors.
    progSources :: SourceMap
  }
  deriving (Show)

emptyProgram :: Program
emptyProgram = Program Map.empty [] Map.empty Map.empty True True emptySourceMap

lookupPred :: PredKey -> Program -> Maybe Pred
lookupPred k = Map.lookup k . progPreds

programPreds :: Program -> [Pred]
programPreds prog = [p | k <- progOrder prog, Just p <- [Map.lookup k (progPreds prog)]]

predDeclaredKeys :: Program -> [PredKey]
predDeclaredKeys prog = [k | k <- progOrder prog, Just p <- [Map.lookup k (progPreds prog)], not (null (predDecls p))]

withPred :: PredKey -> (Pred -> Pred) -> Program -> Program
withPred k f prog =
  let existing = Map.member k (progPreds prog)
      p0 = Map.findWithDefault (newPred k) k (progPreds prog)
   in prog
        { progPreds = Map.insert k (f p0) (progPreds prog),
          progOrder = if existing then progOrder prog else progOrder prog ++ [k]
        }

-- | Append a clause to its predicate and refresh the index.
addClause :: Clause -> Program -> Program
addClause c prog = case clauseKey c of
  Nothing -> prog
  Just k@(_, arity) -> withPred k add prog
    where
      add p =
        let n = IM.size (predClauses p)
            clauses' = IM.insert n c (predClauses p)
         in p {predClauses = clauses', predIndex = buildIndex arity clauses'}

addDecl :: Decl -> Program -> Program
addDecl d prog
  | null (declArgs d) && declDet d == Nothing =
      prog {progNameFlags = Map.insertWith (flip (++)) (declName d) (declFlags d) (progNameFlags prog)}
  | otherwise =
      let k = (declName d, length (declArgs d))
          sig = Signature (maybe Nondet id (declDet d)) (declArgs d) []
       in withPred k (\p -> p {predDecls = predDecls p ++ [sig], predFlags = predFlags p ++ declFlags d}) prog

-- | Effective flags of a predicate: its own plus name-wide ones.
effectiveFlags :: Program -> Pred -> [Flag]
effectiveFlags prog p = predFlags p ++ Map.findWithDefault [] (fst (predKey p)) (progNameFlags prog)

-- | Does any declaration for this name (any arity) carry the flag?
nameHasFlag :: Program -> String -> Flag -> Bool
nameHasFlag prog name flag =
  flag `elem` Map.findWithDefault [] name (progNameFlags prog)
    || or [flag `elem` predFlags p | p <- programPreds prog, fst (predKey p) == name]

-- | Unsafe predicates may perform effects (output, file reads, cut,
-- assert/retract) and call other unsafe predicates.
predIsUnsafe :: Program -> Pred -> Bool
predIsUnsafe prog p = FlagUnsafe `elem` effectiveFlags prog p

-- | Dynamic predicates have no static clauses; their facts live in the
-- solver state and are changed with assert/retract.
predIsDynamic :: Program -> Pred -> Bool
predIsDynamic prog p = FlagDynamic `elem` effectiveFlags prog p

dynamicNames :: Program -> [String]
dynamicNames prog = [name | (name, flags) <- Map.toList (progNameFlags prog), FlagDynamic `elem` flags]

addFiles :: [(String, String)] -> Program -> Program
addFiles files prog = prog {progFiles = Map.union (Map.fromList files) (progFiles prog)}

-- | Handle a global directive; returns Nothing for directives the program
-- table does not understand (e.g. imports, handled elsewhere).
addDirective :: [Term] -> Program -> Maybe Program
addDirective [Atom "table"] prog = Just prog {progTableDefault = True}
addDirective [Atom "notable"] prog = Just prog {progTableDefault = False}
addDirective [Atom "index"] prog = Just prog {progIndexDefault = True}
addDirective [Atom "noindex"] prog = Just prog {progIndexDefault = False}
addDirective _ _ = Nothing

-- | Build a program from clauses and declarations (directives other than the
-- global flag toggles are ignored here).
buildProgram :: [TopLevel] -> Program
buildProgram = foldl' step emptyProgram
  where
    step prog (TLClause c) = addClause c prog
    step prog (TLDecl d) = addDecl d prog
    step prog (TLDirective goals) = maybe prog id (addDirective goals prog)
    step prog (TLQuery _) = prog

-- | Tabling is on by default for recursive, pure predicates that are not
-- merely structurally recursive.  A @table@ flag forces it on; @notable@ (or
-- a global @<- notable.@) turns it off.
predIsTabled :: Program -> Pred -> Bool
predIsTabled prog p
  | FlagNoTable `elem` flags = False
  | FlagTable `elem` flags = True
  | otherwise = progTableDefault prog && predRecursive p && predPure p && not (predStructural p)
  where
    flags = effectiveFlags prog p

predIsIndexed :: Program -> Pred -> Bool
predIsIndexed prog p
  | FlagNoIndex `elem` flags = False
  | FlagIndex `elem` flags = True
  | otherwise = progIndexDefault prog
  where
    flags = effectiveFlags prog p

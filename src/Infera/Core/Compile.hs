{-# LANGUAGE BangPatterns #-}

-- | Compile an inferred 'P.Program' and a query into the core's plans.
--
-- Clause heads become argument patterns matched against call words without
-- building a head term. Bodies become goal plans over activation slots. The
-- compiler also decides, once per program, whether every reachable construct
-- is inside the core's supported subset; otherwise the caller keeps using the
-- existing machine.
module Infera.Core.Compile
  ( Pattern (..),
    Expr (..),
    ArithOp (..),
    CmpOp (..),
    Check (..),
    Goal (..),
    Pred (..),
    PredRef,
    Clause (..),
    ArgIndex (..),
    Key (..),
    CoreProgram (..),
    Unsupported (..),
    compileProgram,
    compileGoalTerm,
    candidateClauses,
    keyOfWord,
  )
where

import Control.Monad (forM, forM_)
import Data.Array (Array, listArray)
import Data.IORef
import qualified Data.IntMap.Strict as IM
import qualified Data.IntSet as IS
import qualified Data.Map.Strict as Map
import Infera.Core.Store
import Infera.Error (PredKey, SolveError (..))
import qualified Infera.Program as P
import qualified Infera.Syntax as S
import Infera.Syntax (Term (..))

-- | How a goal argument or head argument is obtained or matched.
data Pattern
  = -- | activation variable, offset from the activation base
    PSlot !Int
  | -- | a ready word: a constant, or a runtime cell handed to a dynamic goal
    PWord !Word'
  | -- | functor word and argument patterns
    PStruct !Word' [Pattern]
  | -- | arithmetic structure in a call argument: evaluated when ground,
    -- otherwise built as data (the reference normalises call arguments)
    PArith !Word' !ArithOp [Pattern]

data ArithOp = OpPlus | OpMinus | OpMul | OpDiv | OpMod | OpPow | OpNeg | OpAbs | OpMin | OpMax
  deriving (Eq, Show)

data Expr
  = EImm !Int
  | EBig !Integer
  | EFlt !Double
  | -- | evaluate a word at runtime: a number, or arithmetic data
    EPat Pattern
  | EOp !ArithOp [Expr]

data CmpOp = CmpGt | CmpLt | CmpGte | CmpLte deriving (Eq, Show)

data Check = CkVar | CkNonvar | CkGround | CkInt | CkFloat | CkNum | CkStr | CkAtom | CkChar | CkList
  deriving (Eq, Show)

-- | Predicates are resolved through a reference so that bodies can name
-- predicates compiled later (or recursively) without a runtime map lookup.
type PredRef = IORef Pred

data Goal
  = GCall !PredRef [Pattern]
  | -- | a call to a tabled predicate
    GTabled !PredRef [Pattern]
  | -- | a call to a dynamic name without clauses: its asserted facts
    GCallFacts !PredKey [Pattern]
  | GAssert Pattern
  | GRetract Pattern
  | GRetractAll Pattern
  | -- | @minimize Cost Goal@
    GMinimize Pattern [Goal]
  | -- | a variable goal (True) or @call/N@ (False): a goal word plus extra arguments
    GCallDyn !Bool Pattern [Pattern]
  | GAnd [Goal]
  | GUnify Pattern Pattern
  | GEquiv Pattern Pattern
  | -- | disequality; a constraint when non-ground, which the core abandons
    GNeq Pattern Pattern
  | GIs Pattern Expr
  | GCmp !CmpOp Expr Expr
  | GTrue
  | GFail
  | GCut
  | GOr [Goal] [Goal]
  | GIf [Goal] [Goal] (Maybe [Goal])
  | GNot [Goal]
  | GOnce [Goal]
  | GFindAll Pattern [Goal] Pattern
  | GCheck !Check Pattern
  | -- | write (False) or writeln (True)
    GWrite !Bool Pattern
  | GNl
  | GError SolveError
  | -- | a leaf builtin evaluated by the reference implementation on
    -- exported terms, with its bindings imported back
    GLeaf !String [Pattern]
  | -- | @phrase NT L@
    GPhrase Pattern Pattern
  | -- | @phrase_from_file NT Path@
    GPhraseFile Pattern Pattern
  | -- | @emit NT@
    GEmit Pattern
  | -- | runtime only: write the character list in a slot
    GEmitText Pattern
  | -- | a construct outside the core: abandon the run and fall back
    GUnsupported Term

data Clause = Clause
  { clVars :: !Int,
    clHead :: [Pattern],
    clBody :: [Goal]
  }

data Key = KAtm !Int | KInt !Int | KChr !Int | KFun !Word' | KBig !Integer | KFlt !Double | KStr !String
  deriving (Eq, Ord, Show)

-- | Per-position clause selection: immediate keys (atom, integer, character
-- and functor words) map to the ascending candidates sharing that key or
-- open at the position; boxed keys go through a value map; an unbound or
-- unknown key yields the open clauses.
data ArgIndex = ArgIndex
  { aiFast :: !(IM.IntMap [Int]),
    aiBoxed :: !(Map.Map Key [Int]),
    aiOpen :: [Int],
    -- | some clause has a key at this position
    aiSelective :: !Bool
  }

data Pred = Pred
  { pKey :: !PredKey,
    pArity :: !Int,
    pClauses :: !(Array Int Clause),
    pClauseCount :: !Int,
    pIndex :: [ArgIndex],
    pIndexed :: !Bool,
    pDecls :: [P.Signature],
    pInferred :: !P.Signature
  }

data CoreProgram = CoreProgram
  { cpPreds :: Map.Map PredKey PredRef,
    cpQuery :: [Goal],
    cpQueryVars :: !Int,
    cpNil :: !Word',
    cpCons :: !Word',
    -- | arithmetic functor words and their operators
    cpArith :: IM.IntMap ArithOp,
    -- | the first construct that would make a run fall back, if any
    cpUnsupported :: Maybe String
  }

newtype Unsupported = Unsupported String deriving (Show)

data Ctx = Ctx
  { ctxStore :: Store,
    ctxProgram :: P.Program,
    ctxPreds :: Map.Map PredKey PredRef,
    -- | compiling a goal handed to call/N at runtime: nothing is recorded
    ctxDynamic :: Bool,
    ctxProblems :: IORef [String]
  }

-- | Compile the whole program for one store. Constructs outside the core
-- compile to runtime abandonment; the first one met is recorded in
-- 'cpUnsupported' for diagnostics.
compileProgram :: Store -> P.Program -> S.Query -> IO (Either Unsupported CoreProgram)
compileProgram store program query = do
  let preds = P.programPreds program
  problems <- newIORef []
  nilW <- atmWord <$> internAtom (symbols store) "nil"
  consW <- (\f -> funWord f 2) <$> internFunctor (symbols store) "cons" 2
  refs <- forM preds $ \p -> do
    ref <- newIORef (error "predicate compiled later")
    pure (P.predKey p, ref)
  let table = Map.fromList refs
      ctx = Ctx store program table False problems
  forM_ preds $ \p -> do
    compiled <- compilePred ctx p
    writeIORef (table Map.! P.predKey p) compiled
  goals <- compileBody ctx (S.queryGoals query)
  arith <- forM arithFunctors $ \(name, arity, op) -> do
    fid <- internFunctor (symbols store) name arity
    pure (funWord fid arity, op)
  found <- reverse <$> readIORef problems
  pure (Right (CoreProgram table goals (S.queryNVars query) nilW consW (IM.fromList arith)
    (case found of (problem : _) -> Just problem; [] -> Nothing)))

compilePred :: Ctx -> P.Pred -> IO Pred
compilePred ctx p = do
  let clauses = IM.elems (P.predClauses p)
      arity = snd (P.predKey p)
  compiledClauses <- mapM (compileClause ctx) clauses
  let count = length compiledClauses
  index <- mapM (\i -> buildIndex (ctxStore ctx) i compiledClauses) [0 .. arity - 1]
  pure
    Pred
      { pKey = P.predKey p,
        pArity = arity,
        pClauses = listArray (0, max 0 (count - 1)) compiledClauses,
        pClauseCount = count,
        pIndex = index,
        pIndexed = P.predIsIndexed (ctxProgram ctx) p,
        pDecls = P.predDecls p,
        pInferred = P.predInferred p
      }

buildIndex :: Store -> Int -> [Clause] -> IO ArgIndex
buildIndex store position clauses = do
  keyed <- forM (zip [0 ..] clauses) $ \(ordinal, clause) -> do
    key <- case drop position (clHead clause) of
      (pattern : _) -> patternKey store pattern
      [] -> pure Nothing
    pure (ordinal :: Int, key)
  let open = IS.fromList [ordinal | (ordinal, Nothing) <- keyed]
      grouped = Map.fromListWith IS.union [(key, IS.singleton ordinal) | (ordinal, Just key) <- keyed]
      withOpen members = IS.toAscList (IS.union members open)
      fast = IM.fromList [(w, withOpen members) | (key, members) <- Map.toList grouped, Just w <- [immediateKey key]]
      boxedKeys = Map.fromList [(key, withOpen members) | (key, members) <- Map.toList grouped, immediateKey key == Nothing]
  pure (ArgIndex fast boxedKeys (IS.toAscList open) (not (Map.null grouped)))

immediateKey :: Key -> Maybe Int
immediateKey key = case key of
  KAtm i -> Just (atmWord i)
  KInt i -> Just (intWord i)
  KChr i -> Just (chrWord i)
  KFun w -> Just w
  _ -> Nothing

patternKey :: Store -> Pattern -> IO (Maybe Key)
patternKey store pattern = case pattern of
  PSlot _ -> pure Nothing
  PWord w -> keyOfWord store w
  PStruct f _ -> pure (Just (KFun f))
  PArith f _ _ -> pure (Just (KFun f))

-- | The index key of a dereferenced word; Nothing for an unbound variable.
keyOfWord :: Store -> Word' -> IO (Maybe Key)
keyOfWord store w = case tagOf w of
  t | t == tagRef -> pure Nothing
    | t == tagAtm -> pure (Just (KAtm (valOf w)))
    | t == tagInt -> pure (Just (KInt (valOf w)))
    | t == tagChr -> pure (Just (KChr (valOf w)))
    | t == tagStr -> Just . KFun . funKey <$> readCell store (valOf w)
    | t == tagBox -> do
        value <- boxed store w
        pure . Just $ case value of
          BInt n -> KBig n
          BFlt d -> KFlt d
          BStr s -> KStr s
    | otherwise -> pure Nothing

-- | Candidate clause ordinals for dereferenced argument words: the first
-- bound argument at a selective position decides. Selection only skips
-- clauses whose heads cannot match, so any sound choice preserves answers.
candidateClauses :: Store -> Pred -> IO [Int]
candidateClauses store p
  | not (pIndexed p) = pure (all' p)
  | otherwise = go (pIndex p) 0
  where
    all' predicate = [0 .. pClauseCount predicate - 1]
    go (index : rest) !i
      | not (aiSelective index) = go rest (i + 1)
      | otherwise = do
          w <- readArg store i >>= deref store
          if tagOf w == tagRef
            then go rest (i + 1)
            else
              if tagOf w == tagStr
                then do
                  f <- readCell store (valOf w)
                  pure (IM.findWithDefault (aiOpen index) (funKey f) (aiFast index))
                else
                  if tagOf w == tagBox
                    then do
                      key <- keyOfWord store w
                      pure (maybe (aiOpen index) (\k -> Map.findWithDefault (aiOpen index) k (aiBoxed index)) key)
                    else pure (IM.findWithDefault (aiOpen index) w (aiFast index))
    go [] _ = pure (all' p)

compileClause :: Ctx -> S.Clause -> IO Clause
compileClause ctx clause = do
  headPatterns <- case S.clauseHead clause of
    Compound _ as -> mapM (compileHeadArg ctx) as
    _ -> pure []
  body <- compileBody ctx (S.clauseBody clause)
  pure (Clause (max 1 (S.clauseNVars clause)) headPatterns body)

compileHeadArg :: Ctx -> Term -> IO Pattern
compileHeadArg ctx term = case term of
  Var v -> pure (PSlot v)
  Compound f as -> do
    fid <- internFunctor (symbols (ctxStore ctx)) f (length as)
    PStruct (funWord fid (length as)) <$> mapM (compileHeadArg ctx) as
  _ -> PWord <$> constantWord (ctxStore ctx) term

constantWord :: Store -> Term -> IO Word'
constantWord store term = case term of
  Atom a -> atmWord <$> internAtom (symbols store) a
  IntLit n
    | fitsImmediate n -> pure (intWord (fromInteger n))
    | otherwise -> box store (BInt n)
  FloatLit d -> box store (BFlt d)
  CharLit c -> pure (chrWord (fromEnum c))
  StrLit s -> box store (BStr s)
  _ -> fail "constantWord: not a constant"

-- | Goal arguments: slots, constants, structures, and arithmetic structures
-- that the reference would evaluate before the call.
compileArg :: Ctx -> Term -> IO Pattern
compileArg ctx term = case term of
  Var v -> pure (PSlot v)
  Compound f as -> do
    fid <- internFunctor (symbols (ctxStore ctx)) f (length as)
    args <- mapM (compileArg ctx) as
    pure $ case arithOp f (length as) of
      Just op -> PArith (funWord fid (length as)) op args
      Nothing -> PStruct (funWord fid (length as)) args
  _ -> PWord <$> constantWord (ctxStore ctx) term

arithFunctors :: [(String, Int, ArithOp)]
arithFunctors =
  [ ("plus", 2, OpPlus), ("minus", 2, OpMinus), ("mul", 2, OpMul), ("div", 2, OpDiv),
    ("mod", 2, OpMod), ("^", 2, OpPow), ("neg", 1, OpNeg), ("abs", 1, OpAbs),
    ("min", 2, OpMin), ("max", 2, OpMax)
  ]

arithOp :: String -> Int -> Maybe ArithOp
arithOp f n = case [op | (name, arity, op) <- arithFunctors, name == f, arity == n] of
  (op : _) -> Just op
  [] -> Nothing

compileExpr :: Ctx -> Term -> IO Expr
compileExpr ctx term = case term of
  IntLit n | fitsImmediate n -> pure (EImm (fromInteger n))
  IntLit n -> pure (EBig n)
  FloatLit d -> pure (EFlt d)
  Compound f as | Just op <- arithOp f (length as) -> EOp op <$> mapM (compileExpr ctx) as
  _ -> EPat <$> compileArg ctx term

compileBody :: Ctx -> [Term] -> IO [Goal]
compileBody ctx = mapM (compileGoal ctx) . concatMap flatten
  where
    flatten (Compound "," [a, b]) = flatten a ++ flatten b
    flatten t = [t]

compileGoal :: Ctx -> Term -> IO Goal
compileGoal ctx term = case term of
  Var v -> pure (GCallDyn True (PSlot v) [])
  Atom "true" -> pure GTrue
  Atom "fail" -> pure GFail
  Atom "false" -> pure GFail
  Atom "!" -> pure GCut
  Atom "nl" -> pure GNl
  Compound "$cut" [IntLit _] -> pure GCut
  Compound "," [_, _] -> GAnd <$> body term
  Compound ";" [Compound "->" [c, t], e] -> GIf <$> body c <*> body t <*> (Just <$> body e)
  Compound ";" [a, b] -> GOr <$> body a <*> body b
  Compound "->" [c, t] -> GIf <$> body c <*> body t <*> pure Nothing
  Compound "not" [g] -> GNot <$> body g
  Compound "once" [g] -> GOnce <$> body g
  Compound "forall" [c, a] -> do
    cg <- body c
    ag <- body a
    pure (GNot (cg ++ [GNot ag]))
  Compound "findall" [tmpl, g, l] -> GFindAll <$> arg tmpl <*> body g <*> arg l
  Compound "call" (p : args) -> GCallDyn False <$> arg p <*> mapM arg args
  Compound "unify" [a, b] -> GUnify <$> arg a <*> arg b
  Compound "equiv" [a, b] -> GEquiv <$> arg a <*> arg b
  Compound "neq" [a, b] -> GNeq <$> arg a <*> arg b
  Compound "is" [a, b] -> GIs <$> arg a <*> compileExpr ctx b
  Compound "gt" [a, b] -> GCmp CmpGt <$> compileExpr ctx a <*> compileExpr ctx b
  Compound "lt" [a, b] -> GCmp CmpLt <$> compileExpr ctx a <*> compileExpr ctx b
  Compound "gte" [a, b] -> GCmp CmpGte <$> compileExpr ctx a <*> compileExpr ctx b
  Compound "lte" [a, b] -> GCmp CmpLte <$> compileExpr ctx a <*> compileExpr ctx b
  Compound "var" [x] -> GCheck CkVar <$> arg x
  Compound "nonvar" [x] -> GCheck CkNonvar <$> arg x
  Compound "ground" [x] -> GCheck CkGround <$> arg x
  Compound "is_int" [x] -> GCheck CkInt <$> arg x
  Compound "is_float" [x] -> GCheck CkFloat <$> arg x
  Compound "is_num" [x] -> GCheck CkNum <$> arg x
  Compound "is_str" [x] -> GCheck CkStr <$> arg x
  Compound "is_atom" [x] -> GCheck CkAtom <$> arg x
  Compound "is_char" [x] -> GCheck CkChar <$> arg x
  Compound "is_list" [x] -> GCheck CkList <$> arg x
  Compound "write" [x] -> GWrite False <$> arg x
  Compound "print" [x] -> GWrite False <$> arg x
  Compound "writeln" [x] -> GWrite True <$> arg x
  Compound "phrase" [nt, l] -> GPhrase <$> arg nt <*> arg l
  Compound "phrase_from_file" [nt, path] -> GPhraseFile <$> arg nt <*> arg path
  Compound "emit" [nt] -> GEmit <$> arg nt
  Compound "minimize" [cost, g] -> GMinimize <$> arg cost <*> body g
  Compound "assert" [t] -> GAssert <$> arg t
  Compound "retract" [t] -> GRetract <$> arg t
  Compound "retractall" [t] -> GRetractAll <$> arg t
  Compound f as
    | (f, length as) `elem` leafBuiltins -> GLeaf f <$> mapM arg as
    | f `elem` constraintBuiltins -> GLeaf f <$> mapM arg as
    | otherwise -> userCall f as
  Atom f -> userCall f []
  _ -> pure (GError (TypeError "callable goal" term))
  where
    body t = compileBody ctx [t]
    arg = compileArg ctx
    unsupported what = do
      if ctxDynamic ctx then pure () else modifyIORef' (ctxProblems ctx) (what :)
      pure (GUnsupported term)
    userCall f as = case Map.lookup (f, length as) (ctxPreds ctx) of
      Just ref
        | Just p <- P.lookupPred (f, length as) (ctxProgram ctx), P.predIsTabled (ctxProgram ctx) p ->
            GTabled ref <$> mapM arg as
        | otherwise -> GCall ref <$> mapM arg as
      Nothing
        | P.nameHasFlag (ctxProgram ctx) f S.FlagDynamic -> GCallFacts (f, length as) <$> mapM arg as
        | otherwise -> pure (GError (UnknownPredicate (f, length as)))

-- | Builtins whose reference implementation is a pure function of their
-- arguments (and the preloaded files): run through 'GLeaf'.
leafBuiltins :: [(String, Int)]
leafBuiltins =
  [ ("str_concat", 3), ("str_length", 2), ("str_chars", 2), ("str_atom", 2), ("str_num", 2),
    ("str_upper", 2), ("str_lower", 2), ("str_lines", 2), ("term_str", 2), ("char_code", 2),
    ("read_file", 2), ("fmt", 4), ("wr", 3), ("sp", 2), ("nl", 2), ("seq", 3), ("padl", 4), ("padr", 4)
  ]

-- | Goals that post to or search the constraint store: also delegated to
-- the reference implementation, with the store passed in and out.
constraintBuiltins :: [String]
constraintBuiltins =
  [ "int_eq", "fd_ne", "fd_le", "fd_lt", "fd_ge", "fd_gt", "reify", "in", "label", "labeling",
    "all_different", "all_distinct"
  ]

-- | Compile a goal that a running program handed to @call/N@. The caller
-- exports it with its distinct unbound cells numbered @0, 1, ...@ and runs
-- the result in an activation block whose slots alias those cells, so no
-- plan ever holds a raw address.
compileGoalTerm :: Store -> P.Program -> Map.Map PredKey PredRef -> Term -> IO Goal
compileGoalTerm store program preds term = do
  problems <- newIORef []
  compileGoal (Ctx store program preds True problems) term

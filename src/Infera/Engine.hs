{-# OPTIONS_GHC -Wno-name-shadowing #-}

-- | The Infera v2 resolution engine.
--
-- The search is a lazy list of 'SearchItem's.  Predicate calls are solved in
-- isolation and their solutions are bound to the continuation with
-- 'bindSearch'; cut is implemented with markers that travel up the list until
-- they reach the activation that owns the barrier.  Predicates with a
-- (declared or soundly inferred) at-most-one determinism are committed after
-- their first solution; everything else falls back to full backtracking.
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

import Data.IntMap.Strict (IntMap)
import qualified Data.IntMap.Strict as IM
import Data.List (foldl', intercalate, nub, sortOn)
import Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map
import Data.Set (Set)
import qualified Data.Set as Set
import Data.Char (toLower, toUpper)
import Infera.Arith
import Infera.CLP
import Infera.Error
import Infera.Infer (inferProgram)
import Infera.Program
import Infera.Syntax
import Infera.Unify

-- ─── STATE ───────────────────────────────────────────────────────────────────

data OutputEvent
  = WriteEvent String
  | NewlineEvent
  deriving (Show, Eq)

data TableEntry = TableEntry
  { teComplete :: !Bool,
    -- | The fixpoint hit the iteration bound: answers are frozen but may be
    -- missing some.
    teTruncated :: !Bool,
    -- | (canonical answer, number of variables, output produced)
    teAnswers :: [(Term, Int, [OutputEvent])],
    teSet :: Set Term
  }
  deriving (Show)

data SolverState = SolverState
  { ssStore :: !Store,
    ssFresh :: !Int,
    -- | Output events, most recent first.
    ssOutput :: [OutputEvent],
    ssOutLen :: !Int,
    ssTables :: Map Term TableEntry
  }

data SearchItem
  = Found SolverState
  | BranchExhausted
  | BranchError SolveError
  | -- | A cut reached the barrier with this id.
    CutMarker !Int
  | -- | An answer stream consumed an incomplete table (tabling bookkeeping).
    ConsumedIncomplete Term

type Search = [SearchItem]

data Env = Env
  { envProg :: Program
  }

mkEnv :: Program -> Env
mkEnv = Env

maxResolutionDepth :: Int
maxResolutionDepth = 100000

-- | Upper bound on fixpoint iterations for one tabled call.  Predicates with
-- infinitely many answers (generators) hit this bound; declare them
-- @notable@ instead.
maxTableIterations :: Int
maxTableIterations = 300

initialState :: Int -> SolverState
initialState fresh =
  SolverState
    { ssStore = emptyStore,
      ssFresh = fresh,
      ssOutput = [],
      ssOutLen = 0,
      ssTables = Map.empty
    }

emit :: OutputEvent -> SolverState -> SolverState
emit e st = st {ssOutput = e : ssOutput st, ssOutLen = ssOutLen st + 1}

subst :: SolverState -> Subst
subst = stSubst . ssStore

-- ─── SEARCH COMBINATORS ──────────────────────────────────────────────────────

-- | Append two searches, stopping at (and keeping) a cut marker in the first.
thenSearch :: Search -> Search -> Search
thenSearch [] ys = ys
thenSearch (m@(CutMarker _) : _) _ = [m]
thenSearch (x : xs) ys = x : thenSearch xs ys

alts :: [Search] -> Search
alts = foldr thenSearch []

-- | Run a continuation on every solution.  A cut marker stops the
-- enumeration of further solutions and is propagated upwards.
bindSearch :: Search -> (SolverState -> Search) -> Search
bindSearch [] _ = []
bindSearch (Found st : rest) k = k st `thenSearch` bindSearch rest k
bindSearch (m@(CutMarker _) : _) _ = [m]
bindSearch (item : rest) k = item : bindSearch rest k

isMarker :: SearchItem -> Bool
isMarker (CutMarker _) = True
isMarker _ = False

isExhausted :: SearchItem -> Bool
isExhausted BranchExhausted = True
isExhausted _ = False

-- | Items that must survive an opaque sub-search: errors, exhaustion and
-- tabling dependencies (never solutions or markers).
passThrough :: Search -> [SearchItem]
passThrough items = [i | i <- items, keep i]
  where
    keep (BranchError _) = True
    keep BranchExhausted = True
    keep (ConsumedIncomplete _) = True
    keep _ = False

-- | Split a sub-search at its first solution: the items before it and the
-- solution (if any).  Markers are dropped.
firstFound :: Search -> ([SearchItem], Maybe SolverState)
firstFound = go []
  where
    go acc [] = (reverse acc, Nothing)
    go acc (Found st : _) = (reverse acc, Just st)
    go acc (CutMarker _ : rest) = go acc rest
    go acc (item : rest) = go (item : acc) rest

-- | Keep everything up to and including the first solution.
commitFirst :: Search -> Search
commitFirst items = case firstFound items of
  (pre, Just st) -> pre ++ [Found st]
  (pre, Nothing) -> pre

checked :: SolverState -> Either SolveError (Maybe Store) -> Search
checked _ (Left err) = [BranchError err]
checked _ (Right Nothing) = []
checked st (Right (Just store)) = [Found st {ssStore = store}]

-- ─── GOALS ───────────────────────────────────────────────────────────────────

solveGoals :: Env -> Int -> SolverState -> [Term] -> Search
solveGoals _ _ st [] = [Found st]
solveGoals env fuel st (g : gs) =
  bindSearch (solveGoal env fuel st g) (\st' -> solveGoals env fuel st' gs)

solveGoal :: Env -> Int -> SolverState -> Term -> Search
solveGoal env fuel st g0 =
  let store = ssStore st
      s = stSubst store
   in case walk s g0 of
        Var _ -> [BranchError (InstantiationError g0)]
        Atom "true" -> [Found st]
        Atom "fail" -> []
        Atom "false" -> []
        Atom "nl" -> [Found (emit NewlineEvent st)]
        Atom "!" -> [Found st]
        Compound "$cut" [IntLit b] -> [Found st, CutMarker (fromIntegral b)]
        Compound "," [a, b] -> solveGoals env fuel st [a, b]
        Compound ";" [Compound "->" [c, t], e] -> ifThenElse env fuel st c t e
        Compound ";" [a, b] -> alts [solveGoal env fuel st a, solveGoal env fuel st b]
        Compound "->" [c, t] -> ifThenElse env fuel st c t (Atom "fail")
        -- unification and comparison
        Compound "unify" [a, b] -> checked st (storeUnify store a b)
        Compound "equiv" [a, b] ->
          if deepWalk s a == deepWalk s b then [Found st] else []
        Compound "neq" [a, b] -> checked st (addDiseq a b store)
        Compound "is" [lhs, rhs] -> case evalArithSafe s rhs of
          Left err -> [BranchError err]
          Right Nothing -> [BranchError (InstantiationError (deepWalk s rhs))]
          Right (Just v) -> checked st (storeUnify store lhs v)
        Compound "gt" [a, b] -> comparison (== GT) st a b
        Compound "lt" [a, b] -> comparison (== LT) st a b
        Compound "gte" [a, b] -> comparison (/= LT) st a b
        Compound "lte" [a, b] -> comparison (/= GT) st a b
        -- CLP(Z)
        Compound "int_eq" [a, b] -> checked st (addRelation RelEq a b store)
        Compound "fd_ne" [a, b] -> checked st (addRelation RelNe a b store)
        Compound "fd_le" [a, b] -> checked st (addRelation RelLe a b store)
        Compound "fd_lt" [a, b] -> checked st (addRelation RelLe (Compound "plus" [a, IntLit 1]) b store)
        Compound "fd_ge" [a, b] -> checked st (addRelation RelLe b a store)
        Compound "fd_gt" [a, b] -> checked st (addRelation RelLe (Compound "plus" [b, IntLit 1]) a store)
        Compound "in" [x, r] -> inDomain st x r
        Compound "label" [l] -> labeling env st l
        Compound "labeling" [l] -> labeling env st l
        Compound "labeling" [options, l] -> case deepWalk s options of
          Compound "cons" [Compound "min" [cost], Atom "nil"] -> labelMinimum st cost l
          other -> [BranchError (TypeError "labeling options [min Cost]" other)]
        Compound "all_different" [l] -> allDifferent st l
        Compound "all_distinct" [l] -> allDifferent st l
        -- control
        Compound "call" (p : args) ->
          let goal = case walk s p of
                Atom f -> Compound f args
                Compound f as -> Compound f (as ++ args)
                other -> other
           in if isCallable goal
                then opaque (solveGoal env fuel st (replaceCuts (negate (ssFresh st) - 1) goal))
                else [BranchError (TypeError "callable" (deepWalk s goal))]
        Compound "phrase" [nt, l] ->
          let goal = case walk s nt of
                Atom f -> Compound f [l, nil]
                Compound f as -> Compound f (as ++ [l, nil])
                other -> Compound "call" [other, l, nil]
           in solveGoal env fuel st goal
        Compound "not" [g] -> negation env fuel st g
        Compound "once" [g] ->
          let sub = solveGoal env fuel st g
           in case firstFound sub of
                (pre, Just st') -> pre ++ [Found st']
                (pre, Nothing) -> pre
        Compound "forall" [c, a] ->
          negation env fuel st (Compound "," [c, Compound "not" [a]])
        Compound "findall" [tmpl, g, l] -> findAll env fuel st tmpl g l
        Compound "minimize" [cost, g] -> minimizeGoal env fuel st cost g
        -- output
        Compound "write" [x] -> [Found (emit (WriteEvent (showValue (deepEval s x))) st)]
        Compound "print" [x] -> [Found (emit (WriteEvent (showValue (deepEval s x))) st)]
        Compound "writeln" [x] -> [Found (emit NewlineEvent (emit (WriteEvent (showValue (deepEval s x))) st))]
        -- type checks
        Compound "var" [x] -> yesNo (isVar (walk s x))
        Compound "nonvar" [x] -> yesNo (not (isVar (walk s x)))
        Compound "ground" [x] -> yesNo (isGround s x)
        Compound "is_int" [x] -> yesNo (case walk s x of IntLit _ -> True; _ -> False)
        Compound "is_float" [x] -> yesNo (case walk s x of FloatLit _ -> True; _ -> False)
        Compound "is_num" [x] -> yesNo (case walk s x of IntLit _ -> True; FloatLit _ -> True; _ -> False)
        Compound "is_str" [x] -> yesNo (case walk s x of StrLit _ -> True; _ -> False)
        Compound "is_atom" [x] -> yesNo (case walk s x of Atom _ -> True; _ -> False)
        Compound "is_char" [x] -> yesNo (case walk s x of CharLit _ -> True; _ -> False)
        Compound "is_list" [x] -> yesNo (isProperList s x)
        -- strings
        Compound "str_concat" [a, b, c] -> strConcat st a b c
        Compound "str_length" [a, n] -> case walk s a of
          StrLit str -> checked st (storeUnify store n (IntLit (fromIntegral (length str))))
          other -> [BranchError (TypeError "string" other)]
        Compound "str_chars" [a, cs] -> case walk s a of
          StrLit str -> checked st (storeUnify store cs (mkList (map CharLit str) Nothing))
          Var _ -> case deepWalk s cs of
            t | Just chars <- charList t -> checked st (storeUnify store a (StrLit chars))
            other -> [BranchError (InstantiationError other)]
          other -> [BranchError (TypeError "string" other)]
        Compound "str_atom" [a, b] -> case (walk s a, walk s b) of
          (StrLit str, _) -> checked st (storeUnify store b (Atom str))
          (_, Atom at) -> checked st (storeUnify store a (StrLit at))
          (other, _) -> [BranchError (InstantiationError other)]
        Compound "str_num" [a, b] -> case (walk s a, walk s b) of
          (StrLit str, _) -> case parseTerm str of
            Right n@(IntLit _) -> checked st (storeUnify store b n)
            Right n@(FloatLit _) -> checked st (storeUnify store b n)
            _ -> []
          (_, n@(IntLit _)) -> checked st (storeUnify store a (StrLit (show n)))
          (_, n@(FloatLit _)) -> checked st (storeUnify store a (StrLit (show n)))
          (other, _) -> [BranchError (InstantiationError other)]
        Compound "str_upper" [a, b] -> strMap toUpper st a b
        Compound "str_lower" [a, b] -> strMap toLower st a b
        goal -> callPred env fuel st goal
  where
    yesNo True = [Found st]
    yesNo False = []
    isVar (Var _) = True
    isVar _ = False

showValue :: Term -> String
showValue (StrLit s) = s
showValue t = show t

charList :: Term -> Maybe String
charList t = case unfoldCons t of
  (xs, Nothing) -> mapM (\x -> case x of CharLit c -> Just c; _ -> Nothing) xs
  _ -> Nothing

isProperList :: Subst -> Term -> Bool
isProperList s t = case walk s t of
  Atom "nil" -> True
  Compound "cons" [_, tl] -> isProperList s tl
  _ -> False

comparison :: (Ordering -> Bool) -> SolverState -> Term -> Term -> Search
comparison ok st a b =
  let s = subst st
   in case (evalNumeric s a, evalNumeric s b) of
        (Left err, _) -> [BranchError err]
        (_, Left err) -> [BranchError err]
        (Right Nothing, _) -> [BranchError (InstantiationError (deepWalk s a))]
        (_, Right Nothing) -> [BranchError (InstantiationError (deepWalk s b))]
        (Right (Just x), Right (Just y)) -> [Found st | ok (compareNumeric x y)]

strConcat :: SolverState -> Term -> Term -> Term -> Search
strConcat st a b c =
  let s = subst st
      store = ssStore st
   in case (walk s a, walk s b, walk s c) of
        (StrLit x, StrLit y, _) -> checked st (storeUnify store c (StrLit (x ++ y)))
        (_, _, StrLit z) ->
          alts
            [ checked st (storeUnify store a (StrLit x) >>= maybe (Right Nothing) (\st' -> storeUnify st' b (StrLit y)))
            | (x, y) <- [splitAt i z | i <- [0 .. length z]]
            ]
        (x, y, _) -> [BranchError (InstantiationError (if isStr x then y else x))]
  where
    isStr (StrLit _) = True
    isStr _ = False

strMap :: (Char -> Char) -> SolverState -> Term -> Term -> Search
strMap f st a b = case walk (subst st) a of
  StrLit x -> checked st (storeUnify (ssStore st) b (StrLit (map f x)))
  other -> [BranchError (TypeError "string" other)]

-- | Run a sub-search whose cuts are local: drop markers, keep everything else.
opaque :: Search -> Search
opaque = filter (not . isMarker)

ifThenElse :: Env -> Int -> SolverState -> Term -> Term -> Term -> Search
ifThenElse env fuel st c t e =
  let sub = solveGoal env fuel st c
   in case firstFound sub of
        (pre, Just st') -> pre ++ solveGoal env fuel st' t
        (pre, Nothing) ->
          let errors = [i | i@(BranchError _) <- pre]
           in if not (null errors)
                then pre
                else
                  if any isExhausted pre
                    then pre
                    else pre ++ solveGoal env fuel st e

negation :: Env -> Int -> SolverState -> Term -> Search
negation env fuel st g =
  let sub = solveGoal env fuel st g
   in case firstFound sub of
        (pre, Just _) -> [i | i@(ConsumedIncomplete _) <- pre]
        (pre, Nothing) ->
          let errors = [i | i@(BranchError _) <- pre]
           in if not (null errors)
                then pre
                else if any isExhausted pre then pre else pre ++ [Found st]

findAll :: Env -> Int -> SolverState -> Term -> Term -> Term -> Search
findAll env fuel st tmpl g l =
  let sub = opaque (solveGoal env fuel st g)
      founds = [st' | Found st' <- sub]
      results = [deepWalk (subst st') tmpl | st' <- founds]
      pass = passThrough sub
      -- output produced by the collected solutions, in order
      outputs = concat [reverse (take (ssOutLen st' - ssOutLen st) (ssOutput st')) | st' <- founds]
      st1 = foldl' (flip emit) st outputs
   in case [e | e@(BranchError _) <- pass] of
        (e : _) -> [i | i@(ConsumedIncomplete _) <- pass] ++ [e]
        [] -> pass ++ checked st1 (storeUnify (ssStore st1) l (mkList results Nothing))

-- | Keep only the least-cost answer, retaining the first on ties. The goal's
-- bindings and output survive only for that answer. An error or incomplete
-- search cannot establish a minimum and therefore produces no winning answer.
minimizeGoal :: Env -> Int -> SolverState -> Term -> Term -> Search
minimizeGoal env fuel st cost g = finishMinimum (foldl' step (Nothing, []) (opaque (solveGoal env fuel st g)))
  where
    step (best, issues) (Found candidate) = case evalIntExpr (subst candidate) cost of
      Left err -> (best, BranchError err : issues)
      Right Nothing -> (best, BranchError (InstantiationError (deepWalk (subst candidate) cost)) : issues)
      Right (Just value) -> let best' = betterMinimum best (value, candidate) in best' `seq` (best', issues)
    step (best, issues) item = (best, item : issues)

betterMinimum :: Maybe (Integer, SolverState) -> (Integer, SolverState) -> Maybe (Integer, SolverState)
betterMinimum Nothing candidate@(value, _) = value `seq` Just candidate
betterMinimum old@(Just (value, _)) candidate@(value', _)
  | value' < value = Just candidate
  | otherwise = old

finishMinimum :: (Maybe (Integer, SolverState), Search) -> Search
finishMinimum (best, issues)
  | not (null issues) = reverse issues
  | otherwise = maybe [] (\(_, winner) -> [Found winner]) best

-- ─── CLP(Z) GOALS ────────────────────────────────────────────────────────────

parseBound :: Term -> Maybe Bound
parseBound (IntLit n) = Just (Fin n)
parseBound (Atom "inf") = Just NegInf
parseBound (Atom "sup") = Just PosInf
parseBound _ = Nothing

inDomain :: SolverState -> Term -> Term -> Search
inDomain st x r =
  let s = subst st
   in case deepWalk s r of
        Compound "range" [lo, hi]
          | Just l <- parseBound lo,
            Just h <- parseBound hi ->
              let targets = case deepWalk s x of
                    t@(Compound "cons" _) -> fst (unfoldCons t)
                    t -> [t]
               in checked st (foldl' (\acc t -> acc >>= maybe (Right Nothing) (addDomain t l h)) (Right (Just (ssStore st))) targets)
        other -> [BranchError (TypeError "range (Lo..Hi)" other)]

allDifferent :: SolverState -> Term -> Search
allDifferent st l =
  let s = subst st
      (xs, rest) = unfoldCons (deepWalk s l)
   in case rest of
        Just _ -> [BranchError (InstantiationError (deepWalk s l))]
        Nothing ->
          let pairs = [(a, b) | (i, a) <- zip [0 :: Int ..] xs, (j, b) <- zip [0 ..] xs, i < j]
           in checked st (foldl' (\acc (a, b) -> acc >>= maybe (Right Nothing) (addRelation RelNe a b)) (Right (Just (ssStore st))) pairs)

labeling :: Env -> SolverState -> Term -> Search
labeling _ st0 l =
  let s = subst st0
      (xs, _) = unfoldCons (deepWalk s l)
      vars = nub (concatMap termVars xs)
   in go st0 vars
  where
    go st vars =
      let store = ssStore st
          s = stSubst store
          pending = [v | v <- vars, Var w <- [walk s (Var v)], w == v]
       in case pending of
            [] -> [Found st]
            _ ->
              let withSize = [(v, domainOf store v >>= domainSize) | v <- pending]
               in case [v | (v, Nothing) <- withSize] of
                    (v : _) -> [BranchError (UnboundedDomain (Var v))]
                    [] ->
                      let v = case sortOn snd withSize of
                            ((w, _) : _) -> w
                            [] -> error "labeling: no pending variables"
                          values = maybe [] id (domainOf store v >>= domainValues)
                       in alts
                            [ case storeBind store v n of
                                Left err -> [BranchError err]
                                Right Nothing -> []
                                Right (Just store') -> go st {ssStore = store'} pending
                            | n <- values
                            ]

-- | Branch-and-bound labeling. Every new branch receives a strict upper
-- bound from the incumbent; propagation can reject it before enumeration.
-- Only finite integer variables may be labeled, and the cost must be ground
-- at a leaf. This returns one optimum, retaining the first encountered on ties.
labelMinimum :: SolverState -> Term -> Term -> Search
labelMinimum st0 cost l =
  let list = deepWalk (subst st0) l
      (xs, tailTerm) = unfoldCons list
   in case tailTerm of
        Just _ -> [BranchError (TypeError "proper list of integer variables" list)]
        Nothing
          | any invalid xs -> [BranchError (TypeError "list of integer variables" list)]
          | otherwise -> finishMinimum (go st0 (nub (concatMap termVars xs)) (Nothing, []))
  where
    invalid (Var _) = False
    invalid (IntLit _) = False
    invalid _ = True
    bound store best = case best of
      Nothing -> Right (Just store)
      Just (value, _) -> addRelation RelLe cost (IntLit (value - 1)) store
    go st vars acc@(best, issues) =
      let bounded = bound (ssStore st) best
       in case bounded of
            Left err -> (best, BranchError err : issues)
            Right Nothing -> acc
            Right (Just store) ->
              let candidate = st {ssStore = store}
                  pending = nub [w | v <- vars, Var w <- [walk (subst candidate) (Var v)]]
                  sizes = [(v, domainOf store v >>= domainSize) | v <- pending]
               in case pending of
                    [] -> case evalIntExpr (subst candidate) cost of
                      Left err -> (best, BranchError err : issues)
                      Right Nothing -> (best, BranchError (InstantiationError (deepWalk (subst candidate) cost)) : issues)
                      Right (Just value) -> (betterMinimum best (value, candidate), issues)
                    _ -> case [v | (v, Nothing) <- sizes] of
                      v : _ -> (best, BranchError (UnboundedDomain (Var v)) : issues)
                      [] -> case sortOn snd sizes of
                        [] -> acc
                        (v, _) : _ -> case domainOf store v of
                          Just (Domain (Fin lo) _ _) -> explore candidate pending v lo acc
                          _ -> (best, BranchError (UnboundedDomain (Var v)) : issues)
    -- Recompute the remaining domain after each improved incumbent instead of
    -- walking a stale list of values that propagation has already eliminated.
    explore st vars v lower acc@(best, issues) =
      case addDomain (Var v) (Fin lower) PosInf (ssStore st) >>= maybe (Right Nothing) (\store -> bound store best) of
        Left err -> (best, BranchError err : issues)
        Right Nothing -> acc
        Right (Just store) ->
          let values = case walk (stSubst store) (Var v) of
                IntLit value -> [value]
                _ -> maybe [] id (domainOf store v >>= domainValues)
           in case values of
                [] -> acc
                value : _ -> case storeBind store v value of
                  Left err -> (best, BranchError err : issues)
                  Right Nothing -> explore st vars v (value + 1) acc
                  Right (Just store') ->
                    let acc' = go st {ssStore = store'} vars acc
                     in acc' `seq` explore st vars v (value + 1) acc'

-- ─── PREDICATE CALLS ─────────────────────────────────────────────────────────

callPred :: Env -> Int -> SolverState -> Term -> Search
callPred env fuel st goal = case functorOf goal of
  Nothing -> [BranchError (TypeError "callable goal" goal)]
  Just key -> case lookupPred key (envProg env) of
    Nothing -> [BranchError (UnknownPredicate key)]
    Just p ->
      let s = subst st
          goalN = normArithTerm s goal
          args = case goalN of Compound _ as -> as; _ -> []
          argsW = map (deepWalk s) args
       in case selectSignature key p argsW of
            Left err -> [BranchError err]
            Right msig ->
              let raw =
                    if predIsTabled (envProg env) p
                      then evalTabled env fuel st p goalN
                      else evalClauses env fuel st p goalN argsW
                  withOut = case msig of
                    Just sig -> checkOutputs key sig args raw
                    Nothing -> raw
               in applyDeterminism key p msig argsW withOut

-- | Pick the declared signature matching the call (first whose input args
-- are ground), checking sorts of bound arguments.  Nothing when undeclared.
selectSignature :: PredKey -> Pred -> [Term] -> Either SolveError (Maybe Signature)
selectSignature key p argsW = case predDecls p of
  [] -> Right Nothing
  sigs ->
    case [sig | sig <- sigs, all inOk (zip (sigArgs sig) argsW)] of
      (sig : _) -> do
        mapM_ (checkSort key) (zip3 [1 ..] (sigArgs sig) argsW)
        Right (Just sig)
      [] ->
        let bad = [(i, a) | sig <- take 1 sigs, (i, ArgSpec _ ModeIn, a) <- zip3 [1 ..] (sigArgs sig) argsW, not (isGroundTerm a)]
         in case bad of
              ((i, a) : _) -> Left (ModeError key i a)
              [] -> Right Nothing
  where
    inOk (ArgSpec _ ModeIn, a) = isGroundTerm a
    inOk _ = True

checkSort :: PredKey -> (Int, ArgSpec, Term) -> Either SolveError ()
checkSort key (i, ArgSpec sort _, a)
  | sortMatches sort a = Right ()
  | otherwise = Left (SortError key i sort a)

-- | Does a (dereferenced) term conform to a sort?  Unbound parts always do.
sortMatches :: Sort -> Term -> Bool
sortMatches sort t = case (sort, t) of
  (_, Var _) -> True
  (SAny, _) -> True
  (SNone, _) -> True
  (SInt, IntLit _) -> True
  (SFloat, FloatLit _) -> True
  (SNum, IntLit _) -> True
  (SNum, FloatLit _) -> True
  (SStr, StrLit _) -> True
  (SChar, CharLit _) -> True
  (SAtom, Atom _) -> True
  (SList _, Atom "nil") -> True
  (SList e, Compound "cons" [h, tl]) -> sortMatches e h && sortMatches (SList e) tl
  _ -> False

-- | After the call: output arguments must be ground and every argument must
-- match its declared sort.
checkOutputs :: PredKey -> Signature -> [Term] -> Search -> Search
checkOutputs key sig args = map check
  where
    check (Found st) =
      let s = subst st
          argsW = map (deepWalk s) args
          problems =
            [ err
            | (i, ArgSpec sort mode, a) <- zip3 [1 ..] (sigArgs sig) argsW,
              err <- outErr i sort mode a
            ]
       in case problems of
            (e : _) -> BranchError e
            [] -> Found st
    check item = item
    outErr i sort mode a
      | mode == ModeOut && not (isGroundTerm a) = [OutputModeError key i a]
      | not (sortMatches sort a) = [SortError key i sort a]
      | otherwise = []

-- | Enforce declared determinism, or commit on soundly inferred semidet.
applyDeterminism :: PredKey -> Pred -> Maybe Signature -> [Term] -> Search -> Search
applyDeterminism key p msig argsW items = case msig of
  Just sig -> case sigDet sig of
    Det -> requireOne Det (commitFirst items)
    Semidet -> commitFirst items
    Multi -> requireOne Multi items
    Nondet -> items
  Nothing ->
    let inf = predInferred p
        switchGround = all (\i -> i < length argsW && isGroundTerm (argsW !! i)) (sigSwitch inf)
     in if sigDet inf == Semidet && switchGround then commitFirst items else items
  where
    requireOne d xs =
      let hasFound = any isFound xs
       in if hasFound then xs else xs ++ [BranchError (DetError key d 0)]
    isFound (Found _) = True
    isFound _ = False

-- | Try the (indexed) candidate clauses of a predicate.
evalClauses :: Env -> Int -> SolverState -> Pred -> Term -> [Term] -> Search
evalClauses env fuel st p goalN argsW
  | fuel <= 0 = [BranchExhausted]
  | otherwise =
      let keys = if predIsIndexed (envProg env) p then map indexKey argsW else []
          cands = candidateClauses p keys
          base = ssFresh st
       in consumeMarkers base (alts [tryClause env fuel st base goalN (predClauses p IM.! ci) | ci <- cands])

consumeMarkers :: Int -> Search -> Search
consumeMarkers base = filter keep
  where
    keep (CutMarker b) = b /= base
    keep _ = True

tryClause :: Env -> Int -> SolverState -> Int -> Term -> Clause -> Search
tryClause env fuel st base goal cl =
  let hd = renameTerm base (clauseHead cl)
      body = map (renameBody base) (clauseBody cl)
      st1 = st {ssFresh = base + max 1 (clauseNVars cl)}
   in case storeUnify (ssStore st1) goal hd of
        Left err -> [BranchError err]
        Right Nothing -> []
        Right (Just store') -> solveGoals env (fuel - 1) st1 {ssStore = store'} body

-- ─── TABLING ─────────────────────────────────────────────────────────────────

-- | Tabled evaluation (linear tabling with fixpoint iteration).  Calls whose
-- arguments involve constrained variables, and answers that would carry
-- constraints, fall back to plain evaluation.
evalTabled :: Env -> Int -> SolverState -> Pred -> Term -> Search
evalTabled env fuel st0 p goal
  | any (isConstrained store0) callVars = plain st0
  | otherwise = case Map.lookup callKey (ssTables st0) of
      Just te
        | teComplete te -> [BranchExhausted | teTruncated te] ++ consumeAnswers st0 (teAnswers te)
        | otherwise -> ConsumedIncomplete callKey : consumeAnswers st0 (teAnswers te)
      Nothing -> fixpoint (0 :: Int) (ssTables st0) [] Set.empty
  where
    store0 = ssStore st0
    s0 = stSubst store0
    (callKey, callVars) = canonicalize s0 goal
    argsW = case deepWalk s0 goal of Compound _ as -> as; _ -> []
    plain st = evalClauses env fuel st p goal argsW

    fixpoint iteration tables answers answerSet =
      let st1 = st0 {ssTables = Map.insert callKey (TableEntry False False answers answerSet) tables}
          items = evalClauses env fuel st1 p goal argsW
          founds = [stf | Found stf <- items]
          extracted = map extract founds
          unsafe = any (\(_, _, _, bad) -> bad) extracted
          fresh = dedup answerSet [(a, n, o) | (a, n, o, _) <- extracted]
          answers' = answers ++ fresh
          answerSet' = foldl' (\acc (a, _, _) -> Set.insert a acc) answerSet fresh
          deps = nub [k | ConsumedIncomplete k <- items, k /= callKey]
          others = [i | i@(BranchError _) <- items] ++ [BranchExhausted | any isExhausted items]
          completed = Map.unions (Map.filter teComplete tables : [Map.filter teComplete (ssTables stf) | stf <- founds])
          tables' = Map.union completed (Map.delete callKey tables)
          converged = null fresh
          gaveUp = iteration >= maxTableIterations
       in if unsafe
            then plain st0
            else
              if converged || gaveUp
                then
                  let tables'' =
                        if null deps
                          then Map.insert callKey (TableEntry True (not converged) answers' answerSet') tables'
                          else tables'
                      stC = st0 {ssTables = tables''}
                   in map ConsumedIncomplete deps
                        ++ others
                        ++ [BranchExhausted | gaveUp]
                        ++ consumeAnswers stC answers'
                else fixpoint (iteration + 1) tables' answers' answerSet'

    extract stf =
      let sf = subst stf
          (ans, vs) = canonicalize sf goal
          bad = any (isConstrained (ssStore stf)) vs
          out = reverse (take (ssOutLen stf - ssOutLen st0) (ssOutput stf))
       in (ans, length vs, out, bad)

    dedup _ [] = []
    dedup seen ((a, n, o) : rest)
      | Set.member a seen = dedup seen rest
      | otherwise = (a, n, o) : dedup (Set.insert a seen) rest

    consumeAnswers st answers =
      alts
        [ let ans' = instantiate (ssFresh st) ans
              st' = foldl' (flip emit) st {ssFresh = ssFresh st + n} out
           in checked st' (storeUnify (ssStore st') goal ans')
        | (ans, n, out) <- answers
        ]

-- ─── QUERIES AND ANSWERS ─────────────────────────────────────────────────────

solveQuery :: Program -> Query -> Search
solveQuery prog q =
  let barrier = -1
      goals = map (replaceCuts barrier) (queryGoals q)
   in consumeMarkers barrier (solveGoals (mkEnv prog) maxResolutionDepth (initialState (queryNVars q)) goals)

data Answer = Answer
  { answerBindings :: [(String, Term)],
    -- | Residual domains and constraints, rendered.
    answerResiduals :: [String],
    answerOutput :: [OutputEvent],
    -- | Display names for variable ids occurring in the bindings.
    answerNames :: IntMap String
  }
  deriving (Show, Eq)

-- | Project a solution onto the query's named variables, naming internal
-- variables @_0, _1, ...@ and keeping only constraints that reach a visible
-- variable.
projectAnswer :: Query -> SolverState -> Answer
projectAnswer q st =
  let store = ssStore st
      s = stSubst store
      names = queryNames q
      bindingsRaw = [(n, deepEval s (Var v)) | (n, v) <- names]
      -- A query variable bound to an otherwise unnamed free variable lends it
      -- its name instead of showing as a binding.
      (aliases, bindings) = foldl' alias (IM.empty, []) bindingsRaw
      alias (al, bs) (n, t) = case t of
        Var w
          | w == lookupVar n -> (al, bs)
          | not (IM.member w al) && w `notElem` map snd names -> (IM.insert w n al, bs)
        _ -> (al, bs ++ [(n, t)])
      lookupVar n = maybe (-1) id (lookup n names)
      seedVars = nub (map snd names ++ concatMap (termVars . snd) bindingsRaw)
      constraints = stConstraints store
      relevant = closeOver seedVars constraints
      relevantVars = nub (seedVars ++ concatMap constraintVars relevant)
      domains = [(v, d) | v <- relevantVars, Just d <- [domainOf store v], isFree v]
      isFree v = case walk s (Var v) of Var w -> w == v; _ -> False
      -- naming
      allTerms = map snd bindings ++ map constraintTerm relevant ++ [Var v | (v, _) <- domains]
      internal = nub [v | t <- allTerms, v <- termVars t, v `notElem` map snd names, not (IM.member v aliases)]
      internalNames = IM.fromList (zip internal [0 :: Int ..])
      nameOf v = case lookup v [(vid, n) | (n, vid) <- names] of
        Just n -> n
        Nothing -> case IM.lookup v aliases of
          Just n -> n
          Nothing -> case IM.lookup v internalNames of
            Just i -> "_" ++ show i
            Nothing -> showVarDefault v
      render = showTermWith nameOf
      residualDomains = [nameOf v ++ " in " ++ showDomain d | (v, d) <- domains]
      residualConstraints = [render (deepEval s (constraintTerm c)) | c <- relevant]
      displayNames = IM.fromList [(v, nameOf v) | t <- map snd bindings, v <- termVars t]
   in Answer
        { answerBindings = bindings,
          answerResiduals = residualDomains ++ residualConstraints,
          answerOutput = reverse (ssOutput st),
          answerNames = displayNames
        }
  where
    closeOver seed cs = go (Set.fromList seed) [] cs
      where
        go known selected remaining =
          let (hit, miss) = partitionBy (\c -> any (`Set.member` known) (constraintVars c)) remaining
              known' = foldl' (flip Set.insert) known (concatMap constraintVars hit)
           in if null hit then reverse selected else go known' (reverse hit ++ selected) miss
        partitionBy f xs = ([x | x <- xs, f x], [x | x <- xs, not (f x)])

showAnswer :: Answer -> String
showAnswer answer
  | null pieces = "true."
  | otherwise = intercalate ", " pieces
  where
    nameOf v = IM.findWithDefault (showVarDefault v) v (answerNames answer)
    pieces =
      [v ++ " = " ++ showTermWith nameOf t | (v, t) <- answerBindings answer]
        ++ answerResiduals answer

renderOutputEvent :: OutputEvent -> String
renderOutputEvent (WriteEvent text) = text
renderOutputEvent NewlineEvent = "\n"

data QuerySummary = QuerySummary
  { summaryAnswers :: [Answer],
    summaryErrors :: [SolveError],
    summaryExhausted :: Bool
  }
  deriving (Show, Eq)

summarizeSearch :: Query -> Search -> QuerySummary
summarizeSearch q items =
  QuerySummary
    { summaryAnswers = [projectAnswer q st | Found st <- items],
      summaryErrors = nub [err | BranchError err <- items],
      summaryExhausted = any isExhausted items
    }

solveAll :: Program -> Query -> QuerySummary
solveAll prog q = summarizeSearch q (solveQuery prog q)

-- | Build an inferred program from source text (clauses and declarations).
loadProgramText :: String -> Either String Program
loadProgramText src = do
  items <- parseProgram src
  pure (inferProgram (buildProgram items))

-- | Convenience for tests and scripting: run a query against program text and
-- render the answers.
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

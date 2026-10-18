{-# OPTIONS_GHC -Wno-name-shadowing #-}

-- | Retained lazy-list resolver for independent parity tests during both
-- engine roadmap steps. Public resolution uses Infera.Machine.Control.
--
-- The search is a lazy list of 'SearchItem's.  Predicate calls are solved in
-- isolation and their solutions are bound to the continuation with
-- 'bindSearch'; cut is implemented with markers that travel up the list until
-- they reach the activation that owns the barrier.  Predicates with a
-- (declared or soundly inferred) at-most-one determinism are committed after
-- their first solution; everything else falls back to full backtracking.
module Infera.Engine.Reference
  ( -- * State and results
    OutputEvent (..),
    SolverState (..),
    TableEntry (..),
    SearchItem (..),
    Search,
    Env (..),
    mkEnv,
    initialState,
    maxResolutionDepth,
    maxTableIterations,

    -- * Solving
    solveGoals,
    solveGoal,
    renameApart,
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
import Data.List (foldl', intercalate, mapAccumL, nub, sortOn)
import Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map
import Data.Set (Set)
import qualified Data.Set as Set
import Data.Char (toLower, toUpper)
import Infera.Arith
import Infera.CLP
import Infera.Error
import qualified Infera.Engine.Contracts as Contracts
import Infera.Infer (builtinDet, inferProgram)
import Infera.Machine.Trace.Types (sourceMap)
import Infera.Program
import Infera.Purity (describeViolation, programViolations)
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
    ssTables :: Map Term TableEntry,
    -- | Facts of dynamic predicates (assert/retract), canonical with their
    -- variable counts, per predicate in assertion order.
    ssDynamic :: Map PredKey [(Term, Int)]
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
  { envProg :: Program,
    -- | Contents of files preloaded for read_file / phrase_from_file.
    envFiles :: Map String String
  }

mkEnv :: Program -> Env
mkEnv prog = Env prog (progFiles prog)

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
      ssTables = Map.empty,
      ssDynamic = Map.empty
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
        Compound "reify" [relation, truth] -> reifyRelation st relation truth
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
          let input = case walk s l of
                StrLit str -> mkList (map CharLit str) Nothing
                _ -> l
           in solveGoal env fuel st (phraseGoal (walk s nt) input nil)
        Compound "phrase_from_file" [nt, path] -> withFile env s path $ \contents ->
          solveGoal env fuel st (phraseGoal (walk s nt) (mkList (map CharLit contents) Nothing) nil)
        Compound "read_file" [path, str] -> withFile env s path $ \contents ->
          checked st (storeUnify store str (StrLit contents))
        Compound "emit" [nt] -> emitGoal env fuel st nt
        -- dynamic facts
        Compound "assert" [t] -> assertFact env st t
        Compound "retract" [t] -> retractFact st t
        Compound "retractall" [t] -> retractAll st t
        -- pure DCG helpers: NT S0 S
        Compound "seq" [cs, s0, s1] -> seqGoal st cs s0 s1
        Compound "wr" [x, s0, s1] -> dcgText st (showValue (deepEval s x)) s0 s1
        Compound "nl" [s0, s1] -> dcgText st "\n" s0 s1
        Compound "sp" [s0, s1] -> dcgText st " " s0 s1
        Compound "padl" [x, w, s0, s1] -> padGoal True st x w s0 s1
        Compound "padr" [x, w, s0, s1] -> padGoal False st x w s0 s1
        Compound "fmt" [f, args, s0, s1] -> case formatText s f args of
          Left err -> [BranchError err]
          Right text -> dcgText st text s0 s1
        Compound "char_code" [c, n] -> case (walk s c, walk s n) of
          (CharLit ch, _) -> checked st (storeUnify store n (IntLit (fromIntegral (fromEnum ch))))
          (_, IntLit code) -> checked st (storeUnify store c (CharLit (toEnum (fromIntegral code))))
          (other, _) -> [BranchError (InstantiationError other)]
        Compound "term_str" [t, str] -> checked st (storeUnify store str (StrLit (showValue (deepEval s t))))
        Compound "str_lines" [a, l] -> case walk s a of
          StrLit str -> checked st (storeUnify store l (mkList (map StrLit (lines str)) Nothing))
          other -> [BranchError (TypeError "string" other)]
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

-- | The goal that runs a DCG non-terminal between two list arguments.
phraseGoal :: Term -> Term -> Term -> Term
phraseGoal nt s0 s = case nt of
  Atom f -> Compound f [s0, s]
  Compound f as -> Compound f (as ++ [s0, s])
  other -> Compound "call" [other, s0, s]

-- | Unify @s0@ with the characters of a text followed by @s@.
dcgText :: SolverState -> String -> Term -> Term -> Search
dcgText st text s0 s = checked st (storeUnify (ssStore st) s0 (mkList (map CharLit text) (Just s)))

-- | @seq Xs@ as a DCG: the elements of Xs (a list or a string) in sequence.
-- With Xs unbound and a proper input list, enumerates prefixes.
seqGoal :: SolverState -> Term -> Term -> Term -> Search
seqGoal st cs s0 s =
  let sub = subst st
      store = ssStore st
   in case deepWalk sub cs of
        StrLit str -> dcgText st str s0 s
        t | (xs, Nothing) <- unfoldCons t -> checked st (storeUnify store s0 (mkList xs (Just s)))
        _ -> case deepWalk sub s0 of
          t0 | (xs, Nothing) <- unfoldCons t0 ->
            alts
              [ checked st (storeUnify store cs (mkList pre Nothing) >>= maybe (Right Nothing) (\st' -> storeUnify st' s (mkList rest Nothing)))
              | i <- [0 .. length xs],
                let (pre, rest) = splitAt i xs
              ]
          other -> [BranchError (InstantiationError other)]

padGoal :: Bool -> SolverState -> Term -> Term -> Term -> Term -> Search
padGoal left st x w s0 s =
  let sub = subst st
      text = showValue (deepEval sub x)
   in case walk sub w of
        IntLit n ->
          let fill = replicate (fromIntegral n - length text) ' '
           in dcgText st (if left then fill ++ text else text ++ fill) s0 s
        other -> [BranchError (TypeError "integer width" other)]

-- | @fmt Format Args@: ~w term, ~s string or character list, ~d integer,
-- ~a atom, ~n newline, ~~ tilde.
formatText :: Subst -> Term -> Term -> Either SolveError String
formatText s f args = case (walk s f, unfoldCons (deepWalk s args)) of
  (StrLit format, (as, Nothing)) -> go format as
  (StrLit _, _) -> Left (TypeError "argument list" (deepWalk s args))
  (other, _) -> Left (TypeError "format string" other)
  where
    go ('~' : '~' : rest) as = ('~' :) <$> go rest as
    go ('~' : 'n' : rest) as = ('\n' :) <$> go rest as
    go ('~' : c : rest) (a : as) | c `elem` "wsda" = do
      piece <- directive c (deepEval s a)
      (piece ++) <$> go rest as
    go ('~' : c : _) [] | c `elem` "wsda" = Left (UserError "fmt: not enough arguments for the format string")
    go ('~' : c : _) _ = Left (UserError ("fmt: unknown directive ~" ++ [c]))
    go (c : rest) as = (c :) <$> go rest as
    go [] [] = Right []
    go [] _ = Left (UserError "fmt: too many arguments for the format string")
    directive 'w' t = Right (showValue t)
    directive 'a' (Atom a) = Right a
    directive 'd' (IntLit n) = Right (show n)
    directive 's' (StrLit str) = Right str
    directive 's' t | Just str <- charList t = Right str
    directive c t = Left (TypeError (case c of 'd' -> "integer for ~d"; 'a' -> "atom for ~a"; _ -> "string for ~s") t)

-- | Run a file-backed builtin against the preloaded file contents.
withFile :: Env -> Subst -> Term -> (String -> Search) -> Search
withFile env s path k = case walk s path of
  StrLit p -> case Map.lookup p (envFiles env) of
    Just contents -> k contents
    Nothing -> [BranchError (UserError ("read_file: \"" ++ p ++ "\" was not loaded (paths must be string literals in the program or query)"))]
  other -> [BranchError (TypeError "file path string" other)]

-- | @emit NT@: run the DCG once and append its text to the output.
emitGoal :: Env -> Int -> SolverState -> Term -> Search
emitGoal env fuel st nt =
  let cs = Var (ssFresh st)
      st1 = st {ssFresh = ssFresh st + 1}
      sub = solveGoal env fuel st1 (phraseGoal (walk (subst st) nt) cs nil)
   in case firstFound sub of
        (pre, Just st') -> case charList (deepWalk (subst st') cs) of
          Just text -> pre ++ [Found (emit (WriteEvent text) st')]
          Nothing -> pre ++ [BranchError (TypeError "character list from the DCG" (deepWalk (subst st') cs))]
        (pre, Nothing) -> pre

-- ─── DYNAMIC FACTS ───────────────────────────────────────────────────────────

dynamicKey :: Env -> Subst -> Term -> Either SolveError (PredKey, Term)
dynamicKey env s t =
  let fact = deepWalk s t
   in case functorOf fact of
        Nothing -> Left (TypeError "callable fact" fact)
        Just key@(name, _)
          | nameHasFlag (envProg env) name FlagDynamic -> Right (key, fact)
          | otherwise -> Left (UserError (showPredKey key ++ " is not declared dynamic (add `" ++ name ++ " : dynamic.`)"))

assertFact :: Env -> SolverState -> Term -> Search
assertFact env st t = case dynamicKey env (subst st) t of
  Left err -> [BranchError err]
  Right (key, fact) ->
    let (canon, vs) = canonicalize emptySubst fact
     in [Found st {ssDynamic = Map.insertWith (flip (++)) key [(canon, length vs)] (ssDynamic st)}]

-- | Facts of a dynamic predicate, instantiated with fresh variables.
dynamicFacts :: SolverState -> PredKey -> [(Int, Term, SolverState)]
dynamicFacts st key =
  [ (i, instantiate (ssFresh st) canon, st {ssFresh = ssFresh st + n})
  | (i, (canon, n)) <- zip [0 ..] (Map.findWithDefault [] key (ssDynamic st))
  ]

callDynamic :: SolverState -> PredKey -> Term -> Search
callDynamic st key goal =
  alts [checked st' (storeUnify (ssStore st') goal fact) | (_, fact, st') <- dynamicFacts st key]

retractFact :: SolverState -> Term -> Search
retractFact st t = case functorOf (deepWalk (subst st) t) of
  Nothing -> [BranchError (TypeError "callable fact" t)]
  Just key ->
    alts
      [ checked (dropFact i st') (storeUnify (ssStore st') t fact)
      | (i, fact, st') <- dynamicFacts st key
      ]
  where
    dropFact i st' = st' {ssDynamic = Map.adjust (\fs -> [f | (j, f) <- zip [0 :: Int ..] fs, j /= i]) (fst (functorKey st')) (ssDynamic st')}
    functorKey st' = case functorOf (deepWalk (subst st') t) of Just k -> (k, ()); Nothing -> (("", 0), ())

retractAll :: SolverState -> Term -> Search
retractAll st t = case functorOf (deepWalk (subst st) t) of
  Nothing -> [BranchError (TypeError "callable fact" t)]
  Just key ->
    let keep = [ (canon, n) | (i, fact, st') <- dynamicFacts st key, let (canon, n) = Map.findWithDefault [] key (ssDynamic st) !! i, Nothing <- [unifyPlain (subst st') t fact] ]
     in [Found st {ssDynamic = Map.insert key keep (ssDynamic st)}]

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
   in case (walk s a, walk s b) of
        (CharLit x, CharLit y) -> [Found st | ok (compare x y)]
        (StrLit x, StrLit y) -> [Found st | ok (compare x y)]
        (Atom x, Atom y) -> [Found st | ok (compare x y)]
        _ -> numericComparison ok st a b

numericComparison :: (Ordering -> Bool) -> SolverState -> Term -> Term -> Search
numericComparison ok st a b =
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
      -- Each solution is a copy: variables created inside the findall are
      -- renamed apart, per solution and from everything created after it.
      -- Variables that existed before the findall stay shared.
      (results, fresh') = renameApart (ssFresh st) [deepWalk (subst st') tmpl | st' <- founds]
      pass = passThrough sub
      -- output produced by the collected solutions, in order
      outputs = concat [reverse (take (ssOutLen st' - ssOutLen st) (ssOutput st')) | st' <- founds]
      st1 = (foldl' (flip emit) st outputs) {ssFresh = fresh'}
   in case [e | e@(BranchError _) <- pass] of
        (e : _) -> [i | i@(ConsumedIncomplete _) <- pass] ++ [e]
        [] -> pass ++ checked st1 (storeUnify (ssStore st1) l (mkList results Nothing))

-- | Rename the variables at or above @start@ in each term to fresh ids,
-- with a separate namespace per term; returns the next free id.
renameApart :: VarId -> [Term] -> ([Term], VarId)
renameApart start terms = let (final, renamed) = mapAccumL one start terms in (renamed, final)
  where
    one next t =
      let inside = nub [v | v <- termVarIds t, v >= start]
          table = IM.fromList (zip inside [next ..])
          rename term = case term of
            Var v -> Var (IM.findWithDefault v v table)
            Compound f as -> Compound f (map rename as)
            _ -> term
       in (next + length inside, rename t)

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
               in checked st (addDomains targets l h (ssStore st))
        other -> [BranchError (TypeError "range (Lo..Hi)" other)]

allDifferent :: SolverState -> Term -> Search
allDifferent st l =
  let s = subst st
      (xs, rest) = unfoldCons (deepWalk s l)
   in case rest of
        Just _ -> [BranchError (InstantiationError (deepWalk s l))]
        Nothing -> checked st (addAllDifferent xs (ssStore st))

-- | A Boolean view of an integer constraint. Posting it does not execute a
-- goal or enumerate alternatives: both the relation and its truth value are
-- maintained by the constraint store.
reifyRelation :: SolverState -> Term -> Term -> Search
reifyRelation st relation truth =
  let store = ssStore st
      post rel a b = checked st (addReified rel a b truth store)
   in case walk (subst st) relation of
        Compound "int_eq" [a, b] -> post RelEq a b
        Compound "fd_ne" [a, b] -> post RelNe a b
        Compound "fd_le" [a, b] -> post RelLe a b
        Compound "fd_lt" [a, b] -> post RelLe (Compound "plus" [a, IntLit 1]) b
        Compound "fd_ge" [a, b] -> post RelLe b a
        Compound "fd_gt" [a, b] -> post RelLe (Compound "plus" [b, IntLit 1]) a
        other@(Var _) -> [BranchError (InstantiationError other)]
        other -> [BranchError (TypeError "integer relation (#=, #!=, #<, #<=, #>, #>=)" other)]

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
    Nothing
      | nameHasFlag (envProg env) (fst key) FlagDynamic -> callDynamic st key goal
      | otherwise -> [BranchError (UnknownPredicate key)]
    Just p ->
      let s = subst st
          goalN = normArithTerm s goal
          args = case goalN of Compound _ as -> as; _ -> []
          argsW = map (deepWalk s) args
       in case Contracts.selectSignature key p argsW of
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

-- | After the call: output arguments must be ground and every argument must
-- match its declared sort.
checkOutputs :: PredKey -> Signature -> [Term] -> Search -> Search
checkOutputs key sig args = map check
  where
    check (Found st) =
      let s = subst st
          argsW = map (deepWalk s) args
       in case Contracts.checkOutputs key sig argsW of
            Just e -> BranchError e
            Nothing -> Found st
    check item = item

-- | Enforce declared determinism, or commit on soundly inferred semidet.
applyDeterminism :: PredKey -> Pred -> Maybe Signature -> [Term] -> Search -> Search
applyDeterminism key p msig argsW items = case msig of
  Just sig -> case sigDet sig of
    Det -> requireOne Det (commitFirst items)
    Semidet -> commitFirst items
    Multi -> requireOne Multi items
    Nondet -> items
  Nothing ->
    if Contracts.commitsAfterSuccess p Nothing argsW then commitFirst items else items
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

-- | Tabled evaluation (linear tabling with fixpoint iteration). Positive
-- same-variant linear recursion consumes only the preceding round's new
-- answers. Other recursive shapes retain the general fixpoint evaluator.
-- Calls whose arguments involve constrained variables, and answers that carry
-- constraints, fall back to plain evaluation.
evalTabled :: Env -> Int -> SolverState -> Pred -> Term -> Search
evalTabled env fuel st0 p goal
  | any (isConstrained store0) callVars = plain st0
  | otherwise = case Map.lookup callKey (ssTables st0) of
      Just te
        | teComplete te -> [BranchExhausted | teTruncated te] ++ consumeAnswers st0 (teAnswers te)
        | otherwise -> ConsumedIncomplete callKey : consumeAnswers st0 (teAnswers te)
      Nothing -> fixpoint (case deltaClauses of Just _ -> True; Nothing -> False)
        (0 :: Int) (ssTables st0) [] Set.empty []
  where
    store0 = ssStore st0
    s0 = stSubst store0
    (callKey, callVars) = canonicalize s0 goal
    argsW = case deepWalk s0 goal of Compound _ as -> as; _ -> []
    plain st = evalClauses env fuel st p goal argsW

    -- A delta is sound only when removing an old derivation cannot change a
    -- later call's behaviour. Keep the initial fast path deliberately narrow:
    -- one self-call first in a clause, exactly the current variant, followed
    -- by acyclic positive goals with no declared contracts, effects or CLP.
    -- In particular this excludes mutual/nonlinear recursion and all control
    -- constructs; their ordering, errors and cuts still use the old evaluator.
    deltaClauses
      | not (safeContract p) || inferredCommit = Nothing
      | otherwise = fmap (map fst . filter snd) (mapM classifyClause candidates)
      where
        inferredCommit = Contracts.commitsAfterSuccess p Nothing argsW
        candidates = candidateClauses p
          (if predIsIndexed (envProg env) p then map indexKey argsW else [])
        classifyClause ci =
          let cl = predClauses p IM.! ci
           in case clauseBody cl of
                recursive : rest
                  | functorOf recursive == Just (predKey p) ->
                      if all (safeGoal (Set.singleton (predKey p))) rest && sameVariant cl recursive
                        then Just (ci, True)
                        else Nothing
                body
                  | all (safeGoal (Set.singleton (predKey p))) body -> Just (ci, False)
                  | otherwise -> Nothing
        sameVariant cl recursive =
          let base = ssFresh st0
           in case storeUnify store0 goal (renameTerm base (clauseHead cl)) of
                Left _ -> False
                Right Nothing -> True -- This clause cannot contribute.
                Right (Just store) ->
                  let s = stSubst store
                   in fst (canonicalize s (normArithTerm s (renameTerm base recursive))) == callKey
        safeContract predicate =
          null (predDecls predicate)
            && not (predIsUnsafe (envProg env) predicate)
            && not (predIsDynamic (envProg env) predicate)
        safeGoal _ (Atom name) | name `elem` ["true", "fail", "false"] = True
        safeGoal _ (Compound "unify" [_, _]) = True
        safeGoal seen term = case functorOf term of
          Just key@(name, arity)
            | builtinDet name arity == Nothing && Set.notMember key seen ->
                case lookupPred key (envProg env) of
                  Just predicate ->
                    safeContract predicate
                      && all (all (safeGoal (Set.insert key seen)) . clauseBody)
                        (IM.elems (predClauses predicate))
                  Nothing -> False
          _ -> False

    fixpoint useDelta iteration tables answers answerSet delta =
      let visible = if useDelta then delta else answers
          st1 = st0 {ssTables = Map.insert callKey (TableEntry False False visible answerSet) tables}
          items = case (useDelta && iteration > 0, deltaClauses) of
            (True, Just recursive) ->
              let base = ssFresh st1
               in if fuel <= 0 then [BranchExhausted] else
                    consumeMarkers base (alts
                      [tryClause env fuel st1 base goal (predClauses p IM.! ci) | ci <- recursive])
            _ -> evalClauses env fuel st1 p goal argsW
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
          -- Resource exhaustion can make an otherwise independent base clause
          -- observable on every round. Restart with the general algorithm
          -- rather than silently dropping such an issue on subsequent rounds.
          deltaIssue = useDelta && (not (null deps) || not (null others))
       in if deltaIssue
            then fixpoint False 0 (ssTables st0) [] Set.empty []
            else if unsafe
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
                else fixpoint useDelta (iteration + 1) tables' answers' answerSet' fresh

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
  located <- either (Left . snd) Right (parseLocatedFile "<program>" src)
  let prog = inferProgram ((buildProgram items) {progSources = sourceMap located})
  case programViolations prog of
    [] -> pure prog
    ((key, g) : _) -> Left ("unsafe-call: " ++ describeViolation prog key g)

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

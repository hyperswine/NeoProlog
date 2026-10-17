{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE FlexibleContexts #-}

-- | The core driver: an explicit continuation, a choice-point stack with
-- trail marks, inline control scopes and heap-native builtins.
--
-- The driver returns to its caller whenever an item must be delivered
-- ('Yield'); the caller resumes the same mutable machine by running the
-- supplied action. Nothing is copied to save or restore a branch: a choice
-- point records heap, trail, output and scope marks, and backtracking
-- unwinds to them.
module Infera.Core.Run
  ( Step (..),
    runCore,
    runCoreWith,
  )
where

import Control.Monad (foldM, forM, forM_, unless, when)
import Data.Array ((!))
import Data.Array.Base (getNumElements, unsafeRead, unsafeWrite)
import Data.Bits ((.|.))
import Data.Array.IO (IOArray, IOUArray, newArray, newArray_)
import Data.IORef
import qualified Data.IntMap.Strict as IM
import qualified Data.IntSet as IS
import Infera.Arith (NumericValue (..), compareNumeric, deepEval, numericDouble, numericTerm)
import qualified Infera.CLP as CLP
import Infera.Core.Compile
import Infera.Core.Store
import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import Infera.Engine.Reference (Env (..), OutputEvent (..), SearchItem (..), SolverState (..), TableEntry (..), initialState, maxResolutionDepth, maxTableIterations, mkEnv)
import qualified Infera.Engine.Reference as Reference
import Infera.Error (PredKey, SolveError (..))
import qualified Infera.Program as P
import qualified Infera.Syntax as S
import Infera.Syntax (Term (..))
import Infera.Unify (canonicalize, deepWalk, emptySubst, instantiate, unifyPlain)
import System.IO (hPutStrLn, stderr)
import System.IO.Unsafe (unsafePerformIO)
import System.Environment (lookupEnv)

import Infera.Error (showPredKey)

traceOn :: Bool
traceOn = unsafePerformIO (maybe False (const True) <$> lookupEnv "INFERA_CORE_TRACE")
{-# NOINLINE traceOn #-}

traceMsg :: String -> IO ()
traceMsg msg = when traceOn (hPutStrLn stderr msg)

data Step
  = Stop
  | Yield SearchItem (IO Step)
  | -- | a construct outside the supported subset was reached at runtime
    Abandon String

-- Continuations. 'CGoals' carries the activation base, the cut barrier
-- (choice height at clause entry) and the activation depth.
data Cont
  = CDone
  | CGoals [Goal] !Int !Int !Int Cont
  | -- | after a contract-bearing call: output check, guard flag, commit height
    CReturn !Int !(Maybe (IORef Bool)) !(Maybe (PredKey, P.Signature, [Word'])) Cont
  | -- | condition succeeded: cut to the sentinel, run the then-goals
    CExitIf !Int [Goal] !Int !Int !Int Cont
  | -- | negated goal succeeded (sentinel, flag, depth)
    CExitNot !Int !(IORef Bool) !Int
  | -- | a findall solution: copy the template and look for more
    -- (sentinel, results, template, base, entry heap, entry output, depth)
    CExitFindAll !Int !(IORef [(Copy, [OutputEvent])]) Pattern !Int !Int !Int !Int
  | -- | a solution of a tabled fixpoint iteration
    CExitTable !(IORef Fix)
  | -- | a candidate of a minimize scope: cost pattern, base, state ref
    CExitMinimize Pattern !Int !(IORef Minimum)

data Choice = Choice
  { chH :: !Int,
    chTR :: !Int,
    chOut :: !Int,
    chScopes :: !Int,
    chFresh :: !Int,
    -- | branch-local tables
    chTables :: Map.Map Term TableEntry,
    -- | branch-local dynamic facts
    chDynamic :: Map.Map PredKey [(Term, Int)],
    -- | branch-local constraint store and watched cells
    chStore :: CLP.Store,
    chWatched :: IS.IntSet,
    chAlt :: !Alt
  }

data Alt
  = -- | remaining candidates, saved argument address, depth, continuation
    AltClauses !Pred [Int] !Int !Int Cont
  | AltGoals [Goal] !Int !Int !Int Cont
  | AltGuard !PredKey !S.Det !(IORef Bool)
  | AltNot !(IORef Bool) !(IORef [SearchItem]) Cont
  | AltIf !(IORef Int) (Maybe ([Goal], Int, Int, Int)) Cont
  | AltFindAll !(IORef [(Copy, [OutputEvent])]) !(IORef [SearchItem]) Pattern !Int !Int Cont
  | -- | remaining reference items of a delegated goal and the substitution
    -- the goal started from
    AltLeaf [SearchItem] !(IM.IntMap Term) Cont
  | -- | sentinel of a tabled fixpoint iteration
    AltTable !(IORef Fix)
  | -- | remaining table answers to consume: answers, saved call address,
    -- arity, continuation
    AltAnswers [(Term, Int, [OutputEvent])] !Int !Int Cont
  | -- | remaining facts a retract may remove: (index, fact, size), key,
    -- saved term cell, continuation
    AltRetract [(Int, Term, Int)] !PredKey !Int Cont
  | -- | sentinel of a minimize scope
    AltMinimize !(IORef Minimum) !(IORef [SearchItem]) Cont

-- | The state of a minimize scope: entry marks and the best candidate so
-- far as the bindings it made to older cells, its output, tables and facts.
data Minimum = Minimum
  { mnEntryHeap :: !Int,
    mnEntryTrail :: !Int,
    mnEntryOut :: !Int,
    mnBest :: Maybe (Integer, [(Int, Copy)], [OutputEvent], Map.Map Term TableEntry, Map.Map PredKey [(Term, Int)], CLP.Store, IS.IntSet)
  }

-- | The state of one tabled call's fixpoint, as in the reference engine.
data Fix = Fix
  { fxKey :: Term,
    fxPred :: !Pred,
    -- | saved call arguments (arity cells)
    fxArgs :: !Int,
    fxEntryOut :: !Int,
    fxDepth :: !Int,
    -- | the running table map of the fixpoint (the reference's @tables'@)
    fxTables :: Map.Map Term TableEntry,
    fxAnswers :: [(Term, Int, [OutputEvent])],
    fxSet :: Set.Set Term,
    fxIteration :: !Int,
    -- | this iteration's extracted answers, newest first
    fxFound :: [(Term, Int, [OutputEvent])],
    -- | completed entries seen in this iteration's solutions
    fxCompleted :: Map.Map Term TableEntry,
    fxIssues :: !(IORef [SearchItem]),
    fxCont :: Cont,
    -- | a solution bound a constrained variable: evaluate plainly instead
    fxUnsafe :: !Bool
  }

-- Issue scopes: a negation or findall buffers issues until its outcome is
-- known; a condition only counts them.
data Scope = SBuffer !(IORef [SearchItem]) | SCount !(IORef Int)

-- A findall solution copied out of the heap. Cells older than the findall
-- entry are kept by reference; younger free variables become fresh.
data Copy = CpRef !Int | CpFresh !Int !Int | CpWord !Word' | CpStruct !Word' [Copy]

data Machine = Machine
  { mStore :: !Store,
    mProgram :: !P.Program,
    mEnv :: !Env,
    mCore :: !CoreProgram,
    mChoices :: !(IORef (IOArray Int Choice)),
    mChoiceTop :: !(IORef Int),
    mScopes :: !(IORef [Scope]),
    mOutput :: !(IORef [OutputEvent]),
    mTables :: !(IORef (Map.Map Term TableEntry)),
    mDynamic :: !(IORef (Map.Map PredKey [(Term, Int)])),
    -- | the persistent constraint store (branch-local)
    mCLP :: !(IORef CLP.Store),
    -- | cells of variables the store may mention, by logical id
    mVarCells :: !(IORef (IM.IntMap Int)),
    -- | addresses of watched variables (branch-local)
    mWatched :: !(IORef IS.IntSet)
  }

-- | Compile and start a query. Left names the construct that puts the
-- program outside the supported subset; Right produces the first step.
runCore :: P.Program -> S.Query -> IO (Maybe String, IO Step)
runCore = runCoreWith initialCollectLimit

-- | Start with an explicit initial collection threshold (cells); tests use
-- a tiny one to collect at nearly every call. The first component names
-- the first construct that would abandon the run, if any.
runCoreWith :: Int -> P.Program -> S.Query -> IO (Maybe String, IO Step)
runCoreWith limit program query = do
  syms <- newSymbols
  store <- newStore syms
  writeReg store rGCLIM limit
  compiled <- compileProgram store program query
  case compiled of
    Left (Unsupported reason) -> pure (Just reason, pure (Abandon reason))
    Right core -> do
      choices <- newArray_ (0, 1023)
      m <- Machine store program (mkEnv program) core <$> newIORef choices <*> newIORef 0 <*> newIORef [] <*> newIORef [] <*> newIORef Map.empty <*> newIORef Map.empty
        <*> newIORef CLP.emptyStore <*> newIORef IM.empty <*> newIORef IS.empty
      _ <- allocCells store (max 1 (cpQueryVars core))
      setFreshId store (cpQueryVars core)
      writeIORef (mVarCells m) (IM.fromList [(i, i) | i <- [0 .. cpQueryVars core - 1]])
      pure (cpUnsupported core, run m (CGoals (cpQuery core) 0 0 0 CDone))

-- ─── choice stack ────────────────────────────────────────────────────────────

pushChoice :: Machine -> Alt -> IO Int
pushChoice m alt = do
  let s = mStore m
  h <- heapTop s
  tr <- trailTop s
  out <- outLen s
  fresh <- freshId s
  tables <- readIORef (mTables m)
  dynamic <- readIORef (mDynamic m)
  store <- readIORef (mCLP m)
  watched <- readIORef (mWatched m)
  scopes <- length <$> readIORef (mScopes m)
  top <- readIORef (mChoiceTop m)
  arr <- readIORef (mChoices m)
  size <- getNumElements arr
  arr' <-
    if top < size
      then pure arr
      else do
        grown <- newArray_ (0, size * 2 - 1)
        forM_ [0 .. top - 1] $ \i -> unsafeRead arr i >>= unsafeWrite grown i
        writeIORef (mChoices m) grown
        pure grown
  unsafeWrite arr' top (Choice h tr out scopes fresh tables dynamic store watched alt)
  writeIORef (mChoiceTop m) (top + 1)
  setHb s h
  pure top

readChoice :: Machine -> Int -> IO Choice
readChoice m i = do
  arr <- readIORef (mChoices m)
  unsafeRead arr i

writeChoice :: Machine -> Int -> Choice -> IO ()
writeChoice m i ch = do
  arr <- readIORef (mChoices m)
  unsafeWrite arr i ch

-- | Remove every choice at or above @h@ and its scopes.
cutTo :: Machine -> Int -> IO ()
cutTo m h = do
  top <- readIORef (mChoiceTop m)
  when (h < top) $ do
    removed <- readChoice m h
    truncateScopes m (chScopes removed)
    writeIORef (mChoiceTop m) h
    refreshHb m

refreshHb :: Machine -> IO ()
refreshHb m = do
  top <- readIORef (mChoiceTop m)
  if top == 0
    then setHb (mStore m) 0
    else do
      ch <- readChoice m (top - 1)
      setHb (mStore m) (chH ch)

truncateScopes :: Machine -> Int -> IO ()
truncateScopes m depth = do
  scopes <- readIORef (mScopes m)
  let extra = length scopes - depth
  when (extra > 0) (writeIORef (mScopes m) (drop extra scopes))

pushScope :: Machine -> Scope -> IO ()
pushScope m scope = modifyIORef' (mScopes m) (scope :)

-- ─── issues ──────────────────────────────────────────────────────────────────

-- | Deliver items in order through the enclosing scopes: a buffering scope
-- absorbs an item, a counting scope records it and lets it pass, and with
-- no scope the item reaches the consumer. Then continue with @k@.
raiseItems :: Machine -> [SearchItem] -> IO Step -> IO Step
raiseItems _ [] k = k
raiseItems m (item : rest) k = do
  scopes <- readIORef (mScopes m)
  absorbed <- deliver scopes
  if absorbed then raiseItems m rest k else pure (Yield item (raiseItems m rest k))
  where
    deliver [] = pure False
    deliver (SCount counter : outer) = do
      when (isError item || isExhausted item) (modifyIORef' counter (+ 1))
      deliver outer
    deliver (SBuffer buffer : _) = modifyIORef' buffer (item :) >> pure True

isError :: SearchItem -> Bool
isError (BranchError _) = True
isError _ = False

isExhausted :: SearchItem -> Bool
isExhausted BranchExhausted = True
isExhausted _ = False

isDependency :: SearchItem -> Bool
isDependency (ConsumedIncomplete _) = True
isDependency _ = False

raiseError :: Machine -> SolveError -> IO Step
raiseError m err = raiseItems m [BranchError err] (backtrack m)

-- ─── output ──────────────────────────────────────────────────────────────────

emitOutput :: Machine -> OutputEvent -> IO ()
emitOutput m event = do
  modifyIORef' (mOutput m) (event :)
  n <- outLen (mStore m)
  setOutLen (mStore m) (n + 1)

truncateOutput :: Machine -> Int -> IO ()
truncateOutput m saved = do
  n <- outLen (mStore m)
  when (n > saved) $ do
    modifyIORef' (mOutput m) (drop (n - saved))
    setOutLen (mStore m) saved

-- ─── the driver ──────────────────────────────────────────────────────────────

run :: Machine -> Cont -> IO Step
run m cont = case cont of
  CGoals goals base barrier depth next -> runGoals m goals base barrier depth next
  _ -> do
    pending <- readReg (mStore m) rBOUND
    if pending > 0 then reconciled m (run' m cont) else run' m cont

run' :: Machine -> Cont -> IO Step
run' m cont = case cont of
  CDone -> do
    state <- exportState m
    pure (Yield (Found state) (backtrack m))
  CGoals goals base barrier depth next -> runGoals m goals base barrier depth next
  CReturn commitHeight guard check next -> do
    problem <- case check of
      Nothing -> pure Nothing
      Just (key, signature, args) -> checkOutputs m key signature args
    case problem of
      Just err -> raiseError m err
      Nothing -> do
        forM_ guard (`writeIORef` True)
        when (commitHeight >= 0) (cutTo m commitHeight)
        run m next
  CExitIf sentinel thenGoals base barrier depth next -> do
    cutTo m sentinel
    run m (CGoals thenGoals base barrier depth next)
  CExitNot sentinel flag _ -> do
    writeIORef flag True
    cutTo m (sentinel + 1)
    backtrack m
  CExitMinimize cost base ref -> do
    let s = mStore m
    mn <- readIORef ref
    costWord <- buildArg m base False cost
    value <- evalWord m costWord
    outcome <- case value of
      Left err -> pure (Left err)
      Right Nothing -> Left . InstantiationError <$> exportFor m costWord
      Right (Just (NVInt n)) -> pure (Right n)
      Right (Just bad) -> pure (Left (ExpectedInteger (numericTerm bad)))
    case outcome of
      Left err -> raiseItems m [BranchError err] (backtrack m)
      Right n -> do
        let better = case mnBest mn of
              Nothing -> True
              Just (current, _, _, _, _, _, _) -> n < current
        when better $ do
          trailArr <- readIORef (trail s)
          top <- trailTop s
          -- Walk the trail downward: an odd entry restores the word below it.
          let scan !i acc
                | i < mnEntryTrail mn = pure acc
                | otherwise = do
                    entry <- unsafeRead trailArr i
                    if odd entry
                      then scan (i - 2) acc
                      else do
                        -- Only cells older than the scope survive it.
                        let addr = entry `div` 2
                        w <- readCell s addr
                        if addr >= mnEntryHeap mn || (tagOf w == tagRef && valOf w == addr)
                          then scan (i - 1) acc
                          else do
                            copy <- copyOut m (mnEntryHeap mn) w
                            scan (i - 1) ((addr, copy) : acc)
          bound <- scan (top - 1) []
          produced <- outputSince m (mnEntryOut mn)
          tables <- readIORef (mTables m)
          dynamic <- readIORef (mDynamic m)
          store <- readIORef (mCLP m)
          watched <- readIORef (mWatched m)
          writeIORef ref mn {mnBest = Just (n, bound, produced, tables, dynamic, store, watched)}
        backtrack m
  CExitTable fixRef -> do
    fx <- readIORef fixRef
    (answer, count) <- canonicalCall m (fst (pKey (fxPred fx))) (fxArgs fx) (pArity (fxPred fx))
    produced <- outputSince m (fxEntryOut fx)
    tables <- readIORef (mTables m)
    store <- readIORef (mCLP m)
    bad <- callConstrained m store (fxArgs fx) (pArity (fxPred fx))
    writeIORef fixRef fx
      { fxFound = (answer, count, produced) : fxFound fx,
        fxCompleted = Map.union (fxCompleted fx) (Map.filter teComplete tables),
        fxUnsafe = fxUnsafe fx || bad
      }
    backtrack m
  CExitFindAll _ results template base entryHeap entryOut _ -> do
    word <- buildArg m base False template
    copy <- copyOut m entryHeap word
    produced <- outputSince m entryOut
    modifyIORef' results ((copy, produced) :)
    backtrack m

contDepth :: Cont -> Int
contDepth cont = case cont of
  CDone -> 0
  CGoals _ _ _ depth _ -> depth
  CReturn _ _ _ next -> contDepth next
  CExitIf _ _ _ _ depth _ -> depth
  CExitNot _ _ depth -> depth
  CExitFindAll _ _ _ _ _ _ depth -> depth
  CExitTable _ -> 0
  CExitMinimize _ _ _ -> 0

-- Skip exhausted goal lists so that a tail call sees its caller's return.
dropEmpty :: Cont -> Cont
dropEmpty (CGoals [] _ _ _ next) = dropEmpty next
dropEmpty cont = cont

-- | Run a goal list. The continuation is materialised only where a call,
-- a choice point or a scope needs a value.
runGoals :: Machine -> [Goal] -> Int -> Int -> Int -> Cont -> IO Step
runGoals m [] _ _ _ next = run m next
runGoals m (goal : goals) base barrier depth next = do
  pending <- readReg (mStore m) rBOUND
  if pending > 0
    then reconciled m (step m goal goals base barrier depth next)
    else step m goal goals base barrier depth next

-- | Feed the bindings recorded since the last goal boundary to the
-- constraint store, install what propagation bound, then continue; a
-- contradiction fails and a type error is raised here.
reconciled :: Machine -> IO Step -> IO Step
reconciled m continue = do
  let s = mStore m
  addrs <- drainBound s
  watched <- readIORef (mWatched m)
  let hits = filter (`IS.member` watched) addrs
  if null hits
    then continue
    else do
      changes <- forM hits $ \addr -> do
        ident <- cellId m addr
        value <- readCell s addr >>= exportFor m
        pure (ident, value)
      store <- readIORef (mCLP m)
      case CLP.applyBindings changes store of
        Left err -> raiseError m err
        Right Nothing -> backtrack m
        Right (Just store') -> do
          ok <- installStore m (CLP.stSubst store) store'
          if ok then continue else backtrack m

-- | The logical id of a variable cell: query cells by position, others
-- through their block marker.
cellId :: Machine -> Int -> IO Int
cellId m addr
  | addr < cpQueryVars (mCore m) = pure addr
  | otherwise = maybe addr id <$> logicalId (mStore m) addr

-- | Adopt a store returned by the reference: bind every variable it newly
-- bound (without recording those writes again) and refresh the watched
-- set. False when a propagated binding contradicts the heap.
installStore :: Machine -> IM.IntMap Term -> CLP.Store -> IO Bool
installStore m previous store = do
  let s = mStore m
      added = IM.toList (IM.difference (CLP.stSubst store) previous)
  writeIORef (mCLP m) store
  writeReg s rCLP 1
  flag <- readReg s rBOUND
  ok <- installBindings added
  writeReg s rBOUND flag
  cells' <- readIORef (mVarCells m)
  writeIORef (mWatched m) (IS.fromList [addr | v <- IS.toList (CLP.stWatched store), Just addr <- [IM.lookup v cells']])
  pure ok
  where
    s = mStore m
    installBindings [] = pure True
    installBindings ((v, term) : rest) = do
      cells' <- readIORef (mVarCells m)
      case IM.lookup v cells' of
        Nothing -> installBindings rest
        Just addr -> do
          table <- newIORef (IM.map refWord cells')
          w <- importKnown table term
          cell <- readCell s addr
          ok <- unify s cell w
          when traceOn $ do
            shown <- exportFor m cell
            traceMsg ("  install " ++ show v ++ "@" ++ show addr ++ " := " ++ show term ++ " (cell held " ++ show shown ++ ") -> " ++ show ok)
          -- Fresh variables the reference introduced keep their ids.
          final <- readIORef table
          forM_ (IM.toList final) $ \(ident, word) ->
            when (tagOf word == tagRef && not (IM.member ident cells')) $
              modifyIORef' (mVarCells m) (IM.insert ident (valOf word))
          if ok then installBindings rest else pure False
    importKnown table term = case term of
      Var v -> do
        known <- readIORef table
        case IM.lookup v known of
          Just w -> pure w
          Nothing -> do
            addr <- allocSlots s v 1
            modifyIORef' table (IM.insert v (refWord addr))
            pure (refWord addr)
      Compound f as -> do
        fid <- internFunctor (symbols s) f (length as)
        words' <- mapM (importKnown table) as
        structureWord s (funWord fid (length as)) words'
      _ -> importTermWords s table term

step :: Machine -> Goal -> [Goal] -> Int -> Int -> Int -> Cont -> IO Step
step = step'

goalName :: Goal -> String
goalName g = case g of
  GCall _ _ -> "call"; GTabled _ _ -> "tabled"; GCallFacts k _ -> "facts " ++ show k; GAssert _ -> "assert"
  GRetract _ -> "retract"; GRetractAll _ -> "retractall"; GMinimize _ _ -> "minimize"; GCallDyn _ _ _ -> "calldyn"
  GAnd _ -> "and"; GUnify _ _ -> "unify"; GEquiv _ _ -> "equiv"; GNeq _ _ -> "neq"; GIs _ _ -> "is"; GCmp _ _ _ -> "cmp"
  GTrue -> "true"; GFail -> "fail"; GCut -> "cut"; GOr _ _ -> "or"; GIf _ _ _ -> "if"; GNot _ -> "not"; GOnce _ -> "once"
  GFindAll _ _ _ -> "findall"; GCheck _ _ -> "check"; GWrite _ _ -> "write"; GNl -> "nl"; GError _ -> "error"
  GLeaf n _ -> "leaf " ++ n; GPhrase _ _ -> "phrase"; GPhraseFile _ _ -> "phrasefile"; GEmit _ -> "emit"; GEmitText _ -> "emittext"
  GUnsupported _ -> "unsupported"

step' :: Machine -> Goal -> [Goal] -> Int -> Int -> Int -> Cont -> IO Step
step' m goal goals base barrier depth next = case goal of
  GTrue -> continue
  GFail -> backtrack m
  GCut -> cutTo m barrier >> continue
  GAnd inner -> runGoals m (inner ++ goals) base barrier depth next
  GCall ref patterns -> do
    predicate <- readIORef ref
    buildArgs m base patterns 0
    pending <- arithData (mStore m)
    when (pending > 0) (normalizeArgs m (pArity predicate))
    callPredicate m predicate (if null goals then next else CGoals goals base barrier depth next)
  GTabled ref patterns -> do
    predicate <- readIORef ref
    buildArgs m base patterns 0
    pending <- arithData (mStore m)
    when (pending > 0) (normalizeArgs m (pArity predicate))
    callTabled m predicate (if null goals then next else CGoals goals base barrier depth next)
  GCallFacts key patterns -> do
    let s = mStore m
        arity = length patterns
    buildArgs m base patterns 0
    pending <- arithData s
    when (pending > 0) (normalizeArgs m arity)
    saved <- saveArgs s arity
    facts <- Map.findWithDefault [] key <$> readIORef (mDynamic m)
    consumeAnswers m [(fact, n, []) | (fact, n) <- facts] saved arity (CGoals goals base barrier depth next)
  GMinimize cost inner -> do
    let s = mStore m
    entryHeap <- heapTop s
    entryTrail <- trailTop s
    entryOut <- outLen s
    ref <- newIORef (Minimum entryHeap entryTrail entryOut Nothing)
    buffer <- newIORef []
    let rest = CGoals goals base barrier depth next
    sentinel <- pushChoice m (AltMinimize ref buffer rest)
    pushScope m (SBuffer buffer)
    runGoals m inner base (sentinel + 1) depth (CExitMinimize cost base ref)
  GAssert pattern -> do
    word <- buildArg m base False pattern
    fact <- exportFor m word
    case S.functorOf fact of
      Nothing -> raiseError m (TypeError "callable fact" fact)
      Just key@(name, _)
        | not (P.nameHasFlag (mProgram m) name S.FlagDynamic) ->
            raiseError m (UserError (showPredKey key ++ " is not declared dynamic (add `" ++ name ++ " : dynamic.`)"))
        | otherwise -> do
            let (canon, vs) = canonicalize emptySubst fact
            modifyIORef' (mDynamic m) (Map.insertWith (flip (++)) key [(canon, length vs)])
            continue
  GRetract pattern -> do
    let s = mStore m
    word <- buildArg m base False pattern
    shown <- exportFor m word
    case S.functorOf shown of
      Nothing -> raiseError m (TypeError "callable fact" shown)
      Just key -> do
        facts <- Map.findWithDefault [] key <$> readIORef (mDynamic m)
        saved <- reserveCells s 1
        writeCell s saved word
        retractFacts m [(i, fact, n) | (i, (fact, n)) <- zip [0 ..] facts] key saved (CGoals goals base barrier depth next)
  GRetractAll pattern -> do
    word <- buildArg m base False pattern
    shown <- exportFor m word
    case S.functorOf shown of
      Nothing -> raiseError m (TypeError "callable fact" shown)
      Just key -> do
        fresh <- freshId (mStore m)
        facts <- Map.findWithDefault [] key <$> readIORef (mDynamic m)
        let keep = [(canon, n) | (canon, n) <- facts, Nothing <- [unifyPlain emptySubst shown (instantiate fresh canon)]]
        modifyIORef' (mDynamic m) (Map.insert key keep)
        continue
  GCallDyn direct callable extra -> do
    word <- buildArg m base False callable
    aliases <- newIORef IM.empty
    extraTerms <- mapM (\p -> buildArg m base False p >>= exportGoal m aliases) extra
    goalTerm <- exportGoal m aliases word
    let goalWith = case goalTerm of
          Atom f | null extraTerms -> Atom f
          Atom f -> Compound f extraTerms
          Compound f as -> Compound f (as ++ extraTerms)
          other -> other
    case goalWith of
      Var _ | direct -> exportFor m word >>= raiseError m . InstantiationError
      _ | not (S.isCallable goalWith) -> do
            shown <- exportFor m word
            raiseError m (TypeError "callable" shown)
        | otherwise -> do
            runDynamic m aliases [goalWith] [] depth (CGoals goals base barrier depth next)
  GPhrase nt l -> do
    ntWord <- buildArg m base False nt
    lWord <- buildArg m base False l >>= deref (mStore m)
    input <- if tagOf lWord == tagBox
      then do
        value <- boxed (mStore m) lWord
        case value of
          BStr str -> charListWord m str
          _ -> pure lWord
      else pure lWord
    aliases <- newIORef IM.empty
    goal <- phraseTerm m aliases ntWord input
    runDynamic m aliases [goal] [] depth (CGoals goals base barrier depth next)
  GPhraseFile nt path -> do
    ntWord <- buildArg m base False nt
    pathWord <- buildArg m base False path >>= deref (mStore m)
    located <- fileContents m pathWord
    case located of
      Left err -> raiseError m err
      Right contents -> do
        input <- charListWord m contents
        aliases <- newIORef IM.empty
        goal <- phraseTerm m aliases ntWord input
        runDynamic m aliases [goal] [] depth (CGoals goals base barrier depth next)
  GEmit nt -> do
    let s = mStore m
    ntWord <- buildArg m base False nt
    fresh <- freshId s
    chars <- allocSlots s fresh 1
    setFreshId s (fresh + 1)
    aliases <- newIORef IM.empty
    goal <- phraseTerm m aliases ntWord (refWord chars)
    table <- readIORef aliases
    let csId = head [v | (v, w) <- IM.toList table, w == refWord chars]
    phraseGoal <- compileGoalTerm s (mProgram m) (cpPreds (mCore m)) goal
    runDynamic m aliases [] [GIf [phraseGoal] [GEmitText (PSlot csId)] Nothing] depth (CGoals goals base barrier depth next)
  GEmitText pattern -> do
    word <- buildArg m base False pattern
    text <- charListOf m word
    case text of
      Just str -> emitOutput m (WriteEvent str) >> continue
      Nothing -> do
        shown <- exportFor m word
        raiseError m (TypeError "character list from the DCG" shown)
  GLeaf name patterns -> do
    args <- mapM (\p -> buildArg m base False p >>= exportFor m) patterns
    delegate m (Compound name args) (CGoals goals base barrier depth next)
  GUnify a b -> do
    wa <- buildArg m base False a
    wb <- buildArg m base False b
    ok <- unify (mStore m) wa wb
    if ok then continue else backtrack m
  GEquiv a b -> do
    wa <- buildArg m base False a
    wb <- buildArg m base False b
    ok <- equiv (mStore m) wa wb
    if ok then continue else backtrack m
  GNeq a b -> do
    wa <- buildArg m base False a
    wb <- buildArg m base False b
    ga <- isGroundWord (mStore m) wa
    gb <- isGroundWord (mStore m) wb
    if ga && gb
      then do
        same <- equiv (mStore m) wa wb
        if same then backtrack m else continue
      else do
        ta <- exportFor m wa
        tb <- exportFor m wb
        delegate m (Compound "neq" [ta, tb]) (CGoals goals base barrier depth next)
  GIs target expr -> do
    fast <- evalFast m base expr
    if fast
      then do
        quick <- readReg (mStore m) rVAL
        wt <- buildArg m base False target
        ok <- unify (mStore m) wt (intWord quick)
        if ok then continue else backtrack m
      else do
        value <- evalExpr m base expr
        case value of
          Left err -> raiseError m err
          Right Nothing -> do
            shown <- exprTerm m base expr
            raiseError m (InstantiationError shown)
          Right (Just number) -> do
            wt <- buildArg m base False target
            wv <- numberWord (mStore m) number
            ok <- unify (mStore m) wt wv
            if ok then continue else backtrack m
  GCmp op a b -> do
    fa <- evalFast m base a
    qa <- readReg (mStore m) rVAL
    fb <- if fa then evalFast m base b else pure False
    qb <- readReg (mStore m) rVAL
    if fb
      then if cmpAccepts op (compare qa qb) then continue else backtrack m
      else do
        outcome <- compareGoal m base a b
        case outcome of
          Left err -> raiseError m err
          Right ordering -> if cmpAccepts op ordering then continue else backtrack m
  GOr left right -> do
    let rest = CGoals goals base barrier depth next
    _ <- pushChoice m (AltGoals right base barrier depth rest)
    runGoals m left base barrier depth rest
  GIf condition thenGoals elseGoals -> do
    counter <- newIORef 0
    let rest = CGoals goals base barrier depth next
    sentinel <- pushChoice m (AltIf counter (fmap (\gs -> (gs, base, barrier, depth)) elseGoals) rest)
    pushScope m (SCount counter)
    runGoals m condition base (sentinel + 1) depth (CExitIf sentinel thenGoals base barrier depth rest)
  GOnce inner -> step m (GIf inner [] Nothing) goals base barrier depth next
  GNot inner -> do
    flag <- newIORef False
    buffer <- newIORef []
    let rest = CGoals goals base barrier depth next
    sentinel <- pushChoice m (AltNot flag buffer rest)
    pushScope m (SBuffer buffer)
    runGoals m inner base (sentinel + 1) depth (CExitNot sentinel flag depth)
  GFindAll template inner target -> do
    results <- newIORef []
    buffer <- newIORef []
    entryHeap <- heapTop (mStore m)
    entryOut <- outLen (mStore m)
    let rest = CGoals goals base barrier depth next
    sentinel <- pushChoice m (AltFindAll results buffer target base depth rest)
    pushScope m (SBuffer buffer)
    runGoals m inner base (sentinel + 1) depth (CExitFindAll sentinel results template base entryHeap entryOut depth)
  GCheck check pattern -> do
    word <- buildArg m base False pattern
    ok <- typeCheck m check word
    if ok then continue else backtrack m
  GWrite newline pattern -> do
    word <- buildArg m base False pattern
    term <- exportFor m word
    emitOutput m (WriteEvent (showValue (deepEval emptySubst term)))
    when newline (emitOutput m NewlineEvent)
    continue
  GNl -> emitOutput m NewlineEvent >> continue
  GError err -> raiseError m err
  GUnsupported term -> pure (Abandon ("unsupported goal " ++ show term))
  where
    continue = runGoals m goals base barrier depth next

-- | Run goal terms whose variables are the alias table's words, in a fresh
-- activation block aliasing those words; extra compiled goals run after
-- them in the same block. Cuts stay local.
runDynamic :: Machine -> IORef (IM.IntMap Word') -> [Term] -> [Goal] -> Int -> Cont -> IO Step
runDynamic m aliases terms extra depth cont = do
  compiled <- mapM (compileGoalTerm (mStore m) (mProgram m) (cpPreds (mCore m))) terms
  table <- readIORef aliases
  let s = mStore m
  fresh <- freshId s
  block <- allocSlots s fresh (max 1 (IM.size table))
  forM_ (IM.toList table) $ \(v, w) -> writeCell s (block + v) w
  height <- readIORef (mChoiceTop m)
  runGoals m (compiled ++ extra) block height depth cont

-- | The goal that runs a DCG non-terminal between an input and @nil@.
phraseTerm :: Machine -> IORef (IM.IntMap Word') -> Word' -> Word' -> IO Term
phraseTerm m aliases ntWord input = do
  nt <- exportGoal m aliases ntWord
  table <- readIORef aliases
  let inputId = IM.size table
  writeIORef aliases (IM.insert inputId input table)
  let s0 = Var inputId
      end = Atom "nil"
  pure $ case nt of
    Atom f -> Compound f [s0, end]
    Compound f as -> Compound f (as ++ [s0, end])
    other -> Compound "call" [other, s0, end]

charListWord :: Machine -> String -> IO Word'
charListWord m str =
  foldM (\tl c -> structure (mStore m) (cpCons (mCore m)) [chrWord (fromEnum c), tl]) (cpNil (mCore m)) (reverse str)

charListOf :: Machine -> Word' -> IO (Maybe String)
charListOf m w0 = do
  w <- deref s w0
  if w == cpNil (mCore m)
    then pure (Just [])
    else
      if tagOf w /= tagStr
        then pure Nothing
        else do
          f <- readCell s (valOf w)
          if funKey f /= cpCons (mCore m)
            then pure Nothing
            else do
              hd <- readCell s (valOf w + 1) >>= deref s
              if tagOf hd /= tagChr
                then pure Nothing
                else do
                  rest <- readCell s (valOf w + 2) >>= charListOf m
                  pure (fmap (toEnum (valOf hd) :) rest)
  where
    s = mStore m

fileContents :: Machine -> Word' -> IO (Either SolveError String)
fileContents m pathWord
  | tagOf pathWord == tagBox = do
      value <- boxed (mStore m) pathWord
      case value of
        BStr path -> pure $ case Map.lookup path (envFiles (mEnv m)) of
          Just contents -> Right contents
          Nothing -> Left (UserError ("read_file: \"" ++ path ++ "\" was not loaded (paths must be string literals in the program or query)"))
        _ -> Left . TypeError "file path string" <$> exportFor m pathWord
  | otherwise = Left . TypeError "file path string" <$> exportFor m pathWord

-- | Run a goal on the reference engine with the current store and adopt
-- each solution's store and bindings; later solutions wait in a choice
-- point. Variables are exported with their logical ids, so store state
-- stays consistent across goals.
delegate :: Machine -> Term -> Cont -> IO Step
delegate m goal cont = do
  let s = mStore m
  store <- readIORef (mCLP m)
  fresh <- freshId s
  let state = (initialState fresh) {ssStore = store}
      items = Reference.solveGoal (mEnv m) maxResolutionDepth state goal
  when traceOn $ do
    cells' <- readIORef (mVarCells m)
    traceMsg ("delegate " ++ show goal ++ " fresh=" ++ show fresh ++ " cells=" ++ show [(v, a) | v <- S.termVarIds goal, Just a <- [IM.lookup v cells']])
  leafItems m items (CLP.stSubst store) cont

leafItems :: Machine -> [SearchItem] -> IM.IntMap Term -> Cont -> IO Step
leafItems m items previous cont = case items of
  [] -> backtrack m
  (item : rest) -> do
    unless (null rest) $ () <$ pushChoice m (AltLeaf rest previous cont)
    case item of
      Found state -> do
        let s = mStore m
        current <- freshId s
        setFreshId s (max current (ssFresh state))
        ok <- installStore m previous (ssStore state)
        if ok then run m cont else backtrack m
      BranchError err -> raiseItems m [BranchError err] (backtrack m)
      BranchExhausted -> raiseItems m [BranchExhausted] (backtrack m)
      _ -> backtrack m

-- ─── calls ───────────────────────────────────────────────────────────────────

-- | Call with the arguments in the registers.
callPredicate :: Machine -> Pred -> Cont -> IO Step
callPredicate m predicate cont0 = do
  let s = mStore m
      key = pKey predicate
      n = pArity predicate
  top <- heapTop s
  limit <- readReg s rGCLIM
  cont <- if top > limit then collect m cont0 n else pure cont0
  selected <- selectSignature m predicate
  case selected of
    Left err -> raiseError m err
    Right signature -> do
      commits <- commitsAfterSuccess m predicate signature
      let required = case signature of
            Just sig | P.sigDet sig == S.Det -> Just S.Det
            Just sig | P.sigDet sig == S.Multi -> Just S.Multi
            _ -> Nothing
      checked <- case signature of
        Just sig -> do
          args <- mapM (readArg s) [0 .. n - 1]
          pure (Just (key, sig, args))
        Nothing -> pure Nothing
      let depth = contDepth cont + 1
      if depth > maxResolutionDepth
        then raiseItems m [BranchExhausted] (backtrack m)
        else do
          entry <- readIORef (mChoiceTop m)
          guard <- case required of
            Nothing -> pure Nothing
            Just det -> do
              flag <- newIORef False
              _ <- pushChoice m (AltGuard key det flag)
              pure (Just flag)
          let returnCont = case (commits, guard, checked, cont) of
                (False, Nothing, Nothing, _) -> cont
                (True, Nothing, Nothing, CReturn _ Nothing Nothing _) -> cont
                _ -> CReturn (if commits then entry else -1) guard checked cont
          barrier <- readIORef (mChoiceTop m)
          callClauses m predicate barrier depth returnCont

-- | Select and try the clauses of a predicate against the registers.
callClauses :: Machine -> Pred -> Int -> Int -> Cont -> IO Step
callClauses m predicate barrier depth returnCont = do
  let s = mStore m
  candidates <- candidateClauses s predicate
  case candidates of
    [] -> backtrack m
    [ordinal] -> tryClause m predicate ordinal barrier depth returnCont
    (ordinal : more) -> do
      saved <- saveArgs s (pArity predicate)
      choice <- pushChoice m (AltClauses predicate more saved depth returnCont)
      tryClause m predicate ordinal (min barrier choice) depth returnCont

-- | Try one clause against the argument registers.
tryClause :: Machine -> Pred -> Int -> Int -> Int -> Cont -> IO Step
tryClause m predicate ordinal barrier depth cont = do
  let clause = pClauses predicate ! ordinal
      s = mStore m
  fresh <- freshId s
  setFreshId s (fresh + clVars clause)
  base <- allocSlots s fresh (clVars clause)
  ok <- matchHead m base (clHead clause) 0
  if ok
    then runGoals m (clBody clause) base barrier depth cont
    else backtrack m

matchHead :: Machine -> Int -> [Pattern] -> Int -> IO Bool
matchHead _ _ [] _ = pure True
matchHead m base (pattern : patterns) !i = do
  arg <- readArg (mStore m) i
  ok <- unifyPattern m base pattern arg
  if ok then matchHead m base patterns (i + 1) else pure False

-- | Build call arguments into the registers.
buildArgs :: Machine -> Int -> [Pattern] -> Int -> IO ()
buildArgs _ _ [] _ = pure ()
buildArgs m base (pattern : patterns) !i = do
  case pattern of
    PSlot k -> writeArg (mStore m) i (refWord (base + k))
    PWord w -> writeArg (mStore m) i w
    _ -> buildArg m base True pattern >>= writeArg (mStore m) i
  buildArgs m base patterns (i + 1)

normalizeArgs :: Machine -> Int -> IO ()
normalizeArgs m n = forM_ [0 .. n - 1] $ \i -> do
  w <- readArg (mStore m) i
  normalizeWord m w >>= writeArg (mStore m) i

-- | Match a head pattern against a word, building only where the word is
-- an unbound variable.
unifyPattern :: Machine -> Int -> Pattern -> Word' -> IO Bool
unifyPattern m base pattern word = case pattern of
  PSlot i -> unify s (refWord (base + i)) word
  -- An unreferenced fresh cell: no dereference, trail, occurs check or
  -- store record is needed. A self-reference stays a variable.
  PFirst i -> do
    d <- deref s word
    if tagOf d == tagRef && valOf d == base + i then pure True else writeCell s (base + i) d >> pure True
  PWord w -> unify s w word
  PStruct functor children -> do
    d <- deref s word
    case tagOf d of
      t | t == tagRef -> do
            built <- buildArg m base False pattern
            cyclic <- occursIn s (valOf d) built
            if cyclic then pure False else bind s (valOf d) built >> pure True
        | t == tagStr -> do
            f <- readCell s (valOf d)
            if funKey f /= functor then pure False else matchChildren (valOf d + 1) children
        | otherwise -> pure False
  PArith {} -> do
    built <- buildArg m base False pattern
    unify s built word
  where
    s = mStore m
    matchChildren _ [] = pure True
    matchChildren !i (child : rest) = do
      w <- readCell s i
      ok <- unifyPattern m base child w
      if ok then matchChildren (i + 1) rest else pure False

-- | Build a goal argument. With @normalize@, arithmetic structures whose
-- operands are ground numbers are evaluated, as the reference does for
-- user predicate calls.
buildArg :: Machine -> Int -> Bool -> Pattern -> IO Word'
buildArg m base normalize pattern = case pattern of
  PSlot i -> pure (refWord (base + i))
  PFirst i -> pure (refWord (base + i))
  PWord w -> pure w
  PStruct functor children -> do
    let n = funArity functor
    addr <- reserveCells s (n + 1)
    writeCell s addr functor
    ground <- fill (addr + 1) children
    when ground (writeCell s addr (functor .|. groundBit))
    pure (strWord addr)
  PArith functor op children -> do
    words' <- mapM (buildArg m base normalize) children
    evaluated <-
      if normalize
        then do
          operands <- mapM (evalWord m) words'
          pure $ case applyOp op operands of
            Right (Just value) -> Just value
            _ -> Nothing
        else pure Nothing
    case evaluated of
      Just value -> numberWord s value
      Nothing -> do
        bumpArithData s
        structure s functor words'
  where
    s = mStore m
    fill _ [] = pure True
    fill !i (child : rest) = do
      w <- case child of
        PSlot k -> pure (refWord (base + k))
        PFirst k -> pure (refWord (base + k))
        PWord cw -> pure cw
        _ -> buildArg m base normalize child
      writeCell s i w
      g <- groundNowWord s w
      ok <- fill (i + 1) rest
      pure (g && ok)

structure :: Store -> Word' -> [Word'] -> IO Word'
structure = structureWord

-- | Evaluate arithmetic data inside call arguments once such data exists.
normalizeWord :: Machine -> Word' -> IO Word'
normalizeWord m w0 = do
  w <- deref s w0
  if tagOf w /= tagStr
    then pure w
    else do
      f <- readCell s (valOf w)
      let n = funArity f
      children <- forM [1 .. n] $ \i -> readCell s (valOf w + i) >>= deref s
      normalized <- mapM (normalizeWord m) children
      case IM.lookup (funKey f) (cpArith (mCore m)) of
        Just op -> do
          operands <- mapM (evalWord m) normalized
          case applyOp op operands of
            Right (Just value) -> numberWord s value
            _ -> rebuild f children normalized w
        Nothing -> rebuild f children normalized w
  where
    s = mStore m
    rebuild f children normalized w
      | and (zipWith (==) children normalized) = pure w
      | otherwise = structure s (funKey f) normalized

-- ─── backtracking ────────────────────────────────────────────────────────────

backtrack :: Machine -> IO Step
backtrack m = do
  top <- readIORef (mChoiceTop m)
  traceMsg ("backtrack B=" ++ show top)
  if top == 0
    then pure Stop
    else do
      let index = top - 1
      choice <- readChoice m index
      let s = mStore m
      unwindTrail s (chTR choice)
      setHeapTop s (chH choice)
      truncateOutput m (chOut choice)
      truncateScopes m (chScopes choice)
      setFreshId s (chFresh choice)
      writeIORef (mTables m) (chTables choice)
      writeIORef (mDynamic m) (chDynamic choice)
      writeIORef (mCLP m) (chStore choice)
      writeIORef (mWatched m) (chWatched choice)
      writeReg s rBOUND 0
      case chAlt choice of
        AltClauses predicate (ordinal : more) saved depth cont -> do
          loadArgs s saved (pArity predicate)
          if null more
            then writeIORef (mChoiceTop m) index >> refreshHb m
            else writeChoice m index choice {chAlt = AltClauses predicate more saved depth cont}
          tryClause m predicate ordinal index depth cont
        AltClauses _ [] _ _ _ -> pop >> backtrack m
        AltGoals goals base barrier depth cont -> do
          pop
          run m (CGoals goals base barrier depth cont)
        AltGuard key det flag -> do
          pop
          seen <- readIORef flag
          if seen then backtrack m else raiseError m (DetError key det 0)
        AltNot flag buffer cont -> do
          pop
          succeeded <- readIORef flag
          issues <- reverse <$> readIORef buffer
          if succeeded
            then raiseItems m (filter isDependency issues) (backtrack m)
            else
              if any isError issues || any isExhausted issues
                then raiseItems m issues (backtrack m)
                else run m cont
        AltIf counter elseGoals cont -> do
          pop
          issues <- readIORef counter
          case elseGoals of
            Just (goals, base, barrier, depth) | issues == 0 -> run m (CGoals goals base barrier depth cont)
            _ -> backtrack m
        AltLeaf items previous cont -> do
          pop
          leafItems m items previous cont
        AltFindAll results buffer target base _ cont -> do
          pop
          issues <- reverse <$> readIORef buffer
          collected <- reverse <$> readIORef results
          case [e | e@(BranchError _) <- issues] of
            (e : _) -> raiseItems m (filter isDependency issues ++ [e]) (backtrack m)
            [] -> raiseItems m issues $ do
              forM_ collected $ \(_, produced) -> mapM_ (emitOutput m) produced
              list <- rebuildList m (map fst collected)
              wt <- buildArg m base False target
              ok <- unify s wt list
              if ok then run m cont else backtrack m
        AltTable fixRef -> do
          pop
          finishIteration m fixRef
        AltAnswers answers saved arity cont -> do
          pop
          consumeAnswers m answers saved arity cont
        AltRetract facts key saved cont -> do
          pop
          retractFacts m facts key saved cont
        AltMinimize ref buffer cont -> do
          pop
          issues <- reverse <$> readIORef buffer
          mn <- readIORef ref
          if not (null issues)
            then raiseItems m issues (backtrack m)
            else case mnBest mn of
              Nothing -> backtrack m
              Just (_, bound, produced, tables, dynamic, store, watched) -> do
                fresh <- newIORef IM.empty
                forM_ bound $ \(addr, copy) -> do
                  w <- rebuildCopyWith m fresh copy
                  bind s addr w
                mapM_ (emitOutput m) produced
                writeIORef (mTables m) tables
                writeIORef (mDynamic m) dynamic
                writeIORef (mCLP m) store
                writeIORef (mWatched m) watched
                -- The winner's store already holds these bindings.
                writeReg s rBOUND 0
                run m cont
  where
    pop = do
      top <- readIORef (mChoiceTop m)
      writeIORef (mChoiceTop m) (top - 1)
      refreshHb m

-- ─── findall copies ──────────────────────────────────────────────────────────

copyOut :: Machine -> Int -> Word' -> IO Copy
copyOut m entryHeap word = do
  fresh <- newIORef IM.empty
  let go w0 = do
        w <- deref s w0
        case tagOf w of
          t | t == tagRef ->
                if valOf w < entryHeap
                  then pure (CpRef (valOf w))
                  else do
                    table <- readIORef fresh
                    logical <- maybe (valOf w) id <$> logicalId s (valOf w)
                    case IM.lookup (valOf w) table of
                      Just k -> pure (CpFresh k logical)
                      Nothing -> do
                        let k = IM.size table
                        writeIORef fresh (IM.insert (valOf w) k table)
                        pure (CpFresh k logical)
            | t == tagStr -> do
                f <- readCell s (valOf w)
                children <- forM [1 .. funArity f] $ \i -> readCell s (valOf w + i) >>= go
                pure (CpStruct (funKey f) children)
            | otherwise -> pure (CpWord w)
  go word
  where
    s = mStore m

rebuildList :: Machine -> [Copy] -> IO Word'
rebuildList m copies = do
  items <- forM copies $ \copy -> do
    fresh <- newIORef IM.empty
    rebuildCopyWith m fresh copy
  foldM (\tl hd -> structure s (cpCons (mCore m)) [hd, tl]) (cpNil (mCore m)) (reverse items)
  where
    s = mStore m

-- | Rebuild a copy on the heap; fresh variables share the supplied table.
rebuildCopyWith :: Machine -> IORef (IM.IntMap Int) -> Copy -> IO Word'
rebuildCopyWith m fresh copy = case copy of
  CpRef addr -> pure (refWord addr)
  CpWord w -> pure w
  CpFresh k logical -> do
    table <- readIORef fresh
    case IM.lookup k table of
      Just addr -> pure (refWord addr)
      Nothing -> do
        addr <- allocSlots s logical 1
        writeIORef fresh (IM.insert k addr table)
        pure (refWord addr)
  CpStruct f children -> mapM (rebuildCopyWith m fresh) children >>= structure s f
  where
    s = mStore m

outputSince :: Machine -> Int -> IO [OutputEvent]
outputSince m entryOut = do
  n <- outLen (mStore m)
  events <- readIORef (mOutput m)
  pure (reverse (take (n - entryOut) events))

-- ─── arithmetic ──────────────────────────────────────────────────────────────

-- | Evaluate an expression when every operand is an immediate integer and
-- every intermediate result fits, leaving the value in the scratch
-- register and returning True; otherwise False, and the general evaluator
-- decides the outcome (including errors). Results stay unboxed.
evalFast :: Machine -> Int -> Expr -> IO Bool
evalFast m base expr = case expr of
  EImm i -> yield i
  EPat (PSlot i) -> immediate (refWord (base + i))
  EPat (PFirst i) -> immediate (refWord (base + i))
  EPat (PWord w) -> immediate w
  EOp op [a, b] -> do
    okA <- evalFast m base a
    if not okA
      then pure False
      else do
        x <- readReg s rVAL
        okB <- evalFast m base b
        if not okB
          then pure False
          else do
            y <- readReg s rVAL
            case op of
              OpPlus -> fits (x + y)
              OpMinus -> fits (x - y)
              OpMul
                | abs x < 2 ^ (30 :: Int) && abs y < 2 ^ (30 :: Int) -> yield (x * y)
                | otherwise -> pure False
              OpDiv -> if y == 0 then pure False else fits (x `div` y)
              OpMod -> if y == 0 then pure False else yield (x `mod` y)
              OpMin -> yield (min x y)
              OpMax -> yield (max x y)
              _ -> pure False
  EOp op [a] -> do
    okA <- evalFast m base a
    if not okA
      then pure False
      else do
        x <- readReg s rVAL
        case op of
          OpNeg -> fits (negate x)
          OpAbs -> fits (abs x)
          _ -> pure False
  _ -> pure False
  where
    s = mStore m
    yield v = writeReg s rVAL v >> pure True
    immediate w0 = do
      w <- deref s w0
      if tagOf w == tagInt then yield (valOf w) else pure False
    fits r = if r >= -(2 ^ (60 :: Int)) && r < 2 ^ (60 :: Int) then yield r else pure False

evalExpr :: Machine -> Int -> Expr -> IO (Either SolveError (Maybe NumericValue))
evalExpr m base expr = case expr of
  EImm i -> pure (Right (Just (NVInt (toInteger i))))
  EBig n -> pure (Right (Just (NVInt n)))
  EFlt d -> pure (Right (Just (NVFloat d)))
  EPat pattern -> buildArg m base False pattern >>= evalWord m
  EOp op operands -> applyOp op <$> mapM (evalExpr m base) operands

-- | Evaluate a heap word as a number: immediate, boxed, or arithmetic data.
evalWord :: Machine -> Word' -> IO (Either SolveError (Maybe NumericValue))
evalWord m w0 = do
  w <- deref s w0
  case tagOf w of
    t | t == tagRef -> pure (Right Nothing)
      | t == tagInt -> pure (Right (Just (NVInt (toInteger (valOf w)))))
      | t == tagBox -> do
          value <- boxed s w
          case value of
            BInt n -> pure (Right (Just (NVInt n)))
            BFlt d -> pure (Right (Just (NVFloat d)))
            BStr _ -> Left . ExpectedNumber <$> exportFor m w
      | t == tagStr -> do
          f <- readCell s (valOf w)
          case IM.lookup (funKey f) (cpArith (mCore m)) of
            Just op -> do
              children <- forM [1 .. funArity f] $ \i -> readCell s (valOf w + i)
              applyOp op <$> mapM (evalWord m) children
            Nothing -> Left . ExpectedNumber <$> exportFor m w
      | otherwise -> Left . ExpectedNumber <$> exportFor m w
  where
    s = mStore m

-- | The reference evaluator's operator semantics over already evaluated
-- operands, including its error precedence.
applyOp :: ArithOp -> [Either SolveError (Maybe NumericValue)] -> Either SolveError (Maybe NumericValue)
applyOp op operands = do
  values <- sequence operands
  case (op, values) of
    (OpPlus, [a, b]) -> binary (+) (+) a b
    (OpMinus, [a, b]) -> binary (-) (-) a b
    (OpMul, [a, b]) -> binary (*) (*) a b
    (OpMin, [a, b]) -> binary min min a b
    (OpMax, [a, b]) -> binary max max a b
    (OpNeg, [a]) -> Right (fmap neg a)
    (OpAbs, [a]) -> Right (fmap absN a)
    (OpDiv, [a, b]) -> case (a, b) of
      (_, Just (NVInt 0)) -> Left DivisionByZero
      (_, Just (NVFloat 0)) -> Left DivisionByZero
      (Just (NVInt x), Just (NVInt y)) -> Right (Just (NVInt (x `div` y)))
      (Just x, Just y) -> Right (Just (NVFloat (numericDouble x / numericDouble y)))
      _ -> Right Nothing
    (OpMod, [a, b]) -> case (a, b) of
      (_, Just (NVInt 0)) -> Left DivisionByZero
      (Just (NVInt x), Just (NVInt y)) -> Right (Just (NVInt (x `mod` y)))
      (Just _, Just bad) -> Left (ExpectedInteger (numericTerm bad))
      _ -> Right Nothing
    (OpPow, [a, b]) -> case (a, b) of
      (_, Just (NVInt e)) | e < 0 -> Left (NegativeIntegerExponent e)
      (Just (NVInt x), Just (NVInt e)) -> Right (Just (NVInt (x ^ e)))
      (Just x, Just e) -> Right (Just (NVFloat (numericDouble x ** numericDouble e)))
      _ -> Right Nothing
    _ -> Right Nothing
  where
    binary iop fop a b = Right $ case (a, b) of
      (Just (NVInt x), Just (NVInt y)) -> Just (NVInt (iop x y))
      (Just x, Just y) -> Just (NVFloat (fop (numericDouble x) (numericDouble y)))
      _ -> Nothing
    neg (NVInt n) = NVInt (negate n)
    neg (NVFloat d) = NVFloat (negate d)
    absN (NVInt n) = NVInt (abs n)
    absN (NVFloat d) = NVFloat (abs d)

numberWord :: Store -> NumericValue -> IO Word'
numberWord s value = case value of
  NVInt n | fitsImmediate n -> pure (intWord (fromInteger n))
  NVInt n -> box s (BInt n)
  NVFloat d -> box s (BFlt d)

-- | The term of an expression with current bindings, for error reports.
exprTerm :: Machine -> Int -> Expr -> IO Term
exprTerm m base expr = case expr of
  EImm i -> pure (IntLit (toInteger i))
  EBig n -> pure (IntLit n)
  EFlt d -> pure (FloatLit d)
  EPat pattern -> buildArg m base False pattern >>= exportFor m
  EOp op operands -> Compound (opName op) <$> mapM (exprTerm m base) operands

opName :: ArithOp -> String
opName op = case op of
  OpPlus -> "plus"
  OpMinus -> "minus"
  OpMul -> "mul"
  OpDiv -> "div"
  OpMod -> "mod"
  OpPow -> "^"
  OpNeg -> "neg"
  OpAbs -> "abs"
  OpMin -> "min"
  OpMax -> "max"

-- Atoms, characters and strings compare lexicographically when both sides
-- are of the same kind; everything else compares numerically.
compareGoal :: Machine -> Int -> Expr -> Expr -> IO (Either SolveError Ordering)
compareGoal m base a b = do
  direct <- case (a, b) of
    (EPat pa, EPat pb) -> do
      wa <- buildArg m base False pa >>= deref s
      wb <- buildArg m base False pb >>= deref s
      case (tagOf wa, tagOf wb) of
        (ta, tb)
          | ta == tagAtm && tb == tagAtm -> do
              x <- atomName (symbols s) (valOf wa)
              y <- atomName (symbols s) (valOf wb)
              pure (Just (compare x y))
          | ta == tagChr && tb == tagChr -> pure (Just (compare (valOf wa) (valOf wb)))
          | ta == tagBox && tb == tagBox -> do
              x <- boxed s wa
              y <- boxed s wb
              pure $ case (x, y) of
                (BStr p, BStr q) -> Just (compare p q)
                _ -> Nothing
          | otherwise -> pure Nothing
    _ -> pure Nothing
  case direct of
    Just ordering -> pure (Right ordering)
    Nothing -> do
      ea <- evalExpr m base a
      eb <- evalExpr m base b
      case (ea, eb) of
        (Left err, _) -> pure (Left err)
        (_, Left err) -> pure (Left err)
        (Right Nothing, _) -> Left . InstantiationError <$> exprTerm m base a
        (_, Right Nothing) -> Left . InstantiationError <$> exprTerm m base b
        (Right (Just x), Right (Just y)) -> pure (Right (compareNumeric x y))
  where
    s = mStore m

cmpAccepts :: CmpOp -> Ordering -> Bool
cmpAccepts op ordering = case op of
  CmpGt -> ordering == GT
  CmpLt -> ordering == LT
  CmpGte -> ordering /= LT
  CmpLte -> ordering /= GT

-- ─── type checks ─────────────────────────────────────────────────────────────

typeCheck :: Machine -> Check -> Word' -> IO Bool
typeCheck m check w0 = do
  w <- deref s w0
  let tag = tagOf w
  case check of
    CkVar -> pure (tag == tagRef)
    CkNonvar -> pure (tag /= tagRef)
    CkGround -> isGroundWord s w
    CkInt -> boxedIs tag w (\b -> case b of BInt _ -> True; _ -> False) (tag == tagInt)
    CkFloat -> boxedIs tag w (\b -> case b of BFlt _ -> True; _ -> False) False
    CkNum -> boxedIs tag w (\b -> case b of BStr _ -> False; _ -> True) (tag == tagInt)
    CkStr -> boxedIs tag w (\b -> case b of BStr _ -> True; _ -> False) False
    CkAtom -> pure (tag == tagAtm)
    CkChar -> pure (tag == tagChr)
    CkList -> properList w
  where
    s = mStore m
    boxedIs tag w predicate immediate
      | tag == tagBox = predicate <$> boxed s w
      | otherwise = pure immediate
    properList w
      | w == cpNil (mCore m) = pure True
      | tagOf w == tagStr = do
          f <- readCell s (valOf w)
          if funKey f /= cpCons (mCore m)
            then pure False
            else readCell s (valOf w + 2) >>= deref s >>= properList
      | otherwise = pure False

-- ─── contracts ───────────────────────────────────────────────────────────────

selectSignature :: Machine -> Pred -> IO (Either SolveError (Maybe P.Signature))
selectSignature m predicate = case pDecls predicate of
  [] -> pure (Right Nothing)
  sigs -> do
    args <- mapM (readArg s) [0 .. pArity predicate - 1]
    grounds <- mapM (isGroundWord s) args
    let inOk sig = and [g | (S.ArgSpec _ mode, g) <- zip (P.sigArgs sig) grounds, mode == S.ModeIn]
    case filter inOk sigs of
      (sig : _) -> do
        problem <- firstProblem [checkSort i spec w | (i, spec, w) <- zip3 [1 ..] (P.sigArgs sig) args]
        pure (maybe (Right (Just sig)) Left problem)
      [] -> case [i | sig <- take 1 sigs, (i, S.ArgSpec _ S.ModeIn, False) <- zip3 [1 ..] (P.sigArgs sig) grounds] of
        (i : _) -> Left . ModeError key i <$> exportFor m (args !! (i - 1))
        [] -> pure (Right Nothing)
  where
    s = mStore m
    key = pKey predicate
    checkSort i (S.ArgSpec sort _) w = do
      ok <- sortMatches m sort w
      if ok then pure Nothing else Just . SortError key i sort <$> exportFor m w

firstProblem :: [IO (Maybe SolveError)] -> IO (Maybe SolveError)
firstProblem [] = pure Nothing
firstProblem (check : rest) = do
  problem <- check
  case problem of
    Just err -> pure (Just err)
    Nothing -> firstProblem rest

sortMatches :: Machine -> S.Sort -> Word' -> IO Bool
sortMatches m sort w0 = do
  w <- deref s w0
  let tag = tagOf w
  if tag == tagRef
    then pure True
    else case sort of
      S.SAny -> pure True
      S.SNone -> pure True
      S.SInt -> boxedIs tag w (\b -> case b of BInt _ -> True; _ -> False) (tag == tagInt)
      S.SFloat -> boxedIs tag w (\b -> case b of BFlt _ -> True; _ -> False) False
      S.SNum -> boxedIs tag w (\b -> case b of BStr _ -> False; _ -> True) (tag == tagInt)
      S.SStr -> boxedIs tag w (\b -> case b of BStr _ -> True; _ -> False) False
      S.SChar -> pure (tag == tagChr)
      S.SAtom -> pure (tag == tagAtm)
      S.SList element
        | w == cpNil (mCore m) -> pure True
        | tag == tagStr -> do
            f <- readCell s (valOf w)
            if funKey f /= cpCons (mCore m)
              then pure False
              else do
                hd <- readCell s (valOf w + 1)
                tl <- readCell s (valOf w + 2)
                okHead <- sortMatches m element hd
                if okHead then sortMatches m sort tl else pure False
        | otherwise -> pure False
  where
    s = mStore m
    boxedIs tag w predicate immediate
      | tag == tagBox = predicate <$> boxed s w
      | otherwise = pure immediate

checkOutputs :: Machine -> PredKey -> P.Signature -> [Word'] -> IO (Maybe SolveError)
checkOutputs m key signature args =
  firstProblem [check i spec w | (i, spec, w) <- zip3 [1 ..] (P.sigArgs signature) args]
  where
    s = mStore m
    check i (S.ArgSpec sort mode) w = do
      ground <- if mode == S.ModeOut then isGroundWord s w else pure True
      if not ground
        then Just . OutputModeError key i <$> exportTerm s w
        else do
          ok <- sortMatches m sort w
          if ok then pure Nothing else Just . SortError key i sort <$> exportFor m w

commitsAfterSuccess :: Machine -> Pred -> Maybe P.Signature -> IO Bool
commitsAfterSuccess m predicate signature = case signature of
  Just sig -> pure (P.sigDet sig == S.Det || P.sigDet sig == S.Semidet)
  Nothing -> case pSwitch predicate of
    Nothing -> pure False
    Just positions -> switchGround (mStore m) positions

-- | Are the switch arguments ground? Immediate words answer at once.
switchGround :: Store -> [Int] -> IO Bool
switchGround _ [] = pure True
switchGround s (i : rest) = do
  w <- readArg s i
  ok <- case tagOf w of
    t | t == tagInt || t == tagAtm || t == tagChr || t == tagBox -> pure True
      | otherwise -> isGroundWord s w
  if ok then switchGround s rest else pure False

-- ─── exchange with the public state ──────────────────────────────────────────

-- | Export a term with the reference engine's variable names: query
-- variables by position, activation variables through their markers, and
-- anything else after the current fresh id.
exportFor :: Machine -> Word' -> IO Term
exportFor m word = do
  let n = cpQueryVars (mCore m)
      s = mStore m
  names <- newIORef (IM.fromList [(i, i) | i <- [0 .. n - 1]])
  next <- newIORef =<< freshId s
  term <- exportTermWith s names next word
  -- Remember where each exported variable lives for the constraint store.
  seen <- readIORef names
  when (IM.size seen > n) $
    modifyIORef' (mVarCells m) (\cells' -> IM.foldlWithKey' (\acc addr ident -> if ident < n then acc else IM.insert ident addr acc) cells' seen)
  pure term

-- | The immutable solver state of the current answer: query variables bound
-- to fully dereferenced terms, internal variables numbered after them.
exportState :: Machine -> IO SolverState
exportState m = do
  let n = cpQueryVars (mCore m)
      s = mStore m
  names <- newIORef (IM.fromList [(i, i) | i <- [0 .. n - 1]])
  next <- newIORef =<< freshId s
  bindings <- forM [0 .. n - 1] $ \i -> do
    term <- exportTermWith s names next (refWord i)
    pure (i, term)
  fresh <- freshId s
  events <- readIORef (mOutput m)
  count <- outLen s
  store <- readIORef (mCLP m)
  tables <- readIORef (mTables m)
  dynamic <- readIORef (mDynamic m)
  let subst = IM.fromList [(i, term) | (i, term) <- bindings, term /= Var i]
      base = initialState fresh
  pure
    base
      { ssStore = store {CLP.stSubst = IM.union subst (CLP.stSubst store)},
        ssOutput = events,
        ssOutLen = count,
        ssTables = tables,
        ssDynamic = dynamic
      }

-- | Export a goal for @call/N@ and the leaf builtins: distinct unbound
-- cells become variables @0, 1, ...@ whose words the alias table records.
exportGoal :: Machine -> IORef (IM.IntMap Word') -> Word' -> IO Term
exportGoal m aliases w0 = do
  w <- deref s w0
  case tagOf w of
    t | t == tagRef -> do
          table <- readIORef aliases
          case [v | (v, word) <- IM.toList table, word == w] of
            (v : _) -> pure (Var v)
            [] -> do
              let v = IM.size table
              writeIORef aliases (IM.insert v w table)
              pure (Var v)
      | t == tagStr -> do
          f <- readCell s (valOf w)
          (name, arity) <- functorName (symbols s) (funId f)
          children <- forM [1 .. arity] $ \i -> readCell s (valOf w + i) >>= exportGoal m aliases
          pure (Compound name children)
      | otherwise -> exportTerm s w
  where
    s = mStore m

showValue :: Term -> String
showValue (StrLit str) = str
showValue t = show t


-- ─── tabling ─────────────────────────────────────────────────────────────────

-- | The canonical form of the saved call with current bindings, and the
-- number of its free variables.
canonicalCall :: Machine -> String -> Int -> Int -> IO (Term, Int)
canonicalCall m name saved arity = do
  args <- forM [0 .. arity - 1] $ \i -> readCell (mStore m) (saved + i) >>= exportFor m
  let (answer, vars) = canonicalize emptySubst (if null args then Atom name else Compound name args)
  pure (answer, length vars)

-- | A call to a tabled predicate: contracts as for an ordinary call, then
-- the reference's variant table and linear fixpoint.
callTabled :: Machine -> Pred -> Cont -> IO Step
callTabled m predicate cont0 = do
  let s = mStore m
      key = pKey predicate
      n = pArity predicate
  top <- heapTop s
  limit <- readReg s rGCLIM
  cont <- if top > limit then collect m cont0 n else pure cont0
  selected <- selectSignature m predicate
  case selected of
    Left err -> raiseError m err
    Right signature -> do
      commits <- commitsAfterSuccess m predicate signature
      let required = case signature of
            Just sig | P.sigDet sig == S.Det -> Just S.Det
            Just sig | P.sigDet sig == S.Multi -> Just S.Multi
            _ -> Nothing
      checked <- case signature of
        Just sig -> do
          args <- mapM (readArg s) [0 .. n - 1]
          pure (Just (key, sig, args))
        Nothing -> pure Nothing
      let depth = contDepth cont + 1
      entry <- readIORef (mChoiceTop m)
      guard <- case required of
        Nothing -> pure Nothing
        Just det -> do
          flag <- newIORef False
          _ <- pushChoice m (AltGuard key det flag)
          pure (Just flag)
      let returnCont = case (commits, guard, checked) of
            (False, Nothing, Nothing) -> cont
            _ -> CReturn (if commits then entry else -1) guard checked cont
      saved <- saveArgs s n
      (callKey, _) <- canonicalCall m (fst key) saved n
      store <- readIORef (mCLP m)
      constrained <- callConstrained m store saved n
      tables <- readIORef (mTables m)
      if constrained
        then do
          loadArgs s saved n
          callClauses m predicate entry depth returnCont
        else case Map.lookup callKey tables of
          Just te
            | teComplete te ->
                raiseItems m [BranchExhausted | teTruncated te] (consumeAnswers m (teAnswers te) saved n returnCont)
            | otherwise ->
                raiseItems m [ConsumedIncomplete callKey] (consumeAnswers m (teAnswers te) saved n returnCont)
          Nothing -> do
            entryOut <- outLen s
            issues <- newIORef []
            fixRef <- newIORef Fix
              { fxKey = callKey, fxPred = predicate, fxArgs = saved, fxEntryOut = entryOut, fxDepth = depth,
                fxTables = tables, fxAnswers = [], fxSet = Set.empty, fxIteration = 0, fxFound = [],
                fxCompleted = Map.empty, fxIssues = issues, fxCont = returnCont, fxUnsafe = False }
            startIteration m fixRef

-- | Does the saved call mention a constrained variable?
callConstrained :: Machine -> CLP.Store -> Int -> Int -> IO Bool
callConstrained m store saved arity = do
  args <- forM [0 .. arity - 1] $ \i -> readCell (mStore m) (saved + i) >>= exportFor m
  pure (any (CLP.isConstrained store) (concatMap S.termVarIds args))

-- | One fixpoint iteration: all clauses run against the partial table.
startIteration :: Machine -> IORef Fix -> IO Step
startIteration m fixRef = do
  fx <- readIORef fixRef
  let s = mStore m
      partial = TableEntry False False (fxAnswers fx) (fxSet fx)
  writeIORef (mTables m) (Map.insert (fxKey fx) partial (fxTables fx))
  issues <- newIORef []
  writeIORef fixRef fx {fxFound = [], fxCompleted = Map.empty, fxIssues = issues}
  sentinel <- pushChoice m (AltTable fixRef)
  pushScope m (SBuffer issues)
  loadArgs s (fxArgs fx) (pArity (fxPred fx))
  if fxDepth fx > maxResolutionDepth
    then raiseItems m [BranchExhausted] (backtrack m)
    else callClauses m (fxPred fx) (sentinel + 1) (fxDepth fx) (CExitTable fixRef)

-- | The inner search of an iteration is exhausted; the state is back at the
-- call entry.
finishIteration :: Machine -> IORef Fix -> IO Step
finishIteration m fixRef = do
  fx <- readIORef fixRef
  issues <- reverse <$> readIORef (fxIssues fx)
  let extracted = reverse (fxFound fx)
      fresh = dedup (fxSet fx) extracted
      answers' = fxAnswers fx ++ fresh
      set' = foldr (\(a, _, _) -> Set.insert a) (fxSet fx) fresh
      deps = nubTerms [k | ConsumedIncomplete k <- issues, k /= fxKey fx]
      others = [i | i@(BranchError _) <- issues] ++ [BranchExhausted | any isExhausted issues]
      completed = Map.union (Map.filter teComplete (fxTables fx)) (fxCompleted fx)
      tables' = Map.union completed (Map.delete (fxKey fx) (fxTables fx))
      converged = null fresh
      gaveUp = fxIteration fx >= maxTableIterations
  if fxUnsafe fx
    then do
      writeIORef (mTables m) (fxTables fx)
      loadArgs (mStore m) (fxArgs fx) (pArity (fxPred fx))
      entry <- readIORef (mChoiceTop m)
      callClauses m (fxPred fx) entry (fxDepth fx) (fxCont fx)
    else if converged || gaveUp
    then do
      let tables'' =
            if null deps
              then Map.insert (fxKey fx) (TableEntry True (not converged) answers' set') tables'
              else tables'
      writeIORef (mTables m) tables''
      raiseItems m (map ConsumedIncomplete deps ++ others ++ [BranchExhausted | gaveUp])
        (consumeAnswers m answers' (fxArgs fx) (pArity (fxPred fx)) (fxCont fx))
    else do
      writeIORef fixRef fx {fxTables = tables', fxAnswers = answers', fxSet = set', fxIteration = fxIteration fx + 1}
      startIteration m fixRef
  where
    dedup _ [] = []
    dedup seen ((a, n, o) : rest)
      | Set.member a seen = dedup seen rest
      | otherwise = (a, n, o) : dedup (Set.insert a seen) rest
    nubTerms = foldr (\k acc -> if k `elem` acc then acc else k : acc) [] . reverse

-- | Consume table answers in order: each instantiates fresh variables,
-- replays its output and unifies with the saved call.
consumeAnswers :: Machine -> [(Term, Int, [OutputEvent])] -> Int -> Int -> Cont -> IO Step
consumeAnswers m answers saved arity cont = case answers of
  [] -> backtrack m
  ((answer, count, produced) : rest) -> do
    unless (null rest) $ () <$ pushChoice m (AltAnswers rest saved arity cont)
    let s = mStore m
    fresh <- freshId s
    block <- allocSlots s fresh (max 1 count)
    setFreshId s (fresh + count)
    table <- newIORef (IM.fromList [(v, refWord (block + v)) | v <- [0 .. count - 1]])
    mapM_ (emitOutput m) produced
    let args = case answer of Compound _ as -> as; _ -> []
    ok <- unifyArgs s table 0 args
    if ok then run m cont else backtrack m
  where
    unifyArgs _ _ _ [] = pure True
    unifyArgs s table i (term : rest) = do
      w <- importTermWords s table term
      cell <- readCell s (saved + i)
      ok <- unify s cell w
      if ok then unifyArgs s table (i + 1) rest else pure False

-- | Retract alternatives: each fact that unifies with the saved term is
-- removed from the facts as they were when the retract began.
retractFacts :: Machine -> [(Int, Term, Int)] -> PredKey -> Int -> Cont -> IO Step
retractFacts m facts key saved cont = case facts of
  [] -> backtrack m
  ((index, fact, count) : rest) -> do
    unless (null rest) $ () <$ pushChoice m (AltRetract rest key saved cont)
    let s = mStore m
    fresh <- freshId s
    block <- allocSlots s fresh (max 1 count)
    setFreshId s (fresh + count)
    table <- newIORef (IM.fromList [(v, refWord (block + v)) | v <- [0 .. count - 1]])
    imported <- importTermWords s table fact
    target <- readCell s saved
    ok <- unify s target imported
    if ok
      then do
        modifyIORef' (mDynamic m) (Map.adjust (\fs -> [f | (j, f) <- zip [0 :: Int ..] fs, j /= index]) key)
        run m cont
      else backtrack m

-- | Trace-mode self check after a collection.
checkInvariants :: Machine -> Cont -> IO ()
checkInvariants m cont = do
  let s = mStore m
  top <- heapTop s
  arr <- readIORef (cells s)
  forM_ [0 .. top - 1] $ \a -> do
    w <- unsafeRead arr a
    when ((tagOf w == tagRef || tagOf w == tagStr) && (valOf w < 0 || valOf w >= top)) $
      traceMsg ("INVARIANT: cell " ++ show a ++ " points outside the heap: " ++ show w)
  tr <- readIORef (trail s)
  trTop <- trailTop s
  let walk i
        | i < 0 = pure ()
        | otherwise = do
            e <- unsafeRead tr i
            let addr = e `div` 2
            when (addr >= top) (traceMsg ("INVARIANT: trail entry " ++ show i ++ " -> dead cell " ++ show addr))
            w <- if addr < top then unsafeRead arr addr else pure 0
            when (addr < top && even e && w == refWord addr) (traceMsg ("INVARIANT: trail entry " ++ show i ++ " for unbound cell " ++ show addr))
            walk (if odd e then i - 2 else i - 1)
  walk (trTop - 1)
  choiceTop <- readIORef (mChoiceTop m)
  choices <- forM [0 .. choiceTop - 1] (readChoice m)
  let hs = map chH choices
      trs = map chTR choices
  when (hs /= IM.elems (IM.fromList (zip [0 :: Int ..] hs)) || or (zipWith (>) hs (drop 1 hs))) (traceMsg ("INVARIANT: choice H marks not ascending " ++ show hs))
  when (or (zipWith (>) trs (drop 1 trs)) || any (> trTop) trs) (traceMsg ("INVARIANT: choice trail marks wrong " ++ show trs ++ " top " ++ show trTop))
  let checkCont c = case c of
        CGoals _ base _ _ next -> checkBase base >> checkCont next
        CReturn _ _ _ next -> checkCont next
        CExitIf _ _ base _ _ next -> checkBase base >> checkCont next
        CExitFindAll _ _ _ base _ _ _ -> checkBase base
        CExitMinimize _ base _ -> checkBase base
        _ -> pure ()
      checkBase base = when (base > 0) $ do
        marker <- unsafeRead arr (base - 1)
        unless (tagOf marker == tagFun) (traceMsg ("INVARIANT: block base " ++ show base ++ " has no marker: " ++ show marker))
      checkAlt alt = case alt of
        AltClauses _ _ _ _ c -> checkCont c
        AltGoals _ base _ _ c -> checkBase base >> checkCont c
        AltNot _ _ c -> checkCont c
        AltIf _ e c -> forM_ e (\(_, base, _, _) -> checkBase base) >> checkCont c
        AltFindAll _ _ _ base _ c -> checkBase base >> checkCont c
        AltLeaf _ _ c -> checkCont c
        AltAnswers _ _ _ c -> checkCont c
        AltRetract _ _ _ c -> checkCont c
        AltMinimize _ _ c -> checkCont c
        _ -> pure ()
  checkCont cont
  forM_ choices (checkAlt . chAlt)
  traceMsg "GC checked"

-- ─── collection ──────────────────────────────────────────────────────────────

-- | Mark-compact collection of the cell store at a call boundary. Roots are
-- the first @nargs@ argument registers, the current continuation, every
-- choice point's alternatives and continuation, and findall results. Live
-- cells slide down in address order, so every age relation survives; the
-- control records are rebuilt with forwarded addresses and the trail keeps
-- only entries for live cells.
collect :: Machine -> Cont -> Int -> IO Cont
collect m cont nargs = do
  let s = mStore m
      queryCells = max 1 (cpQueryVars (mCore m))
  top <- heapTop s
  traceMsg ("GC at H=" ++ show top)
  arr <- readIORef (cells s)
  marks <- newArray (0, top) False :: IO (IOUArray Int Bool)
  -- Cells with a trail entry can become unbound again; their ids matter.
  trailed <- newArray (0, top) False :: IO (IOUArray Int Bool)
  do
    trailArr0 <- readIORef (trail s)
    trailLen0 <- trailTop s
    let noteTrail i
          | i < 0 = pure ()
          | otherwise = do
              entry <- unsafeRead trailArr0 i
              let addr = entry `div` 2
              when (addr < top) (unsafeWrite trailed addr True)
              noteTrail (if odd entry then i - 2 else i - 1)
    noteTrail (trailLen0 - 1)
  stackRef <- newIORef =<< (newArray (0, 4095) 0 :: IO (IOUArray Int Int))
  stackTop <- newIORef (0 :: Int)
  let push a = do
        st <- readIORef stackRef
        i <- readIORef stackTop
        size <- getNumElements st
        st' <-
          if i < size
            then pure st
            else do
              grown <- newArray (0, size * 2 - 1) 0
              forM_ [0 .. i - 1] $ \j -> unsafeRead st j >>= unsafeWrite grown j
              writeIORef stackRef grown
              pure grown
        unsafeWrite st' i a
        writeIORef stackTop (i + 1)
      markCell a = do
        seen <- unsafeRead marks a
        if seen then pure () else unsafeWrite marks a True >> push a >> markBlockOf a
      -- A live slot that is unbound, or bound but undoable, keeps its whole
      -- activation block, marker included, so its logical id survives
      -- compaction. Functor words below a cell are either its structure's
      -- functor (block size 0) or a block marker.
      markBlockOf a = do
        w0 <- unsafeRead arr a
        undoable <- unsafeRead trailed a
        when ((tagOf w0 == tagRef && valOf w0 == a) || undoable) $ scanBlock a
      scanBlock a = do
        let scan i
              | i < 0 = pure ()
              | otherwise = do
                  w <- unsafeRead arr i
                  if tagOf w == tagFun
                    then do
                      let n = markerVars w
                      when (n > 0 && a <= i + n) $ do
                        unsafeWrite marks i True
                        forM_ [i + 1 .. i + n] markCell
                    else scan (i - 1)
        scan (a - 1)
      markStructure a = do
        seen <- unsafeRead marks a
        if seen
          then pure ()
          else do
            f <- unsafeRead arr a
            unsafeWrite marks a True
            forM_ [a + 1 .. a + funArity f] markCell
      markWord w
        | tagOf w == tagRef = markCell (valOf w)
        | tagOf w == tagStr = markStructure (valOf w)
        | otherwise = pure ()
      drain = do
        i <- readIORef stackTop
        if i == 0
          then pure ()
          else do
            st <- readIORef stackRef
            a <- unsafeRead st (i - 1)
            writeIORef stackTop (i - 1)
            w <- unsafeRead arr a
            if tagOf w == tagRef
              then (if valOf w /= a then markCell (valOf w) else pure ())
              else if tagOf w == tagStr then markStructure (valOf w) else pure ()
            drain
      markBlock base
        | base == 0 = forM_ [0 .. queryCells - 1] markCell
        | otherwise = do
            marker <- unsafeRead arr (base - 1)
            unsafeWrite marks (base - 1) True
            forM_ [base .. base + markerVars marker - 1] markCell
      markCont c = case c of
        CDone -> pure ()
        CGoals _ base _ _ next -> markBlock base >> markCont next
        CReturn _ _ check next -> do
          forM_ (maybe [] (\(_, _, ws) -> ws) check) markWord
          markCont next
        CExitIf _ _ base _ _ next -> markBlock base >> markCont next
        CExitNot _ _ _ -> pure ()
        CExitFindAll _ results _ base _ _ _ -> markBlock base >> markResults results
        CExitTable fixRef -> do
          fx <- readIORef fixRef
          forM_ [fxArgs fx .. fxArgs fx + pArity (fxPred fx) - 1] markCell
          markCont (fxCont fx)
        CExitMinimize _ base _ -> markBlock base
      markResults ref = do
        collected <- readIORef ref
        forM_ collected (markCopy . fst)
      markCopy copy = case copy of
        CpRef a -> markCell a
        CpStruct _ children -> mapM_ markCopy children
        _ -> pure ()
      markAlt alt = case alt of
        AltClauses predicate _ saved _ c -> do
          forM_ [saved .. saved + pArity predicate - 1] markCell
          markCont c
        AltGoals _ base _ _ c -> markBlock base >> markCont c
        AltGuard _ _ _ -> pure ()
        AltNot _ _ c -> markCont c
        AltIf _ elseGoals c -> do
          forM_ elseGoals (\(_, base, _, _) -> markBlock base)
          markCont c
        AltFindAll results _ _ base _ c -> markBlock base >> markResults results >> markCont c
        AltLeaf _ _ c -> markCont c
        AltTable fixRef -> do
          fx <- readIORef fixRef
          forM_ [fxArgs fx .. fxArgs fx + pArity (fxPred fx) - 1] markCell
          markCont (fxCont fx)
        AltAnswers _ saved arity c -> forM_ [saved .. saved + arity - 1] markCell >> markCont c
        AltRetract _ _ saved c -> markCell saved >> markCont c
        AltMinimize ref _ c -> do
          mn <- readIORef ref
          forM_ (mnBest mn) $ \(_, bound, _, _, _, _, _) -> forM_ bound $ \(addr, copy) -> markCell addr >> markCopy copy
          markCont c
  -- The query block is a root even when no continuation names it any
  -- more: the answer is exported from it.
  forM_ [0 .. queryCells - 1] markCell
  forM_ [0 .. nargs - 1] $ \i -> readArg s i >>= markWord
  markCont cont
  choiceTop <- readIORef (mChoiceTop m)
  forM_ [0 .. choiceTop - 1] $ \i -> readChoice m i >>= markAlt . chAlt
  drain
  -- Forwarding: fwd a = live cells below a.
  fwd <- newArray (0, top) 0 :: IO (IOUArray Int Int)
  let count !a !n
        | a > top = pure ()
        | otherwise = do
            unsafeWrite fwd a n
            live <- if a < top then unsafeRead marks a else pure False
            count (a + 1) (if live then n + 1 else n)
  count 0 0
  newTop <- unsafeRead fwd top
  -- Entries from abandoned branches may point above the heap top.
  let liveCell addr = if addr < top then unsafeRead marks addr else pure False
      forward a = unsafeRead fwd a
      reloc w
        | tagOf w == tagRef = refWord <$> forward (valOf w)
        | tagOf w == tagStr = strWord <$> forward (valOf w)
        | otherwise = pure w
      slide !a
        | a >= top = pure ()
        | otherwise = do
            live <- unsafeRead marks a
            when live $ do
              w <- unsafeRead arr a
              w' <- reloc w
              a' <- forward a
              unsafeWrite arr a' w'
            slide (a + 1)
  -- Trail: keep entries of live cells, remember how many survive below
  -- each original index for the choice points' marks.
  trailArr <- readIORef (trail s)
  trailLen <- trailTop s
  keptBelow <- newArray (0, trailLen) 0 :: IO (IOUArray Int Int)
  kept <- newIORef (0 :: Int)
  let classify i acc
        | i < 0 = pure acc
        | otherwise = do
            entry <- unsafeRead trailArr i
            if odd entry then classify (i - 2) ((i - 1, 2, entry) : acc) else classify (i - 1) ((i, 1, entry) : acc)
  entries <- classify (trailLen - 1) []
  forM_ entries $ \(start, len, entry) -> do
    k <- readIORef kept
    forM_ [start .. start + len - 1] $ \j -> unsafeWrite keptBelow j k
    let addr = entry `div` 2
    live <- unsafeRead marks addr
    when live $ do
      addr' <- forward addr
      if len == 1
        then unsafeWrite trailArr k (addr' * 2)
        else do
          old <- unsafeRead trailArr start
          unsafeWrite trailArr k old
          unsafeWrite trailArr (k + 1) (addr' * 2 + 1)
      writeIORef kept (k + len)
  keptTotal <- readIORef kept
  unsafeWrite keptBelow trailLen keptTotal
  setTrailTop s keptTotal
  -- Relocate control records before sliding: they read markers via old
  -- addresses only through 'forward', which does not touch cells.
  let relocBlock base
        | base == 0 = pure 0
        | otherwise = (+ 1) <$> forward (base - 1)
      relocCont c = case c of
        CDone -> pure CDone
        CGoals goals base barrier depth next ->
          CGoals goals <$> relocBlock base <*> pure barrier <*> pure depth <*> relocCont next
        CReturn commit guard check next -> do
          check' <- case check of
            Nothing -> pure Nothing
            Just (key, sig, ws) -> Just . (,,) key sig <$> mapM reloc ws
          CReturn commit guard check' <$> relocCont next
        CExitIf sentinel thenGoals base barrier depth next ->
          CExitIf sentinel thenGoals <$> relocBlock base <*> pure barrier <*> pure depth <*> relocCont next
        CExitNot sentinel flag depth -> pure (CExitNot sentinel flag depth)
        -- Shared buffers are relocated once, through the sentinel's alternative.
        CExitFindAll sentinel results template base entryHeap entryOut depth ->
          CExitFindAll sentinel results template <$> relocBlock base <*> forward entryHeap <*> pure entryOut <*> pure depth
        CExitTable fixRef -> pure (CExitTable fixRef)
        CExitMinimize cost base ref -> CExitMinimize cost <$> relocBlock base <*> pure ref
      relocResults ref = do
        collected <- readIORef ref
        relocated <- forM collected $ \(copy, produced) -> (\c -> (c, produced)) <$> relocCopy copy
        writeIORef ref relocated
      relocCopy copy = case copy of
        CpRef a -> CpRef <$> forward a
        CpStruct f children -> CpStruct f <$> mapM relocCopy children
        other -> pure other
      relocAlt alt = case alt of
        AltClauses predicate more saved depth c ->
          AltClauses predicate more <$> forward saved <*> pure depth <*> relocCont c
        AltGoals goals base barrier depth c ->
          AltGoals goals <$> relocBlock base <*> pure barrier <*> pure depth <*> relocCont c
        AltGuard key det flag -> pure (AltGuard key det flag)
        AltNot flag buffer c -> AltNot flag buffer <$> relocCont c
        AltIf counter elseGoals c -> do
          elseGoals' <- case elseGoals of
            Nothing -> pure Nothing
            Just (goals, base, barrier, depth) -> do
              base' <- relocBlock base
              pure (Just (goals, base', barrier, depth))
          AltIf counter elseGoals' <$> relocCont c
        AltFindAll results buffer target base depth c -> do
          relocResults results
          AltFindAll results buffer target <$> relocBlock base <*> pure depth <*> relocCont c
        AltLeaf items previous c -> AltLeaf items previous <$> relocCont c
        AltTable fixRef -> do
          fx <- readIORef fixRef
          saved' <- forward (fxArgs fx)
          c' <- relocCont (fxCont fx)
          writeIORef fixRef fx {fxArgs = saved', fxCont = c'}
          pure (AltTable fixRef)
        AltAnswers answers saved arity c ->
          AltAnswers answers <$> forward saved <*> pure arity <*> relocCont c
        AltRetract facts key saved c ->
          AltRetract facts key <$> forward saved <*> relocCont c
        AltMinimize ref buffer c -> do
          mn <- readIORef ref
          best' <- case mnBest mn of
            Nothing -> pure Nothing
            Just (n, bound, produced, tables, dynamic, store, watched) -> do
              bound' <- forM bound $ \(addr, copy) -> (,) <$> forward addr <*> relocCopy copy
              watchedList <- forM (IS.toList watched) $ \addr -> do
                keep <- liveCell addr
                if keep then (: []) <$> forward addr else pure []
              pure (Just (n, bound', produced, tables, dynamic, store, IS.fromList (concat watchedList)))
          entryHeap' <- forward (mnEntryHeap mn)
          entryTrail' <- unsafeRead keptBelow (mnEntryTrail mn)
          writeIORef ref mn {mnEntryHeap = entryHeap', mnEntryTrail = entryTrail', mnBest = best'}
          AltMinimize ref buffer <$> relocCont c
  cont' <- relocCont cont
  forM_ [0 .. nargs - 1] $ \i -> readArg s i >>= reloc >>= writeArg s i
  varCells <- readIORef (mVarCells m)
  live <- forM (IM.toList varCells) $ \(ident, addr) -> do
    keep <- liveCell addr
    if keep then (\a -> [(ident, a)]) <$> forward addr else pure []
  writeIORef (mVarCells m) (IM.fromList (concat live))
  watched <- readIORef (mWatched m)
  watched' <- forM (IS.toList watched) $ \addr -> do
    keep <- liveCell addr
    if keep then (: []) <$> forward addr else pure []
  writeIORef (mWatched m) (IS.fromList (concat watched'))
  pendingCount <- readReg s rBOUND
  when (pendingCount > 0) $ do
    pendingAddrs <- drainBound s
    forM_ pendingAddrs $ \addr -> do
      keep <- liveCell addr
      when keep (forward addr >>= recordBoundCell s)
  forM_ [0 .. choiceTop - 1] $ \i -> do
    choice <- readChoice m i
    h' <- forward (chH choice)
    tr' <- unsafeRead keptBelow (chTR choice)
    alt' <- relocAlt (chAlt choice)
    watchedList <- forM (IS.toList (chWatched choice)) $ \addr -> do
      keep <- liveCell addr
      if keep then (: []) <$> forward addr else pure []
    writeChoice m i choice {chH = h', chTR = tr', chAlt = alt', chWatched = IS.fromList (concat watchedList)}
  slide 0
  setHeapTop s newTop
  refreshHb m
  when traceOn (checkInvariants m cont')
  floor' <- readReg s rGCLIM
  writeReg s rGCLIM (max (min floor' initialCollectLimit) (newTop * 4))
  pure cont'

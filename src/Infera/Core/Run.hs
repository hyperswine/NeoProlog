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
  )
where

import Control.Monad (foldM, forM, forM_, when)
import Data.Array ((!))
import Data.Array.Base (getNumElements, unsafeRead, unsafeWrite)
import Data.Array.IO (IOArray, newArray_)
import Data.IORef
import qualified Data.IntMap.Strict as IM
import Infera.Arith (NumericValue (..), compareNumeric, deepEval, numericDouble, numericTerm)
import qualified Infera.CLP as CLP
import Infera.Core.Compile
import Infera.Core.Store
import Infera.Engine.Reference (OutputEvent (..), SearchItem (..), SolverState (..), initialState, maxResolutionDepth)
import Infera.Error (PredKey, SolveError (..))
import qualified Infera.Program as P
import qualified Infera.Syntax as S
import Infera.Syntax (Term (..))
import Infera.Unify (emptySubst)

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

data Choice = Choice
  { chH :: !Int,
    chTR :: !Int,
    chOut :: !Int,
    chScopes :: !Int,
    chFresh :: !Int,
    chAlt :: !Alt
  }

data Alt
  = AltClauses !Pred [Int] [Word'] !Int Cont
  | AltGoals [Goal] !Int !Int !Int Cont
  | AltGuard !PredKey !S.Det !(IORef Bool)
  | AltNot !(IORef Bool) !(IORef [SearchItem]) Cont
  | AltIf !(IORef Int) (Maybe ([Goal], Int, Int, Int)) Cont
  | AltFindAll !(IORef [(Copy, [OutputEvent])]) !(IORef [SearchItem]) Pattern !Int !Int Cont

-- Issue scopes: a negation or findall buffers issues until its outcome is
-- known; a condition only counts them.
data Scope = SBuffer !(IORef [SearchItem]) | SCount !(IORef Int)

-- A findall solution copied out of the heap. Cells older than the findall
-- entry are kept by reference; younger free variables become fresh.
data Copy = CpRef !Int | CpFresh !Int !Int | CpWord !Word' | CpStruct !Word' [Copy]

data Machine = Machine
  { mStore :: !Store,
    mProgram :: !P.Program,
    mCore :: !CoreProgram,
    mChoices :: !(IORef (IOArray Int Choice)),
    mChoiceTop :: !(IORef Int),
    mScopes :: !(IORef [Scope]),
    mOutput :: !(IORef [OutputEvent])
  }

-- | Compile and start a query. Left names the construct that puts the
-- program outside the supported subset; Right produces the first step.
runCore :: P.Program -> S.Query -> IO (Either String (IO Step))
runCore program query = do
  syms <- newSymbols
  store <- newStore syms
  compiled <- compileProgram store program query
  case compiled of
    Left (Unsupported reason) -> pure (Left reason)
    Right core -> do
      choices <- newArray_ (0, 1023)
      m <- Machine store program core <$> newIORef choices <*> newIORef 0 <*> newIORef [] <*> newIORef []
      _ <- allocCells store (max 1 (cpQueryVars core))
      setFreshId store (cpQueryVars core)
      pure (Right (run m (CGoals (cpQuery core) 0 0 0 CDone)))

-- ─── choice stack ────────────────────────────────────────────────────────────

pushChoice :: Machine -> Alt -> IO Int
pushChoice m alt = do
  let s = mStore m
  h <- heapTop s
  tr <- trailTop s
  out <- outLen s
  fresh <- freshId s
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
  unsafeWrite arr' top (Choice h tr out scopes fresh alt)
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
    deliver (SCount counter : outer) = modifyIORef' counter (+ 1) >> deliver outer
    deliver (SBuffer buffer : _) = modifyIORef' buffer (item :) >> pure True

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
  CDone -> do
    state <- exportState m
    pure (Yield (Found state) (backtrack m))
  CGoals [] _ _ _ next -> run m next
  CGoals (goal : goals) base barrier depth next ->
    step m goal base barrier depth (CGoals goals base barrier depth next)
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

-- Skip exhausted goal lists so that a tail call sees its caller's return.
dropEmpty :: Cont -> Cont
dropEmpty (CGoals [] _ _ _ next) = dropEmpty next
dropEmpty cont = cont

step :: Machine -> Goal -> Int -> Int -> Int -> Cont -> IO Step
step m goal base barrier depth rest = case goal of
  GTrue -> run m rest
  GFail -> backtrack m
  GCut -> cutTo m barrier >> run m rest
  GAnd goals -> run m (CGoals goals base barrier depth rest)
  GCall ref patterns -> do
    predicate <- readIORef ref
    args <- mapM (buildArg m base True) patterns
    pending <- arithData (mStore m)
    normalized <- if pending > 0 then mapM (normalizeWord m) args else pure args
    callPredicate m predicate normalized (dropEmpty rest)
  GCallDyn direct callable extra -> do
    word <- buildArg m base False callable
    extraTerms <- mapM (\p -> buildArg m base False p >>= exportGoal m) extra
    goalTerm <- exportGoal m word
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
            compiled <- compileGoalTerm (mStore m) (mProgram m) (cpPreds (mCore m)) goalWith
            height <- readIORef (mChoiceTop m)
            run m (CGoals [compiled] base height depth rest)
  GUnify a b -> do
    wa <- buildArg m base False a
    wb <- buildArg m base False b
    ok <- unify (mStore m) wa wb
    if ok then run m rest else backtrack m
  GEquiv a b -> do
    wa <- buildArg m base False a
    wb <- buildArg m base False b
    ok <- equiv (mStore m) wa wb
    if ok then run m rest else backtrack m
  GNeq a b -> do
    wa <- buildArg m base False a
    wb <- buildArg m base False b
    ga <- isGroundWord (mStore m) wa
    gb <- isGroundWord (mStore m) wb
    if ga && gb
      then do
        same <- equiv (mStore m) wa wb
        if same then backtrack m else run m rest
      else pure (Abandon "disequality constraint on non-ground operands")
  GIs target expr -> do
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
        if ok then run m rest else backtrack m
  GCmp op a b -> do
    outcome <- compareGoal m base a b
    case outcome of
      Left err -> raiseError m err
      Right ordering -> if cmpAccepts op ordering then run m rest else backtrack m
  GOr left right -> do
    _ <- pushChoice m (AltGoals right base barrier depth rest)
    run m (CGoals left base barrier depth rest)
  GIf condition thenGoals elseGoals -> do
    counter <- newIORef 0
    sentinel <- pushChoice m (AltIf counter (fmap (\gs -> (gs, base, barrier, depth)) elseGoals) rest)
    pushScope m (SCount counter)
    run m (CGoals condition base (sentinel + 1) depth (CExitIf sentinel thenGoals base barrier depth rest))
  GOnce goals -> step m (GIf goals [] Nothing) base barrier depth rest
  GNot goals -> do
    flag <- newIORef False
    buffer <- newIORef []
    sentinel <- pushChoice m (AltNot flag buffer rest)
    pushScope m (SBuffer buffer)
    run m (CGoals goals base (sentinel + 1) depth (CExitNot sentinel flag depth))
  GFindAll template goals target -> do
    results <- newIORef []
    buffer <- newIORef []
    entryHeap <- heapTop (mStore m)
    entryOut <- outLen (mStore m)
    sentinel <- pushChoice m (AltFindAll results buffer target base depth rest)
    pushScope m (SBuffer buffer)
    run m (CGoals goals base (sentinel + 1) depth (CExitFindAll sentinel results template base entryHeap entryOut depth))
  GCheck check pattern -> do
    word <- buildArg m base False pattern
    ok <- typeCheck m check word
    if ok then run m rest else backtrack m
  GWrite newline pattern -> do
    word <- buildArg m base False pattern
    term <- exportFor m word
    emitOutput m (WriteEvent (showValue (deepEval emptySubst term)))
    when newline (emitOutput m NewlineEvent)
    run m rest
  GNl -> emitOutput m NewlineEvent >> run m rest
  GError err -> raiseError m err
  GUnsupported term -> pure (Abandon ("unsupported goal " ++ show term))

-- ─── calls ───────────────────────────────────────────────────────────────────

callPredicate :: Machine -> Pred -> [Word'] -> Cont -> IO Step
callPredicate m predicate args cont = do
  let s = mStore m
      key = pKey predicate
  derefs <- mapM (deref s) args
  selected <- selectSignature m predicate derefs
  case selected of
    Left err -> raiseError m err
    Right signature -> do
      commits <- commitsAfterSuccess m predicate signature derefs
      let required = case signature of
            Just sig | P.sigDet sig == S.Det -> Just S.Det
            Just sig | P.sigDet sig == S.Multi -> Just S.Multi
            _ -> Nothing
          checked = case signature of
            Just sig -> Just (key, sig, args)
            Nothing -> Nothing
          depth = contDepth cont + 1
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
          keys <- if pIndexed predicate then mapM (keyOfWord s) derefs else pure []
          case candidateClauses predicate keys of
            [] -> backtrack m
            [ordinal] -> do
              barrier <- readIORef (mChoiceTop m)
              tryClause m predicate ordinal args barrier depth returnCont
            (ordinal : more) -> do
              barrier <- pushChoice m (AltClauses predicate more args depth returnCont)
              tryClause m predicate ordinal args barrier depth returnCont

tryClause :: Machine -> Pred -> Int -> [Word'] -> Int -> Int -> Cont -> IO Step
tryClause m predicate ordinal args barrier depth cont = do
  let clause = pClauses predicate ! ordinal
      s = mStore m
  fresh <- freshId s
  setFreshId s (fresh + clVars clause)
  base <- allocSlots s fresh (clVars clause)
  ok <- matchHead m base (clHead clause) args
  if ok
    then run m (CGoals (clBody clause) base barrier depth cont)
    else backtrack m

matchHead :: Machine -> Int -> [Pattern] -> [Word'] -> IO Bool
matchHead _ _ [] _ = pure True
matchHead m base (pattern : patterns) (arg : args) = do
  ok <- unifyPattern m base pattern arg
  if ok then matchHead m base patterns args else pure False
matchHead _ _ _ [] = pure True

-- | Match a head pattern against a word, building only where the word is
-- an unbound variable.
unifyPattern :: Machine -> Int -> Pattern -> Word' -> IO Bool
unifyPattern m base pattern word = case pattern of
  PSlot i -> unify s (refWord (base + i)) word
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
            if f /= functor then pure False else matchChildren (valOf d + 1) children
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
  PWord w -> pure w
  PStruct functor children -> do
    words' <- mapM (buildArg m base normalize) children
    structure s functor words'
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

structure :: Store -> Word' -> [Word'] -> IO Word'
structure s functor words' = do
  addr <- pushCell s functor
  mapM_ (pushCell s) words'
  pure (strWord addr)

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
      case IM.lookup f (cpArith (mCore m)) of
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
      | otherwise = structure s f normalized

-- ─── backtracking ────────────────────────────────────────────────────────────

backtrack :: Machine -> IO Step
backtrack m = do
  top <- readIORef (mChoiceTop m)
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
      case chAlt choice of
        AltClauses predicate (ordinal : more) args depth cont -> do
          if null more
            then writeIORef (mChoiceTop m) index >> refreshHb m
            else writeChoice m index choice {chAlt = AltClauses predicate more args depth cont}
          tryClause m predicate ordinal args index depth cont
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
            then backtrack m
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
        AltFindAll results buffer target base _ cont -> do
          pop
          issues <- reverse <$> readIORef buffer
          collected <- reverse <$> readIORef results
          case [e | e@(BranchError _) <- issues] of
            (e : _) -> raiseItems m [e] (backtrack m)
            [] -> raiseItems m issues $ do
              forM_ collected $ \(_, produced) -> mapM_ (emitOutput m) produced
              list <- rebuildList m (map fst collected)
              wt <- buildArg m base False target
              ok <- unify s wt list
              if ok then run m cont else backtrack m
  where
    pop = do
      top <- readIORef (mChoiceTop m)
      writeIORef (mChoiceTop m) (top - 1)
      refreshHb m
    isError (BranchError _) = True
    isError _ = False
    isExhausted BranchExhausted = True
    isExhausted _ = False

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
                pure (CpStruct f children)
            | otherwise -> pure (CpWord w)
  go word
  where
    s = mStore m

rebuildList :: Machine -> [Copy] -> IO Word'
rebuildList m copies = do
  items <- mapM rebuildCopy copies
  foldM (\tl hd -> structure s (cpCons (mCore m)) [hd, tl]) (cpNil (mCore m)) (reverse items)
  where
    s = mStore m
    rebuildCopy copy = do
      fresh <- newIORef IM.empty
      let go c = case c of
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
            CpStruct f children -> mapM go children >>= structure s f
      go copy

outputSince :: Machine -> Int -> IO [OutputEvent]
outputSince m entryOut = do
  n <- outLen (mStore m)
  events <- readIORef (mOutput m)
  pure (reverse (take (n - entryOut) events))

-- ─── arithmetic ──────────────────────────────────────────────────────────────

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
          case IM.lookup f (cpArith (mCore m)) of
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
          if f /= cpCons (mCore m)
            then pure False
            else readCell s (valOf w + 2) >>= deref s >>= properList
      | otherwise = pure False

-- ─── contracts ───────────────────────────────────────────────────────────────

selectSignature :: Machine -> Pred -> [Word'] -> IO (Either SolveError (Maybe P.Signature))
selectSignature m predicate args = case pDecls predicate of
  [] -> pure (Right Nothing)
  sigs -> do
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
            if f /= cpCons (mCore m)
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

commitsAfterSuccess :: Machine -> Pred -> Maybe P.Signature -> [Word'] -> IO Bool
commitsAfterSuccess m predicate signature args = case signature of
  Just sig -> pure (P.sigDet sig == S.Det || P.sigDet sig == S.Semidet)
  Nothing -> do
    let inferred = pInferred predicate
    if P.sigDet inferred /= S.Semidet
      then pure False
      else allM (\i -> if i < length args then isGroundWord (mStore m) (args !! i) else pure False) (P.sigSwitch inferred)
  where
    allM _ [] = pure True
    allM p (x : xs) = do
      ok <- p x
      if ok then allM p xs else pure False

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
  exportTermWith s names next word

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
  let subst = IM.fromList [(i, term) | (i, term) <- bindings, term /= Var i]
      base = initialState fresh
  pure
    base
      { ssStore = (ssStore base) {CLP.stSubst = subst},
        ssOutput = events,
        ssOutLen = count
      }

-- | Export a goal for @call/N@: unbound cells become negative variable ids,
-- which the compiler turns back into cell words.
exportGoal :: Machine -> Word' -> IO Term
exportGoal m w0 = do
  w <- deref s w0
  case tagOf w of
    t | t == tagRef -> pure (Var (negate (valOf w) - 1))
      | t == tagStr -> do
          f <- readCell s (valOf w)
          (name, arity) <- functorName (symbols s) (funId f)
          children <- forM [1 .. arity] $ \i -> readCell s (valOf w + i) >>= exportGoal m
          pure (Compound name children)
      | otherwise -> exportTerm s w
  where
    s = mStore m

showValue :: Term -> String
showValue (StrLit str) = str
showValue t = show t

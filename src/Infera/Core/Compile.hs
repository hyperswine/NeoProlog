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
    Plan (..),
    exprPlan,
    ArithOp (..),
    CmpOp (..),
    Check (..),
    Goal (..),
    Trust (..),
    Pred (..),
    PredRef,
    Clause (..),
    ArgIndex (..),
    DecisionIndex (..),
    Candidates (..),
    candidateList,
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
import qualified Data.Array.IArray as IA
import Data.Array.Base (numElements, unsafeAt)
import Data.Array.Unboxed (UArray)
import Data.IORef
import Data.List (nub)
import Data.Maybe (isJust)
import qualified Data.IntMap.Strict as IM
import qualified Data.IntSet as IS
import qualified Data.Map.Strict as Map
import Infera.Core.Store
import Infera.Error (PredKey, SolveError (..))
import Infera.Infer (joinSort)
import qualified Infera.Program as P
import qualified Infera.Syntax as S
import Infera.Syntax (Term (..))

-- | How a goal argument or head argument is obtained or matched.
data Pattern
  = -- | activation variable, offset from the activation base
    PSlot !Int
  | -- | first occurrence of an activation variable in a clause head: the
    -- cell is still unbound and unreferenced, so matching is a plain write
    PFirst !Int
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

-- | A compiled plan for a common arithmetic shape: a slot or immediate, or
-- one binary operator over two of them with at least one slot. It runs
-- directly on immediate integer words, under the same bounds as the
-- general fast path, and misses on any other operand or result; the
-- general evaluator then decides the outcome. 'PlanNone' marks every other
-- shape. Plans are derived from their 'Expr' by 'exprPlan', so anything
-- that rewrites an expression rebuilds its plan the same way.
data Plan
  = PlanNone
  | PlanImm !Int
  | PlanSlot !Int
  | -- | slot op immediate
    PlanSI !ArithOp !Int !Int
  | -- | immediate op slot
    PlanIS !ArithOp !Int !Int
  | -- | slot op slot
    PlanSS !ArithOp !Int !Int

exprPlan :: Expr -> Plan
exprPlan expr = case expr of
  EImm n -> PlanImm n
  EPat p | Just v <- slotOf p -> PlanSlot v
  EOp op [a, b] | planOp op -> case (a, b) of
    (EPat pa, EImm k) | Just v <- slotOf pa -> PlanSI op v k
    (EImm k, EPat pb) | Just v <- slotOf pb -> PlanIS op k v
    (EPat pa, EPat pb) | Just v <- slotOf pa, Just w <- slotOf pb -> PlanSS op v w
    _ -> PlanNone
  _ -> PlanNone
  where
    slotOf (PSlot v) = Just v
    slotOf (PFirst v) = Just v
    slotOf _ = Nothing
    planOp op = op `elem` [OpPlus, OpMinus, OpMul, OpDiv, OpMod, OpMin, OpMax]

data CmpOp = CmpGt | CmpLt | CmpGte | CmpLte deriving (Eq, Show)

data Check = CkVar | CkNonvar | CkGround | CkInt | CkFloat | CkNum | CkStr | CkAtom | CkChar | CkList
  deriving (Eq, Show)

-- | Predicates are resolved through a reference so that bodies can name
-- predicates compiled later (or recursively) without a runtime map lookup.
type PredRef = IORef Pred

-- | What a call site has proven about a callee's declared contract: the
-- signature alternative the runtime may select without testing groundness,
-- and per argument whether the entry sort check may be skipped.
data Trust = Trust !Int [Bool]

data Goal
  = GCall !PredRef [Pattern] !(Maybe Trust)
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
  | -- | the expression's 'exprPlan' is kept beside it
    GIs Pattern Expr !Plan
  | GCmp !CmpOp Expr Expr !Plan !Plan
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
    -- | Slots not initialized by a first head occurrence. Head construction
    -- initializes its first occurrences in the same left-to-right order as
    -- matching, so allocation need not clear those cells beforehand.
    clInitSlots :: [Int],
    clHead :: [Pattern],
    clBody :: [Goal],
    -- | the clause's result provably satisfies every declared alternative,
    -- so its return check may be skipped
    clTrustReturn :: !Bool
  }

data Key = KAtm !Int | KInt !Int | KChr !Int | KFun !Word' | KBig !Integer | KFlt !Double | KStr !String
  deriving (Eq, Ord, Show)

-- | Selected clause ordinals, ascending. Every index result is built once
-- at compile time, and a singleton is the predicate's shared value for that
-- ordinal, so a call that only looks results up allocates nothing.
data Candidates
  = NoCandidate
  | OneCandidate !Int
  | -- | two or more
    Candidates !(UArray Int Int)

candidateList :: Candidates -> [Int]
candidateList NoCandidate = []
candidateList (OneCandidate i) = [i]
candidateList (Candidates xs) = [unsafeAt xs k | k <- [0 .. numElements xs - 1]]

-- | Per-position clause selection: immediate keys (atom, integer, character
-- and functor words) map to the ascending candidates sharing that key or
-- open at the position; boxed keys go through a value map; an unbound or
-- unknown key yields the open clauses.
data ArgIndex = ArgIndex
  { aiFast :: !(IM.IntMap Candidates),
    aiBoxed :: !(Map.Map Key Candidates),
    aiOpen :: !Candidates,
    -- | some clause has a key at this position
    aiSelective :: !Bool
  }

-- | A bounded, compiled discriminator below an argument's principal
-- functor. Every ancestor is checked before reading a child cell; open
-- head variables remain candidates at every descendant position.
data DecisionIndex = DecisionIndex !Int [Int] !ArgIndex

-- Only a leading comparison between immediate integers can reject a
-- clause here. Unknown values remain on the ordinary execution path,
-- including its instantiation and type errors.
data GuardValue = GuardInt !Int | GuardArg !Int [Int]
data IntGuard = IntGuard !CmpOp !GuardValue !GuardValue

data Pred = Pred
  { pKey :: !PredKey,
    pArity :: !Int,
    pClauses :: !(Array Int Clause),
    pClauseCount :: !Int,
    pIndex :: [ArgIndex],
    pDecisions :: [DecisionIndex],
    -- | the leading immediate-integer guard of each clause, if any
    pIntGuards :: !(Array Int (Maybe IntGuard)),
    pHasGuards :: !Bool,
    -- | every clause, and each ordinal alone
    pAll :: !Candidates,
    pOne :: !(Array Int Candidates),
    pIndexed :: !Bool,
    pDecls :: [P.Signature],
    pInferred :: !P.Signature,
    -- | inferred semidet: the argument positions that must be ground for
    -- the call to commit after its first solution
    pSwitch :: !(Maybe [Int]),
    -- | every clause's return is trusted: calls push no return check
    pTrustReturn :: !Bool
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
    ctxProblems :: IORef [String],
    -- | slots proven ground, with their sort, at this point of the clause
    ctxFacts :: IORef (IM.IntMap S.Sort),
    -- | slots that may already be bound at this point of the clause
    ctxSeen :: IORef IS.IntSet,
    ctxCons :: Word',
    ctxNil :: Word'
  }

-- | Is every term of sort @a@ also of sort @b@?
subSort :: S.Sort -> S.Sort -> Bool
subSort a b = joinSort a b == b

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
  facts <- newIORef IM.empty
  seen <- newIORef IS.empty
  let table = Map.fromList refs
      ctx = Ctx store program table False problems facts seen consW nilW
  forM_ preds $ \p -> do
    compiled <- compilePred ctx p
    writeIORef (table Map.! P.predKey p) compiled
  writeIORef facts IM.empty
  writeIORef seen IS.empty
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
  compiledClauses <- mapM (compileClause ctx (P.predDecls p)) clauses
  let count = length compiledClauses
  let ones = listArray (0, max 0 (count - 1)) (map OneCandidate [0 .. count - 1])
      shared = toCandidates ones
  index <- mapM (\i -> buildIndex (ctxStore ctx) shared i compiledClauses) [0 .. arity - 1]
  let paths = take (if count > 1 then 32 else 0) . nub $
        [(i, path) | clause <- compiledClauses, (i, pattern) <- zip [0 ..] (clHead clause),
          path <- nestedPaths 3 pattern]
  decisions <- forM paths $ \(i, path) -> do
    decision <- buildIndexAt (ctxStore ctx) shared i path compiledClauses
    pure (DecisionIndex i path decision)
  let guards = map leadingIntGuard compiledClauses
  pure
    Pred
      { pKey = P.predKey p,
        pArity = arity,
        pClauses = listArray (0, max 0 (count - 1)) compiledClauses,
        pClauseCount = count,
        pIndex = index,
        pDecisions = [decision | decision@(DecisionIndex _ _ idx) <- decisions, aiSelective idx],
        pIntGuards = listArray (0, max 0 (count - 1)) (if null guards then [Nothing] else guards),
        pHasGuards = any isJust guards,
        pAll = shared [0 .. count - 1],
        pOne = ones,
        pIndexed = P.predIsIndexed (ctxProgram ctx) p,
        pDecls = P.predDecls p,
        pInferred = P.predInferred p,
        pSwitch =
          if P.sigDet (P.predInferred p) == S.Semidet
            then Just (filter (< arity) (P.sigSwitch (P.predInferred p)))
            else Nothing,
        pTrustReturn = not (null (P.predDecls p)) && all clTrustReturn compiledClauses
      }

-- | Ascending ordinals as a selection result, sharing the singletons.
toCandidates :: Array Int Candidates -> [Int] -> Candidates
toCandidates _ [] = NoCandidate
toCandidates ones [i] = ones `unsafeAt` i
toCandidates _ xs = Candidates (IA.listArray (0, length xs - 1) xs)

buildIndex :: Store -> ([Int] -> Candidates) -> Int -> [Clause] -> IO ArgIndex
buildIndex store shared position = buildIndexAt store shared position []

buildIndexAt :: Store -> ([Int] -> Candidates) -> Int -> [Int] -> [Clause] -> IO ArgIndex
buildIndexAt store shared position path clauses = do
  keyed <- forM (zip [0 ..] clauses) $ \(ordinal, clause) -> do
    key <- case patternAtPath (position : path) (clHead clause) of
      Just pattern -> patternKey store pattern
      Nothing -> pure Nothing
    pure (ordinal :: Int, key)
  let open = IS.fromList [ordinal | (ordinal, Nothing) <- keyed]
      grouped = Map.fromListWith IS.union [(key, IS.singleton ordinal) | (ordinal, Just key) <- keyed]
      withOpen members = shared (IS.toAscList (IS.union members open))
      fast = IM.fromList [(w, withOpen members) | (key, members) <- Map.toList grouped, Just w <- [immediateKey key]]
      boxedKeys = Map.fromList [(key, withOpen members) | (key, members) <- Map.toList grouped, immediateKey key == Nothing]
  pure (ArgIndex fast boxedKeys (shared (IS.toAscList open)) (not (Map.null grouped)))

patternAtPath :: [Int] -> [Pattern] -> Maybe Pattern
patternAtPath [] _ = Nothing
patternAtPath (i : path) patterns = case drop i patterns of
  pattern : _ -> case path of
    [] -> Just pattern
    _ -> case pattern of
      PStruct _ children -> patternAtPath path children
      PArith _ _ children -> patternAtPath path children
      _ -> Nothing
  [] -> Nothing

nestedPaths :: Int -> Pattern -> [[Int]]
nestedPaths depth pattern
  | depth <= 0 = []
  | otherwise = case pattern of
      PStruct _ children -> descend children
      PArith _ _ children -> descend children
      _ -> []
  where
    descend children = concat
      [[ [i] | discriminates child ] ++ map (i :) (nestedPaths (depth - 1) child)
        | (i, child) <- zip [0 ..] children]
    discriminates (PWord _) = True
    discriminates (PStruct _ _) = True
    discriminates (PArith _ _ _) = True
    discriminates _ = False

leadingIntGuard :: Clause -> Maybe IntGuard
leadingIntGuard clause = case clBody clause of
  GCmp op a b _ _ : _ -> IntGuard op <$> value a <*> value b
  _ -> Nothing
  where
    slots = IM.fromListWith (\_ first -> first)
      [(v, (i, path)) | (i, pattern) <- zip [0 ..] (clHead clause), (v, path) <- slotPaths [] pattern]
    value (EImm n) = Just (GuardInt n)
    value (EPat (PSlot v)) = slotValue v
    value (EPat (PFirst v)) = slotValue v
    value _ = Nothing
    slotValue v = case IM.lookup v slots of
      Just (i, path) | length path <= 3 -> Just (GuardArg i path)
      _ -> Nothing
    slotPaths path pattern = case pattern of
      PSlot v -> [(v, path)]
      PFirst v -> [(v, path)]
      PStruct _ children -> concat [slotPaths (path ++ [i]) child | (i, child) <- zip [0 ..] children]
      PArith _ _ children -> concat [slotPaths (path ++ [i]) child | (i, child) <- zip [0 ..] children]
      PWord _ -> []

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
  PFirst _ -> pure Nothing
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
        pure $ case value of
          BInt n -> Just (KBig n)
          BFlt d | isNaN d -> Nothing
          BFlt d -> Just (KFlt d)
          BStr s -> Just (KStr s)
    | otherwise -> pure Nothing

-- | Intersect the useful principal keys in clause order, then refine with
-- bounded constructor decisions and a leading immediate-integer guard.
-- Refinement makes no bindings and never evaluates an expression. It is
-- disabled while a constraint store is active: head bindings may wake a
-- constraint before a later head mismatch or failed guard is reached.
--
-- Index results are precomputed and shared; only an intersection or guard
-- filter leaving two or more clauses, neither of its inputs, builds a new
-- result, and a boxed key allocates its lookup key.
candidateClauses :: Store -> Pred -> IO Candidates
candidateClauses !store p
  | not (pIndexed p) = pure (pAll p)
  | otherwise = do
      constrained <- readReg store rCLP
      if constrained /= 0
        then principalKeys store p False (pIndex p) 0 (pAll p)
        else
          if pClauseCount p <= 1
            -- A pure single candidate is tried directly: its head performs
            -- every check an index could, and a mismatch binds nothing
            -- that survives the failure.
            then pure (pAll p)
            else do
              selected <- principalKeys store p True (pIndex p) 0 (pAll p)
              case selected of
                Candidates _ -> do
                  refined <- decisionKeys store p (pDecisions p) selected
                  if pHasGuards p then keepGuards store p refined else pure refined
                _ -> pure selected

-- The selection steps are top-level functions: local ones closing over the
-- store and predicate would be allocated on every call.

-- | Once only one pure candidate remains, ordinary head/body execution
-- performs all remaining checks without allocating another alternative.
-- Constraints retain every principal decision: skipped head bindings can
-- otherwise change whether an error is exposed.
principalKeys :: Store -> Pred -> Bool -> [ArgIndex] -> Int -> Candidates -> IO Candidates
principalKeys _ _ _ [] !_ selected = pure selected
principalKeys store p pureCall (index : rest) !i selected
  | not (aiSelective index) = principalKeys store p pureCall rest (i + 1) selected
  | otherwise = do
      w <- readArg store i >>= deref store
      if tagOf w == tagRef
        then principalKeys store p pureCall rest (i + 1) selected
        else
          if tagOf w == tagBox
            then do
              restricted <- lookupBoxed store index w
              case restricted of
                Nothing -> principalKeys store p pureCall rest (i + 1) selected
                Just candidates -> choose candidates
            else lookupImmediate store index w >>= choose
  where
    choose !candidates = case intersectCandidates p selected candidates of
      NoCandidate -> pure NoCandidate
      narrowed@(OneCandidate _) | pureCall -> pure narrowed
      narrowed -> principalKeys store p pureCall rest (i + 1) narrowed

-- | Bounded constructor decisions below the principal functors.
decisionKeys :: Store -> Pred -> [DecisionIndex] -> Candidates -> IO Candidates
decisionKeys _ _ _ NoCandidate = pure NoCandidate
decisionKeys _ _ _ only@(OneCandidate _) = pure only
decisionKeys _ _ [] selected = pure selected
decisionKeys store p (DecisionIndex i path index : rest) selected = do
  found <- argumentAtPath store i path
  if tagOf found == tagRef
    then decisionKeys store p rest selected
    else
      if tagOf found == tagBox
        then do
          restricted <- lookupBoxed store index found
          let !narrowed = maybe selected (intersectCandidates p selected) restricted
          decisionKeys store p rest narrowed
        else do
          restricted <- lookupImmediate store index found
          let !narrowed = intersectCandidates p selected restricted
          decisionKeys store p rest narrowed

-- | A boxed key's candidates. NaN has no lawful ordered-map key: preserve
-- the ordinary unification path for it instead of making an index decision.
lookupBoxed :: Store -> ArgIndex -> Word' -> IO (Maybe Candidates)
lookupBoxed store index w = do
  key <- keyOfWord store w
  pure $ case key of
    Just (KFlt d) | isNaN d -> Nothing
    Just k -> Just (Map.findWithDefault (aiOpen index) k (aiBoxed index))
    Nothing -> Nothing

-- | An immediate or functor key's candidates: a precomputed shared value.
lookupImmediate :: Store -> ArgIndex -> Word' -> IO Candidates
lookupImmediate store index w
  | tagOf w == tagStr = do
      f <- readCell store (valOf w)
      pure $! IM.findWithDefault (aiOpen index) (funKey f) (aiFast index)
  | otherwise = pure $! IM.findWithDefault (aiOpen index) w (aiFast index)
{-# INLINE lookupImmediate #-}

-- | Drop the candidates whose leading integer guard is known to fail. A
-- result equal to the input, empty or single is not rebuilt.
keepGuards :: Store -> Pred -> Candidates -> IO Candidates
keepGuards _ _ NoCandidate = pure NoCandidate
keepGuards store p only@(OneCandidate ordinal) = do
  ok <- guardHolds store p ordinal
  pure $! if ok then only else NoCandidate
keepGuards store p selected@(Candidates ordinals) = do
  let n = numElements ordinals
      -- survivors, and the first one
      count !k !kept !first
        | k >= n = finish kept first
        | otherwise = do
            let ordinal = ordinals `unsafeAt` k
            ok <- guardHolds store p ordinal
            if ok
              then count (k + 1) (kept + 1) (if kept == 0 then ordinal else first)
              else count (k + 1) kept first
      finish kept first
        | kept == n = pure selected
        | kept == 0 = pure NoCandidate
        | kept == 1 = pure $! pOne p `unsafeAt` first
        | otherwise = do
            survivors <- filterOrdinals [unsafeAt ordinals k | k <- [0 .. n - 1]]
            pure (Candidates (IA.listArray (0, kept - 1) survivors))
  count 0 (0 :: Int) (0 :: Int)
  where
    filterOrdinals [] = pure []
    filterOrdinals (ordinal : rest) = do
      ok <- guardHolds store p ordinal
      if ok then (ordinal :) <$> filterOrdinals rest else filterOrdinals rest

guardHolds :: Store -> Pred -> Int -> IO Bool
guardHolds store p ordinal = case pIntGuards p `unsafeAt` ordinal of
  Nothing -> pure True
  Just (IntGuard op a b) -> do
    left <- guardWord a
    right <- guardWord b
    pure $!
      if tagOf left /= tagInt || tagOf right /= tagInt
        then True
        else
          let x = valOf left
              y = valOf right
           in case op of
                CmpGt -> x > y
                CmpLt -> x < y
                CmpGte -> x >= y
                CmpLte -> x <= y
  where
    guardWord (GuardInt n) = pure (intWord n)
    guardWord (GuardArg i path) = argumentAtPath store i path

-- | The intersection of two ascending selections. An input equal to the
-- result is returned itself, and a singleton is the shared one, so only a
-- strictly smaller intersection of two or more allocates.
intersectCandidates :: Pred -> Candidates -> Candidates -> Candidates
-- Every selection is a subset of all clauses, the first key's starting point.
intersectCandidates p (Candidates xs) right | numElements xs == pClauseCount p = right
intersectCandidates _ NoCandidate _ = NoCandidate
intersectCandidates _ _ NoCandidate = NoCandidate
intersectCandidates _ left@(OneCandidate x) right = if memberCandidates x right then left else NoCandidate
intersectCandidates _ left right@(OneCandidate y) = if memberCandidates y left then right else NoCandidate
intersectCandidates p left@(Candidates xs) right@(Candidates ys)
  | ny == pClauseCount p = left
  | kept == ny = right
  | kept == nx = left
  | kept == 0 = NoCandidate
  | kept == 1 = pOne p `unsafeAt` first
  | otherwise = Candidates (IA.listArray (0, kept - 1) (common 0 0))
  where
    nx = numElements xs
    ny = numElements ys
    (kept, first) = count 0 0 0 0
    count :: Int -> Int -> Int -> Int -> (Int, Int)
    count !i !j !c !f
      | i >= nx || j >= ny = (c, f)
      | otherwise =
          let x = xs `unsafeAt` i
              y = ys `unsafeAt` j
           in case compare x y of
                LT -> count (i + 1) j c f
                GT -> count i (j + 1) c f
                EQ -> count (i + 1) (j + 1) (c + 1) (if c == 0 then x else f)
    common !i !j
      | i >= nx || j >= ny = []
      | otherwise =
          let x = xs `unsafeAt` i
              y = ys `unsafeAt` j
           in case compare x y of
                LT -> common (i + 1) j
                GT -> common i (j + 1)
                EQ -> x : common (i + 1) (j + 1)

memberCandidates :: Int -> Candidates -> Bool
memberCandidates _ NoCandidate = False
memberCandidates x (OneCandidate y) = x == y
memberCandidates x (Candidates ys) = go 0
  where
    n = numElements ys
    go !k
      | k >= n = False
      | otherwise = case compare (ys `unsafeAt` k) x of
          LT -> go (k + 1)
          EQ -> True
          GT -> False

-- | Read at most the compiled path length. An unbound ancestor, a constant
-- or a different constructor arity cannot provide a child discriminator;
-- such a path reads as an unbound word, which no index or guard decides.
-- No recursive walk of runtime data occurs, including for cyclic data.
argumentAtPath :: Store -> Int -> [Int] -> IO Word'
argumentAtPath store position path = readArg store position >>= descend path
  where
    descend [] word = deref store word
    descend (i : rest) word = do
      current <- deref store word
      if tagOf current /= tagStr
        then pure (refWord 0)
        else do
          functor <- readCell store (valOf current)
          if i >= funArity functor
            then pure (refWord 0)
            else readCell store (valOf current + i + 1) >>= descend rest

compileClause :: Ctx -> [P.Signature] -> S.Clause -> IO Clause
compileClause ctx sigs clause = do
  seen <- newIORef IS.empty
  headPatterns <- case S.clauseHead clause of
    Compound _ as -> mapM (compileHeadArg ctx seen) as
    _ -> pure []
  -- Facts that hold under every declared alternative at clause entry.
  writeIORef (ctxFacts ctx) IM.empty
  readIORef seen >>= writeIORef (ctxSeen ctx)
  forM_ (zip [0 ..] headPatterns) $ \(i, pattern) ->
    case entryFact sigs i of
      Just sort -> assumePattern ctx pattern sort
      Nothing -> pure ()
  body <- compileBody ctx (S.clauseBody clause)
  trusted <-
    if null sigs
      then pure False
      else do
        facts <- readIORef (ctxFacts ctx)
        proven <- mapM (patternSort ctx facts) headPatterns
        pure (and [maybe False (\sort -> all (\sig -> subSort sort (argSort sig i)) sigs) p | (i, p) <- zip [0 ..] proven])
  let count = max 1 (S.clauseNVars clause)
      headWrites = IS.fromList (concatMap firstSlots headPatterns)
      initialize = filter (`IS.notMember` headWrites) [0 .. count - 1]
  pure (Clause count initialize headPatterns body trusted)
  where
    firstSlots pattern = case pattern of
      PFirst offset -> [offset]
      PStruct _ children -> concatMap firstSlots children
      PArith _ _ children -> concatMap firstSlots children
      _ -> []

argSort :: P.Signature -> Int -> S.Sort
argSort sig i = case drop i (P.sigArgs sig) of
  S.ArgSpec sort _ : _ -> sort
  [] -> S.SAny

argMode :: P.Signature -> Int -> S.Mode
argMode sig i = case drop i (P.sigArgs sig) of
  S.ArgSpec _ mode : _ -> mode
  [] -> S.ModeInOut

-- | The sort an argument is known to have, ground, at clause entry: it is
-- an input in every declared alternative, with the join of their sorts.
entryFact :: [P.Signature] -> Int -> Maybe S.Sort
entryFact [] _ = Nothing
entryFact sigs i
  | all (\sig -> argMode sig i == S.ModeIn) sigs = Just (foldr (joinSort . (`argSort` i)) S.SNone sigs)
  | otherwise = Nothing

-- | The sort a callee's argument is known to have, ground, after the call:
-- an output in every alternative, with the join of their sorts.
outputFact :: [P.Signature] -> Int -> Maybe S.Sort
outputFact [] _ = Nothing
outputFact sigs i
  | all (\sig -> argMode sig i == S.ModeOut) sigs = Just (foldr (joinSort . (`argSort` i)) S.SNone sigs)
  | otherwise = Nothing

-- | Record that a pattern is ground with the given sort: variables get the
-- fact, list cells distribute it to head and tail.
assumePattern :: Ctx -> Pattern -> S.Sort -> IO ()
assumePattern ctx pattern sort = case pattern of
  PSlot v -> modifyIORef' (ctxFacts ctx) (IM.insertWith (\_ old -> old) v sort)
  PFirst v -> modifyIORef' (ctxFacts ctx) (IM.insertWith (\_ old -> old) v sort)
  PWord _ -> pure ()
  PStruct f [h, t]
    | f == ctxCons ctx -> case sort of
        S.SList element -> assumePattern ctx h element >> assumePattern ctx t sort
        _ -> assumePattern ctx h S.SAny >> assumePattern ctx t S.SAny
  PStruct _ children -> mapM_ (\c -> assumePattern ctx c S.SAny) children
  PArith _ _ children -> mapM_ (\c -> assumePattern ctx c S.SNum) children

-- | The sort of a pattern that is provably ground under the facts.
patternSort :: Ctx -> IM.IntMap S.Sort -> Pattern -> IO (Maybe S.Sort)
patternSort ctx facts pattern = case pattern of
  PSlot v -> pure (IM.lookup v facts)
  PFirst v -> pure (IM.lookup v facts)
  PWord w -> Just <$> constantSort ctx w
  PStruct f [h, t]
    | f == ctxCons ctx -> do
        sh <- patternSort ctx facts h
        st <- patternSort ctx facts t
        pure $ case (sh, st) of
          (Just a, Just (S.SList b)) -> Just (S.SList (joinSort a b))
          (Just _, Just _) -> Just S.SAny
          _ -> Nothing
  PStruct _ children -> do
    sorts <- mapM (patternSort ctx facts) children
    pure (if all (/= Nothing) sorts then Just S.SAny else Nothing)
  PArith _ _ children -> do
    sorts <- mapM (patternSort ctx facts) children
    pure $ if any (== Nothing) sorts then Nothing
      else Just (if all (== Just S.SInt) sorts then S.SInt else S.SNum)

constantSort :: Ctx -> Word' -> IO S.Sort
constantSort ctx w
  | w == ctxNil ctx = pure (S.SList S.SNone)
  | otherwise = case tagOf w of
      t | t == tagInt -> pure S.SInt
        | t == tagAtm -> pure S.SAtom
        | t == tagChr -> pure S.SChar
        | t == tagBox -> do
            value <- boxed (ctxStore ctx) w
            pure $ case value of
              BInt _ -> S.SInt
              BFlt _ -> S.SFloat
              BStr _ -> S.SStr
        | otherwise -> pure S.SAny

exprSort :: IM.IntMap S.Sort -> Expr -> S.Sort
exprSort facts expr = case expr of
  EImm _ -> S.SInt
  EBig _ -> S.SInt
  EFlt _ -> S.SFloat
  EPat (PSlot v) -> maybe S.SNum numeric (IM.lookup v facts)
  EPat (PFirst v) -> maybe S.SNum numeric (IM.lookup v facts)
  EPat _ -> S.SNum
  EOp _ operands -> if all ((== S.SInt) . exprSort facts) operands then S.SInt else S.SNum
  where
    numeric S.SInt = S.SInt
    numeric S.SFloat = S.SFloat
    numeric _ = S.SNum

-- | Facts and seen slots are saved around sub-bodies: nothing established
-- inside a branch holds after it, while anything bound inside may be bound.
isolated :: Ctx -> IO a -> IO a
isolated ctx action = do
  facts <- readIORef (ctxFacts ctx)
  result <- action
  writeIORef (ctxFacts ctx) facts
  pure result

noteSlot :: Ctx -> Pattern -> IO ()
noteSlot ctx pattern = case pattern of
  PSlot v -> modifyIORef' (ctxSeen ctx) (IS.insert v)
  PFirst v -> modifyIORef' (ctxSeen ctx) (IS.insert v)
  PStruct _ children -> mapM_ (noteSlot ctx) children
  PArith _ _ children -> mapM_ (noteSlot ctx) children
  PWord _ -> pure ()

compileHeadArg :: Ctx -> IORef IS.IntSet -> Term -> IO Pattern
compileHeadArg ctx seen term = case term of
  Var v -> do
    known <- readIORef seen
    if IS.member v known
      then pure (PSlot v)
      else modifyIORef' seen (IS.insert v) >> pure (PFirst v)
  Compound f as -> do
    fid <- internFunctor (symbols (ctxStore ctx)) f (length as)
    PStruct (funWord fid (length as)) <$> mapM (compileHeadArg ctx seen) as
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
compileArg ctx term = do
  pattern <- compileArg' ctx term
  noteSlot ctx pattern
  pure pattern

compileArg' :: Ctx -> Term -> IO Pattern
compileArg' ctx term = case term of
  Var v -> pure (PSlot v)
  Compound f as -> do
    fid <- internFunctor (symbols (ctxStore ctx)) f (length as)
    args <- mapM (compileArg' ctx) as
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
  Compound ";" [Compound "->" [c, t], e] -> isolated ctx (GIf <$> body c <*> body t <*> (Just <$> body e))
  Compound ";" [a, b] -> isolated ctx (GOr <$> body a <*> body b)
  Compound "->" [c, t] -> isolated ctx (GIf <$> body c <*> body t <*> pure Nothing)
  Compound "not" [g] -> isolated ctx (GNot <$> body g)
  Compound "once" [g] -> isolated ctx (GOnce <$> body g)
  Compound "forall" [c, a] -> isolated ctx $ do
    cg <- body c
    ag <- body a
    pure (GNot (cg ++ [GNot ag]))
  Compound "findall" [tmpl, g, l] -> GFindAll <$> arg tmpl <*> isolated ctx (body g) <*> arg l
  Compound "call" (p : args) -> GCallDyn False <$> arg p <*> mapM arg args
  Compound "unify" [a, b] -> do
    pa <- arg a
    pb <- arg b
    facts <- readIORef (ctxFacts ctx)
    sb <- patternSort ctx facts pb
    sa <- patternSort ctx facts pa
    forM_ sb (assumePattern ctx pa)
    forM_ sa (assumePattern ctx pb)
    pure (GUnify pa pb)
  Compound "equiv" [a, b] -> GEquiv <$> arg a <*> arg b
  Compound "neq" [a, b] -> GNeq <$> arg a <*> arg b
  Compound "is" [a, b] -> do
    pa <- arg a
    expr <- compileExpr ctx b
    facts <- readIORef (ctxFacts ctx)
    assumePattern ctx pa (exprSort facts expr)
    pure (GIs pa expr (exprPlan expr))
  Compound "gt" [a, b] -> comparison CmpGt a b
  Compound "lt" [a, b] -> comparison CmpLt a b
  Compound "gte" [a, b] -> comparison CmpGte a b
  Compound "lte" [a, b] -> comparison CmpLte a b
  Compound "var" [x] -> GCheck CkVar <$> arg x
  Compound "nonvar" [x] -> GCheck CkNonvar <$> arg x
  Compound "ground" [x] -> checked CkGround S.SAny x
  Compound "is_int" [x] -> checked CkInt S.SInt x
  Compound "is_float" [x] -> checked CkFloat S.SFloat x
  Compound "is_num" [x] -> checked CkNum S.SNum x
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
  Compound "minimize" [cost, g] -> GMinimize <$> arg cost <*> isolated ctx (body g)
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
    checked check sort x = do
      px <- arg x
      assumePattern ctx px sort
      pure (GCheck check px)
    comparison op a b = do
      ea <- compileExpr ctx a
      eb <- compileExpr ctx b
      pure (GCmp op ea eb (exprPlan ea) (exprPlan eb))
    unsupported what = do
      if ctxDynamic ctx then pure () else modifyIORef' (ctxProblems ctx) (what :)
      pure (GUnsupported term)
    userCall f as = case Map.lookup (f, length as) (ctxPreds ctx) of
      Just ref
        | Just p <- P.lookupPred (f, length as) (ctxProgram ctx), P.predIsTabled (ctxProgram ctx) p ->
            GTabled ref <$> mapM arg as
        | otherwise -> do
            let sigs = maybe [] P.predDecls (P.lookupPred (f, length as) (ctxProgram ctx))
            seenBefore <- readIORef (ctxSeen ctx)
            patterns <- mapM arg as
            facts <- readIORef (ctxFacts ctx)
            sorts <- mapM (patternSort ctx facts) patterns
            let fresh pattern = case pattern of
                  PSlot v -> not (IS.member v seenBefore)
                  _ -> False
                selectable sig = and [maybe False (const True) sort | (i, sort) <- zip [0 :: Int ..] sorts, argMode sig i == S.ModeIn]
                trust = case [k | (k, sig) <- zip [0 ..] sigs, selectable sig] of
                  (k : _) ->
                    let sig = sigs !! k
                     in Just (Trust k [maybe (fresh pattern) (\sort -> subSort sort (argSort sig i)) msort
                                      | (i, pattern, msort) <- zip3 [0 ..] patterns sorts])
                  [] -> Nothing
            -- The callee's verified or proven contract gives its outputs.
            forM_ (zip [0 ..] patterns) $ \(i, pattern) -> forM_ (outputFact sigs i) (assumePattern ctx pattern)
            pure (GCall ref patterns trust)
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
  facts <- newIORef IM.empty
  seen <- newIORef IS.empty
  nilW <- atmWord <$> internAtom (symbols store) "nil"
  consW <- (\f -> funWord f 2) <$> internFunctor (symbols store) "cons" 2
  compileGoal (Ctx store program preds True problems facts seen consW nilW) term

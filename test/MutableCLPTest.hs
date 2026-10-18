{-# LANGUAGE OverloadedStrings #-}

module MutableCLPTest (mutableCLPGroup) where

import Control.Exception (evaluate)
import Control.Monad (foldM, forM, forM_)
import qualified Data.IntMap.Strict as IM
import Data.List (nub, sort)
import qualified Data.Set as Set
import Hedgehog hiding (Var)
import qualified Hedgehog.Gen as Gen
import qualified Hedgehog.Range as Range
import Infera hiding (Answer, Domain, solveQuery)
import qualified Infera.CLP as P
import qualified Infera.CLP.Mutable as M
import qualified Infera.Core.Run as Run
import qualified Infera.Engine.Reference as Reference
import qualified Infera.Unify as Unify
import System.Timeout (timeout)

-- The pure store is the compatibility oracle, including constraint IDs,
-- dependency entries, pending work and residual order, rather than just its
-- visible domains. Separate exhaustive models below check its solution sets.
data Operation
  = Domain Term P.Bound P.Bound
  | Domains [Term] P.Bound P.Bound
  | Relation P.Rel Term Term
  | Diseq Term Term
  | Different [Term]
  | Reified P.Rel Term Term Term
  | Unify Term Term
  | Bind VarId Integer
  | External Term Term
  | Propagate
  deriving Show

data TraceCommand = Apply Operation | Save | Restore | RestoreEntry | Forget
  deriving Show

type Checked = Either SolveError (Maybe P.Store)

persistent :: Operation -> P.Store -> Checked
persistent operation store = case operation of
  Domain term lo hi -> P.addDomain term lo hi store
  Domains terms lo hi -> P.addDomains terms lo hi store
  Relation rel lhs rhs -> P.addRelation rel lhs rhs store
  Diseq lhs rhs -> P.addDiseq lhs rhs store
  Different terms -> P.addAllDifferent terms store
  Reified rel lhs rhs truth -> P.addReified rel lhs rhs truth store
  Unify lhs rhs -> P.storeUnify store lhs rhs
  Bind variable value -> P.storeBind store variable value
  External lhs rhs -> case externalWrites store lhs rhs of
    Nothing -> Right Nothing
    Just writes -> P.applyBindings writes store
  Propagate -> P.propagate store

-- External writes obey the real API's precondition: they come from a valid
-- occurs-checked unification, and contain its actual writes only.
externalWrites :: P.Store -> Term -> Term -> Maybe [(VarId, Term)]
externalWrites store lhs rhs = do
  (substitution, changed) <- Unify.unify (P.stSubst store) lhs rhs
  pure [(variable, substitution IM.! variable) | variable <- changed]

mutable :: M.MutableStore -> P.Store -> Operation -> IO (Either SolveError Bool)
mutable store before operation = case operation of
  Domain term lo hi -> M.addDomain store term lo hi
  Domains terms lo hi -> M.addDomains store terms lo hi
  Relation rel lhs rhs -> M.addRelation store rel lhs rhs
  Diseq lhs rhs -> M.addDiseq store lhs rhs
  Different terms -> M.addAllDifferent store terms
  Reified rel lhs rhs truth -> M.addReified store rel lhs rhs truth
  Unify lhs rhs -> M.storeUnify store lhs rhs
  Bind variable value -> M.storeBind store variable value
  External lhs rhs -> case externalWrites before lhs rhs of
    Nothing -> pure (Right False)
    Just writes -> M.applyBindings store writes
  Propagate -> M.propagate store

applyChecked :: M.MutableStore -> P.Store -> Operation -> PropertyT IO (P.Store, Bool)
applyChecked store before operation = do
  annotateShow operation
  let expected = persistent operation before
  actual <- evalIO (mutable store before operation)
  actual === fmap (maybe False (const True)) expected
  frozen <- evalIO (M.freeze store)
  let after = case expected of Right (Just value) -> value; _ -> before
  frozen === after
  pure (after, actual == Right True)

variable :: Gen Term
variable = Var <$> Gen.int (Range.linear 0 5)

smallInteger :: Gen Integer
smallInteger = Gen.integral (Range.linear (-4) 5)

term :: Gen Term
term = Gen.frequency
  [ (6, variable), (3, IntLit <$> smallInteger),
    (1, pure (Atom "bad")),
    (1, Compound "box" . (: []) <$> variable),
    (1, Compound "pair" <$> Gen.list (Range.singleton 2) variable)
  ]

expression :: Gen Term
expression = Gen.frequency
  [ (4, variable), (2, IntLit <$> smallInteger),
    (3, do coefficient <- smallInteger; v <- variable
           offset <- smallInteger
           pure (Compound "plus" [Compound "mul" [IntLit coefficient, v], IntLit offset])),
    (1, Compound "mul" <$> Gen.list (Range.singleton 2) variable),
    (1, Compound "abs" . (: []) <$> variable),
    (1, pure (Compound "div" [IntLit 1, Var 0]))
  ]

relation :: Gen P.Rel
relation = Gen.element [P.RelEq, P.RelNe, P.RelLe]

operation :: Gen Operation
operation = Gen.frequency
  [ (5, do lo <- smallInteger; width <- Gen.integral (Range.linear (-1) 5)
           Domain <$> term <*> pure (P.Fin lo) <*> pure (P.Fin (lo + width))),
    (3, do lo <- smallInteger; width <- Gen.integral (Range.linear 0 5)
           Domains <$> Gen.list (Range.linear 0 5) term <*> pure (P.Fin lo) <*> pure (P.Fin (lo + width))),
    (6, Relation <$> relation <*> expression <*> expression),
    (3, Diseq <$> term <*> term),
    (2, Different <$> Gen.list (Range.linear 0 4) term),
    (2, Reified <$> relation <*> expression <*> expression <*> term),
    (4, Unify <$> term <*> term),
    (4, Bind <$> Gen.int (Range.linear 0 5) <*> smallInteger),
    (3, External <$> term <*> term),
    (1, pure Propagate)
  ]

prop_generated_traces :: Property
prop_generated_traces = withTests 150 . property $ do
  commands <- forAll $ Gen.list (Range.linear 25 90) $ Gen.frequency
    [(12, Apply <$> operation), (3, pure Save), (2, pure Restore),
     (1, pure RestoreEntry), (1, pure Forget)]
  store <- evalIO (M.new P.emptyStore)
  entry <- evalIO (M.mark store)
  let go current _ [] = pure current
      go current saved (command : rest) = do
        annotateShow command
        case command of
          Apply next -> do
            (after, _) <- applyChecked store current next
            go after saved rest
          Save -> do
            checkpoint <- evalIO (M.mark store)
            go current ((checkpoint, current) : saved) rest
          Restore -> case saved of
            [] -> go current saved rest
            (checkpoint, snapshot) : _ -> do
              evalIO (M.rollback store checkpoint)
              frozen <- evalIO (M.freeze store)
              frozen === snapshot
              -- Reuse the same mark after subsequent writes, as alternative
              -- retries do; descendant marks have been discarded already.
              go snapshot saved rest
          RestoreEntry -> do
            evalIO (M.rollback store entry)
            frozen <- evalIO (M.freeze store)
            frozen === P.emptyStore
            go P.emptyStore [] rest
          Forget -> go current (drop 1 saved) rest
  _ <- go P.emptyStore [] commands
  evalIO (M.rollback store entry)
  frozen <- evalIO (M.freeze store)
  frozen === P.emptyStore

holds :: P.Rel -> Integer -> Integer -> Bool
holds P.RelEq = (==)
holds P.RelNe = (/=)
holds P.RelLe = (<=)

prop_finite_models :: Property
prop_finite_models = withTests 100 . property $ do
  upper <- forAll (Gen.integral (Range.linear 0 3))
  a <- forAll (Gen.integral (Range.linear (-2) 2))
  b <- forAll (Gen.integral (Range.linear (-2) 2))
  offset <- forAll smallInteger
  rel <- forAll relation
  different <- forAll Gen.bool
  alias <- forAll Gen.bool
  let lhs = Compound "plus" [Compound "mul" [IntLit a, Var 0], Compound "mul" [IntLit b, Var 1]]
      rhs = Compound "plus" [Var 2, IntLit offset]
      operations =
        [Domains [Var 0, Var 1, Var 2] (P.Fin 0) (P.Fin upper),
         Domain (Var 3) (P.Fin 0) (P.Fin 1), Relation rel lhs rhs,
         Reified P.RelEq (Compound "mul" [Var 0, Var 1]) (Var 2) (Var 3)] ++
        [Different [Var 0, Var 1, Var 2] | different] ++
        [External (Var 0) (Var 1) | alias]
      assignments = [[x, y, z, truth] | x <- [0 .. upper], y <- [0 .. upper],
        z <- [0 .. upper], truth <- [0, 1]]
      model = [values | values@[x, y, z, truth] <- assignments,
        holds rel (a * x + b * y) (z + offset),
        truth == if x * y == z then 1 else 0,
        not different || length (nub [x, y, z]) == 3,
        not alias || x == y]
  store <- evalIO (M.new P.emptyStore)
  let applyAlive (current, False) _ = pure (current, False)
      applyAlive (current, True) next = applyChecked store current next
  (base, alive) <- foldM applyAlive (P.emptyStore, True) operations
  checkpoint <- evalIO (M.mark store)
  actual <- if not alive then pure [] else fmap concat $ forM assignments $ \values -> do
    (after, succeeds) <- foldM applyAlive (base, True)
      [Bind index value | (index, value) <- zip [0 ..] values]
    whenSuccessful succeeds $ forM_ (zip [0 ..] values) $ \(index, value) ->
      P.storeWalk after (Var index) === IntLit value
    evalIO (M.rollback store checkpoint)
    frozen <- evalIO (M.freeze store)
    frozen === base
    pure [values | succeeds]
  classify "no satisfying assignments" (null model)
  classify "aliases" alias
  classify "all different" different
  sort actual === sort model
  where
    whenSuccessful True action = action
    whenSuccessful False _ = pure ()

prop_atomic_boundaries :: Property
prop_atomic_boundaries = withTests 1 . property $ do
  let reciprocal = Compound "div" [IntLit 1,
        Compound "mul" [Var 0, Compound "minus" [Var 0, IntLit 1]]]
      large = 999999999999999999999999999999999999999
      scenarios =
        [ [Domains [Var 0, Var 1] (P.Fin 0) (P.Fin 3),
           Domains [Var 0, Atom "bad"] (P.Fin 1) (P.Fin 2)],
          [Domains [IntLit 0, Atom "bad"] (P.Fin 1) (P.Fin 2)],
          [Domain (Var 0) (P.Fin 0) (P.Fin 2), Relation P.RelEq (Var 1) reciprocal,
           Bind 0 0, Bind 0 1, Bind 0 2],
          [Relation P.RelEq (Var 1) (Compound "plus" [Var 0, IntLit 1]),
           Domains [Var 0, Atom "bad"] (P.Fin 0) (P.Fin 3), Bind 0 2],
          [Domain (Var 1) (P.Fin large) (P.Fin (large + 3)),
           External (Var 1) (Var 0), Bind 0 (large + 1)],
          [Different [Var 0, Var 1, Var 2], Domains [Var 0, Var 1, Var 2] (P.Fin 0) (P.Fin 2),
           Bind 0 1, External (Var 1) (Var 2), Bind 1 2],
          [Domain (Var 0) (P.Fin 0) (P.Fin 3),
           Unify (Compound "pair" [Var 0, Var 1]) (Compound "pair" [IntLit 2, Atom "ok"]),
           Unify (Var 2) (Compound "box" [Var 2]), Bind 0 7],
          [Relation P.RelEq (Compound "mul" [Var 0, Var 1]) (Var 2),
           Reified P.RelLe (Var 2) (IntLit 3) (Var 3),
           Domains [Var 0, Var 1] (P.Fin 1) (P.Fin 3), Bind 0 2, Bind 1 3]
        ]
  forM_ scenarios $ \operations -> do
    annotateShow operations
    store <- evalIO (M.new P.emptyStore)
    checkpoint <- evalIO (M.mark store)
    _ <- foldM (\before next -> fst <$> applyChecked store before next) P.emptyStore operations
    evalIO (M.rollback store checkpoint)
    frozen <- evalIO (M.freeze store)
    frozen === P.emptyStore

prop_import_and_rebuild :: Property
prop_import_and_rebuild = withTests 1 . property $ do
  let seeded = P.emptyStore
        { P.stDomains = IM.fromList [(0, P.Domain (P.Fin 0) (P.Fin 4) (Set.singleton 2))],
          P.stConstraints = [P.CLinear P.RelLe (P.LinExpr (IM.fromList [(0, 1), (1, 1)]) (-3)),
            P.CDiseq (Var 0) (Var 1)]
        }
      indexed = do
        first <- P.addDomains [Var 0, Var 1, Var 2] (P.Fin 0) (P.Fin 4) P.emptyStore
        maybe (Right Nothing) (P.addAllDifferent [Var 0, Var 1, Var 2]) first
  normal <- evalEither indexed >>= maybe failure pure
  forM_ [P.emptyStore, seeded, normal] $ \initial -> do
    store <- evalIO (M.new initial)
    untouched <- evalIO (M.freeze store)
    untouched === initial
    checkpoint <- evalIO (M.mark store)
    _ <- applyChecked store initial Propagate
    evalIO (M.rollback store checkpoint)
    restored <- evalIO (M.freeze store)
    restored === initial

prop_exact_replacement_and_binding_writes :: Property
prop_exact_replacement_and_binding_writes = withTests 1 . property $ do
  first <- evalEither (P.addDomains [Var 0, Var 1] (P.Fin 0) (P.Fin 4) P.emptyStore) >>= maybe failure pure
  initial <- evalEither (P.addRelation P.RelEq (Var 0) (Compound "plus" [Var 1, IntLit 1]) first) >>= maybe failure pure
  store <- evalIO (M.new initial)
  checkpoint <- evalIO (M.mark store)
  (bound, _) <- applyChecked store initial (Bind 1 2)
  changes <- evalIO (M.changesSince store checkpoint)
  let expected = [(variable, value) | (variable, value) <- IM.toAscList (P.stSubst bound),
        IM.lookup variable (P.stSubst initial) /= Just value]
  sort changes === expected
  -- Frozen answers retain their value across replacing the entire live
  -- solver state, exactly as minimum winners and reference adapters do.
  snapshot <- evalIO (M.freeze store)
  let rendered = show snapshot
  _ <- evalIO (evaluate (length rendered))
  evalIO (M.replaceStore store P.emptyStore)
  replaced <- evalIO (M.freeze store)
  replaced === P.emptyStore
  show snapshot === rendered
  evalIO (M.rollback store checkpoint)
  restored <- evalIO (M.freeze store)
  restored === initial
  unchanged <- evalIO (M.changesSince store checkpoint)
  unchanged === []

prop_commit_reclaims_history :: Property
prop_commit_reclaims_history = withTests 1 . property $ do
  store <- evalIO (M.new P.emptyStore)
  let operations =
        [Domains [Var 0, Var 1] (P.Fin 0) (P.Fin 5),
         Relation P.RelEq (Var 0) (Compound "plus" [Var 1, IntLit 1])]
  before <- foldM (\current next -> fst <$> applyChecked store current next) P.emptyStore operations
  snapshot <- evalIO (M.freeze store)
  historyBefore <- evalIO (M.historySize store)
  assert (historyBefore > 0)
  -- No external checkpoint exists here: deterministic execution can discard
  -- its old undo entries while preserving the live solver state exactly.
  root <- evalIO (M.commit store)
  historyAfter <- evalIO (M.historySize store)
  historyAfter === 0
  committed <- evalIO (M.freeze store)
  committed === before
  (bound, succeeds) <- applyChecked store before (Bind 1 2)
  assert succeeds
  P.storeWalk bound (Var 0) === IntLit 3
  newHistory <- evalIO (M.historySize store)
  assert (newHistory > 0)
  evalIO (M.rollback store root)
  restored <- evalIO (M.freeze store)
  restored === before
  reclaimed <- evalIO (M.historySize store)
  reclaimed === 0
  snapshot === before
  -- Each one-variable bound is absorbed into its domain and drops its
  -- constraint. Keep snapshots out of this loop: otherwise freezing could
  -- hide retained tombstones or deferred snapshot deltas between commits.
  streaming <- evalIO (M.new P.emptyStore)
  let narrow current upper = do
        let next = Relation P.RelLe (Var 0) (IntLit upper)
        expected <- evalEither (persistent next current) >>= maybe failure pure
        checkpoint <- evalIO (M.mark streaming)
        trial <- evalIO (M.addRelation streaming P.RelLe (Var 0) (IntLit upper))
        trial === Right True
        evalIO (M.rollback streaming checkpoint)
        undone <- evalIO (M.historySize streaming)
        undone === 0
        actual <- evalIO (M.addRelation streaming P.RelLe (Var 0) (IntLit upper))
        actual === Right True
        _ <- evalIO (M.commit streaming)
        history <- evalIO (M.historySize streaming)
        history === 0
        (variables, constraints) <- evalIO (M.storageSizes streaming)
        assert (variables <= 2)
        constraints === 0
        pure expected
  final <- foldM narrow P.emptyStore [1000, 999 .. 1]
  frozen <- evalIO (M.freeze streaming)
  frozen === final

data Event = Answer [(String, Term)] [String] [OutputEvent] Int
  | Problem SolveError | Exhausted | Cut Int | Incomplete Term
  deriving (Eq, Show)

observe :: Query -> Search -> [Event]
observe query = map event
  where
    event (Found state) = let answer = projectAnswer query state in
      Answer (answerBindings answer) (answerResiduals answer) (answerOutput answer) (ssFresh state)
    event (BranchError err) = Problem err
    event BranchExhausted = Exhausted
    event (CutMarker owner) = Cut owner
    event (ConsumedIncomplete key) = Incomplete key

native :: Int -> Program -> Query -> PropertyT IO Search
native limit program query = do
  result <- evalIO $ timeout 120000000 $ do
    (_, first) <- Run.runCoreWith limit program query
    let drain action = do
          step <- action
          case step of
            Run.Stop -> pure []
            Run.Yield item next -> (item :) <$> drain next
            Run.Abandon reason -> fail ("mutable CLP acceptance abandoned: " ++ reason)
    items <- drain first
    _ <- evaluate (length (show (observe query items)))
    pure items
  maybe (annotate "Native CLP acceptance exceeded 120s" >> failure) pure result

nativePropagation :: Int -> Program -> Query -> PropertyT IO (Search, (Int, Int, Int))
nativePropagation limit program query = do
  result <- evalIO $ timeout 120000000 $ do
    (_, first, counters) <- Run.runCoreWithPropagationStats limit program query
    let drain action = do
          step <- action
          case step of
            Run.Stop -> pure []
            Run.Yield item next -> (item :) <$> drain next
            Run.Abandon reason -> fail ("mutable propagation acceptance abandoned: " ++ reason)
    items <- drain first
    _ <- evaluate (length (show (observe query items)))
    counts <- counters
    pure (items, counts)
  completed@(_, (propagations, linear, _)) <-
    maybe (annotate "Measured native CLP acceptance exceeded 120s" >> failure) pure result
  assert (propagations > 0)
  assert (linear > 0)
  pure completed

loadExample :: FilePath -> PropertyT IO Program
loadExample path = do
  source <- evalIO (readFile path)
  items <- evalEither (parseFile source)
  evalEither (buildChecked [item | item <- items, case item of TLQuery _ -> False; _ -> True])

parity :: Int -> Program -> String -> PropertyT IO (Query, Search)
parity limit program text = do
  annotate text
  query <- evalEither (parseQuery text)
  actual <- native limit program query
  observe query actual === observe query (Reference.solveQuery program query)
  pure (query, actual)

parityPropagation :: Int -> Program -> String -> PropertyT IO (Query, Search, (Int, Int, Int))
parityPropagation limit program text = do
  annotate text
  query <- evalEither (parseQuery text)
  (actual, counts) <- nativePropagation limit program query
  observe query actual === observe query (Reference.solveQuery program query)
  pure (query, actual, counts)

answers :: Query -> Search -> PropertyT IO [[(String, Term)]]
answers query items = forM items $ \item -> case item of
  Found state -> do
    let answer = projectAnswer query state
    answerResiduals answer === []
    answerOutput answer === []
    pure (answerBindings answer)
  other -> annotateShow (observe query [other]) >> failure

binding :: String -> [(String, Term)] -> PropertyT IO Term
binding name bindings = maybe (annotateShow bindings >> failure) pure (lookup name bindings)

asList :: Term -> PropertyT IO [Term]
asList value = case unfoldCons value of
  (values, Nothing) -> pure values
  _ -> annotateShow value >> failure

integer :: Term -> PropertyT IO Integer
integer (IntLit value) = pure value
integer other = annotateShow other >> failure

grid :: [(String, Term)] -> PropertyT IO [[Integer]]
grid bindings = binding "Grid" bindings >>= asList >>= mapM (\row -> asList row >>= mapM integer)

validWindows :: Int -> Int -> Integer -> [[Integer]] -> Bool
validWindows width height cap rows = and
  [sum [rows !! y !! x | y <- [top .. top + height - 1], x <- [left .. left + width - 1]] <= cap
    | top <- [0 .. length rows - height], left <- [0 .. columns - width]]
  where columns = case rows of first : _ -> length first; [] -> 0

chunks :: Int -> [a] -> [[a]]
chunks _ [] = []
chunks width values = take width values : chunks width (drop width values)

prop_native_small_minefields :: Property
prop_native_small_minefields = withTests 50 . property $ do
  width <- forAll (Gen.int (Range.linear 1 3))
  height <- forAll (Gen.int (Range.linear 1 3))
  bombs <- forAll (Gen.int (Range.linear 0 (width * height)))
  cap <- forAll (Gen.int (Range.linear 0 4))
  seed <- forAll (Gen.int (Range.linear (-50) 50))
  program <- loadExample "examples/minesweeper.nprolog"
  let arguments = unwords (map show [width, height, bombs]) ++ " [window 2 2 " ++ show cap ++ "]"
      model = sort [rows | cells <- sequence (replicate (width * height) [0, 1]),
        sum cells == toInteger bombs, let rows = chunks width cells,
        validWindows 2 2 (toInteger cap) rows]
  forM_ ["minefield " ++ arguments ++ " Grid?",
    "minefield_seed " ++ arguments ++ " " ++ show seed ++ " Grid?"] $ \text -> do
      (query, actual) <- parity 1 program text
      bindings <- answers query actual
      values <- mapM grid bindings
      sort values === model

prop_native_large_minefields :: Property
prop_native_large_minefields = withTests 1 . property $ do
  program <- loadExample "examples/minesweeper.nprolog"
  forM_ [("once (minefield 16 16 50 [window 2 2 2] Grid)?", 16, 16, [(2, 2, 2)]),
    ("once (minefield_seed 10 10 50 [window 2 2 2] 42 Grid)?", 10, 10, [(2, 2, 2)]),
    ("once (minefield_seed 8 6 12 [window 2 2 2, window 3 3 3] -42 Grid)?", 8, 6, [(2, 2, 2), (3, 3, 3)])] $
      \(text, width, height, rules) -> do
        (query, actual, _) <- parityPropagation 1 program text
        bindings <- answers query actual
        length bindings === 1
        values <- mapM grid bindings
        forM_ values $ \rows -> do
          length rows === height
          map length rows === replicate height width
          assert (all (`elem` [0, 1]) (concat rows))
          sum (concat rows) === if width == 8 then 12 else 50
          forM_ rules $ \(w, h, cap) -> assert (validWindows w h cap rows)

-- Recompute every node and hole from physical coordinates, and enumerate
-- all bounded column/half choices without consulting Infera's score goals.
data Placed = Placed Term Term Integer Integer Integer Integer Integer Integer Integer
  deriving Show

placements :: Term -> PropertyT IO [Placed]
placements value = asList value >>= mapM part
  where
    part (Compound "pl" [_, _, _, a, b, _, IntLit row, IntLit col, IntLit half,
      IntLit ha, IntLit hb, IntLit na, IntLit nb]) = pure (Placed a b row col half ha hb na nb)
    part other = annotateShow other >> failure

score :: [Placed] -> Integer
score ps = sum [abs (col - 9) | Placed _ _ _ col _ _ _ _ _ <- ps] +
  sum [pair p q | (i, p) <- zip [0 :: Int ..] ps, q <- drop (i + 1) ps]
  where
    pair (Placed a b _ col half _ _ _ _) (Placed c d _ otherCol otherHalf _ _ _ _) =
      (if half == otherHalf then 0 else 2) +
      (if half == otherHalf && abs (col - otherCol) <= 2 &&
        not (a == c || a == d || b == c || b == d) then 4 else 0)

validPlacement :: [Term] -> Integer -> Integer -> [Placed] -> Bool
validPlacement wired lo hi ps = not (null ps) && onTop && all part ps &&
  length holes == length (nub holes) &&
  and [compatible p q | (i, p) <- zip [0 :: Int ..] pins, q <- drop (i + 1) pins]
  where
    onTop = case ps of Placed _ _ _ _ half _ _ _ _ : _ -> half == 0; [] -> False
    part (Placed _ _ row col half ha hb na nb) = row >= 1 && row <= 5 && col >= lo && col <= hi &&
      half `elem` [0, 1] && na == half * 100 + col && nb == na + 1 &&
      ha == na * 10 + row && hb == nb * 10 + row
    holes = concat [[ha, hb] | Placed _ _ _ _ _ ha hb _ _ <- ps]
    pins = concat [[(a, na), (b, nb)] | Placed a b _ _ _ _ _ na nb <- ps]
    compatible (a, na) (b, nb) | a == b = a `elem` wired || na == nb
                             | otherwise = na /= nb

prop_native_breadboard :: Property
prop_native_breadboard = withTests 1 . property $ do
  program <- loadExample "examples/breadboard.nprolog"
  let standard name jumpers = ("comps " ++ name ++ " Cs, nets Cs Ns, best Cs Ns Wired P Cost?", 7, 11, jumpers)
      wide = ("Cs = [c p0 r \"1k\" n0 n1 1 1, c p1 r \"1k\" n2 n3 2 2, " ++
        "c p2 r \"1k\" n4 n5 3 3], Wired = [], solve_min Cs Wired 1 16 P Cost?", 1, 16, 0)
  forM_ [standard "rc" 0, standard "div" 0, standard "tri" 1, wide] $ \(text, lo, hi, jumpers) -> do
    (query, actual, (_, _, complex)) <- parityPropagation 1 program text
    -- Hole distinctness and scoring reification exercise the hybrid complex
    -- reducer as well as the mutable scheduler and native linear reducer.
    assert (complex > 0)
    bindings <- answers query actual
    length bindings === 1
    forM_ bindings $ \answer -> do
      wired <- binding "Wired" answer >>= asList
      length wired === jumpers
      ps <- binding "P" answer >>= placements
      cost <- binding "Cost" answer >>= integer
      assert (validPlacement wired lo hi ps)
      cost === score ps
      let candidates = sequence
            [[Placed a b row col half (na * 10 + row) ((na + 1) * 10 + row) na (na + 1)
              | col <- [lo .. hi], half <- if i == 0 then [0] else [0, 1], let na = half * 100 + col]
              | (i, Placed a b row _ _ _ _ _ _) <- zip [0 :: Int ..] ps]
          costs = [score candidate | candidate <- candidates, validPlacement wired lo hi candidate]
      assert (not (null costs))
      cost === minimum costs

prop_native_rollback_and_retention :: Property
prop_native_rollback_and_retention = withTests 1 . property $ do
  loaded <- evalIO (loadFile "test/core/parity-mutable-clp.nprolog")
  (program, queries) <- evalEither loaded
  forM_ queries $ \query -> do
    annotateShow (queryGoals query)
    actual <- native 1 program query
    observe query actual === observe query (Reference.solveQuery program query)
  query <- evalEither (parseQuery "[X,Y] in 0..3, X #< Y, label [X,Y]?")
  (_, first) <- evalIO (Run.runCoreWith 1 program query)
  initial <- evalIO first
  case initial of
    Run.Yield (Found state) next -> do
      let snapshot = show (ssStore state)
      _ <- evalIO (evaluate (length snapshot))
      let drain action = do
            step <- action
            case step of
              Run.Stop -> pure ()
              Run.Yield _ more -> drain more
              Run.Abandon reason -> fail reason
      evalIO (drain next)
      show (ssStore state) === snapshot
      answerBindings (projectAnswer query state) === [("X", IntLit 0), ("Y", IntLit 1)]
    _ -> annotate "Expected native first answer before resuming mutable propagation" >> failure

mutableCLPGroup :: Group
mutableCLPGroup = Group "mutable CLP propagation and acceptance"
  [ ("generated operation traces preserve exact scheduler snapshots and rollback", prop_generated_traces),
    ("generated finite solution sets match independent arithmetic models", prop_finite_models),
    ("failed and erroneous propagation is atomic", prop_atomic_boundaries),
    ("public Store imports and propagation rebuild preserve snapshots", prop_import_and_rebuild),
    ("exact replacement and propagated writes preserve prior snapshots", prop_exact_replacement_and_binding_writes),
    ("deterministic history reclamation preserves state and fresh checkpoints", prop_commit_reclaims_history),
    ("native generated minefields match complete finite models", prop_native_small_minefields),
    ("native large and seeded minefields satisfy overlapping rules", prop_native_large_minefields),
    ("native breadboard placements have independently optimal costs", prop_native_breadboard),
    ("native nested control and retained answers survive mutable rollback", prop_native_rollback_and_retention)
  ]

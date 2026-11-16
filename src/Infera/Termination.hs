-- | Total recursion inference (docs/2026-11-16-TOTAL-RECURSION.md).
--
-- Every predicate gets a 'Verdict' saying whether its recursion always ends,
-- and under which condition on its arguments. Proofs use size-change
-- termination (Lee, Jones and Ben-Amram): each recursive call contributes a
-- graph of how the callee's arguments relate in size to the caller's, and
-- the recursion ends when every infinite sequence of calls has an argument
-- thread that decreases infinitely often. That accepts permuted arguments,
-- lexicographic descent, merges that shrink a different argument at each
-- call and mutual recursion, and it rejects recursion that shrinks one
-- argument while growing another one that a later call shrinks back.
--
-- Step 0 has one norm: the subterm order on ground arguments. An argument
-- can only be measured when it is ground at the call (its size cannot grow
-- through later bindings); a verdict's condition names the argument
-- positions that must be ground. Later steps add list length, integers with
-- floors from guards, size relations through callees and tabling over finite
-- domains, all checked by the same size-change test.
module Infera.Termination
  ( Verdict (..),
    Proof (..),
    verdicts,
    renderVerdict,
    verdictStatus,
  )
where

import Data.Graph (SCC (..), stronglyConnComp)
import Data.List (foldl', nub, zip3)
import qualified Data.IntMap.Strict as IM
import Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map
import Data.Maybe (isJust)
import Data.Set (Set)
import qualified Data.Set as Set
import Infera.Error (showPredKey)
import Infera.Infer (groundDependencies)
import Infera.Program
import Infera.Syntax

-- | A proof that a recursive predicate's calls always end.
data Proof = Proof
  { -- | Alternative conditions: the recursion ends when every position
    -- (1-based) of at least one of these sets is ground at the call.
    proofConditions :: [[Int]],
    -- | The predicate calls a closure it was given, so its calls end only
    -- when that closure's calls do.
    proofClosures :: Bool
  }
  deriving (Eq, Show)

data Verdict
  = -- | The predicate cannot reach itself.
    NotRecursive
  | Total Proof
  | -- | Why no proof was found, naming the call that defeats it.
    Unproven String
  | -- | An io predicate whose recursion was not proven: it runs for as long
    -- as the world feeds it, which is what an effect loop is for.
    Reactive
  deriving (Eq, Show)

verdictStatus :: Verdict -> String
verdictStatus v = case v of
  NotRecursive -> "not-recursive"
  Total _ -> "total"
  Unproven _ -> "unproven"
  Reactive -> "reactive"

renderVerdict :: Verdict -> String
renderVerdict v = case v of
  NotRecursive -> "not recursive"
  Reactive -> "reactive: an io loop that runs while the world feeds it"
  Unproven why -> "recursion not proven total: " ++ why
  Total (Proof conds closures) ->
    "total when "
      ++ joinWith " or " (map condition conds)
      ++ " (subterm descent)"
      ++ (if closures then ", given that its closure arguments are total" else "")
  where
    condition [] = "called in any mode"
    condition [i] = "argument " ++ show i ++ " is ground"
    condition is = "arguments " ++ joinWith ", " (map show is) ++ " are ground"
    joinWith sep = foldr1' (\a b -> a ++ sep ++ b)
    foldr1' _ [] = ""
    foldr1' f xs = foldr1 f xs

-- ─── Calls ───────────────────────────────────────────────────────────────────

-- | A call made from a clause body, with the goals that certainly ran before
-- it in the same clause (the head unification is implicit).
data Call = Call
  { callClause :: Int,
    callHead :: [Term],
    callBefore :: [Term],
    callTarget :: Target,
    callGoal :: Term
  }

data Target
  = -- | A statically known user predicate and the arguments passed to it.
    -- An argument the call cannot see (supplied later by a meta-predicate)
    -- is 'Nothing'.
    CallUser PredKey [Maybe Term]
  | -- | A closure the predicate received in head position.
    CallParameter
  | -- | A goal built at run time: it could call anything.
    CallOpaque

-- | Meta-argument positions: position i (0-based) of a predicate is called
-- as a closure with n extra arguments.
type Meta = Map PredKey (Set (Int, Int))

-- | Goals with their dominating goals: a goal G is reported together with
-- the goals that must have succeeded, in this clause, before G runs. Goals
-- under negation, findall and the like are still calls, but bind nothing.
dominated :: [Term] -> [(Term, [Term])]
dominated = go []
  where
    go _ [] = []
    go dom (g : gs) = inner dom g ++ go (dom ++ definite g) gs
    inner dom g = case g of
      Compound "," [a, b] -> go dom [a, b]
      Compound ";" [Compound "->" [c, t], e] -> inner dom c ++ go (dom ++ definite c) [t] ++ inner dom e
      Compound ";" [a, b] -> inner dom a ++ inner dom b
      Compound "->" [c, t] -> inner dom c ++ go (dom ++ definite c) [t]
      Compound "not" [a] -> inner dom a
      Compound "once" [a] -> inner dom a
      Compound "forall" [a, b] -> inner dom a ++ go (dom ++ definite a) [b]
      Compound "findall" [_, a, _] -> inner dom a
      Compound f [_, a, _] | f `elem` ["bagof", "setof", "std_native_bagof", "std_native_setof"] -> inner dom (strip a)
      Compound "minimize" [_, a] -> inner dom a
      _ -> [(g, dom)]
    definite g = case g of
      Compound "," [a, b] -> definite a ++ definite b
      Compound "once" [a] -> definite a
      Compound "->" [a, b] -> definite a ++ definite b
      Compound ";" _ -> []
      Compound "not" _ -> []
      Compound "forall" _ -> []
      Compound "findall" _ -> []
      Compound f _ | f `elem` ["bagof", "setof", "std_native_bagof", "std_native_setof", "minimize"] -> []
      _ -> [g]
    strip (Compound "^" [_, a]) = strip a
    strip a = a

headArgs :: Clause -> [Term]
headArgs cl = case clauseHead cl of
  Compound _ as -> as
  _ -> []

-- | Resolve a closure term called with @n@ extra arguments.
closureTarget :: Program -> [Term] -> Term -> Int -> [Maybe Term] -> Target
closureTarget prog hs c n extra = case c of
  Atom f -> user (f, n) []
  Compound f as -> user (f, length as + n) as
  Var v | Var v `elem` hs -> CallParameter
  _ -> CallOpaque
  where
    user k captured
      | isJust (lookupPred k prog) = CallUser k (map Just captured ++ extra)
      | otherwise = CallUser k [] -- a builtin closure: no user edge

-- | The calls a clause makes, including closures passed to meta-predicates.
clauseCalls :: Program -> Meta -> Int -> Clause -> [Call]
clauseCalls prog meta ci cl = concatMap call (dominated (clauseBody cl))
  where
    hs = headArgs cl
    mk dom g t = Call ci hs dom t g
    call (g, dom) = case g of
      Var v | Var v `elem` hs -> [mk dom g CallParameter]
      Var _ -> [mk dom g CallOpaque]
      Compound "call" (c : extra) -> [mk dom g (closureTarget prog hs c (length extra) (map Just extra))]
      Compound "phrase" [c, s0] -> [mk dom g (closureTarget prog hs c 2 [Just s0, Just nil])]
      Compound "phrase" [c, s0, s] -> [mk dom g (closureTarget prog hs c 2 [Just s0, Just s])]
      _ -> case functorOf g of
        Just k | isJust (lookupPred k prog) ->
          let args = case g of
                Compound _ as -> as
                _ -> []
              direct = mk dom g (CallUser k (map Just args))
              closures =
                [ mk dom g (closureTarget prog hs c n (replicate n Nothing))
                | (i, n) <- Set.toList (Map.findWithDefault Set.empty k meta),
                  i < length args,
                  let c = args !! i
                ]
           in direct : closures
        _ -> []

-- | Meta-argument positions of every predicate, to a fixpoint: a head
-- variable is a closure when the body calls it, or passes it on in a
-- meta-argument position of another predicate.
metaPositions :: Program -> Meta
metaPositions prog = go Map.empty
  where
    preds = programPreds prog
    go meta =
      let meta' = Map.fromList [(predKey p, positions meta p) | p <- preds]
          nonEmpty = Map.filter (not . Set.null) meta'
       in if nonEmpty == meta then meta else go nonEmpty
    positions meta p =
      Set.fromList
        [ (i, n)
        | cl <- IM.elems (predClauses p),
          let hs = headArgs cl,
          (i, Var v) <- zip [0 ..] hs,
          (g, _) <- dominated (clauseBody cl),
          n <- usesAt meta v g
        ]
    usesAt meta v g = case g of
      Var u | u == v -> [0]
      Compound "call" (Var u : extra) | u == v -> [length extra]
      Compound "phrase" (Var u : _) | u == v -> [2]
      _ -> case (functorOf g, g) of
        (Just k, Compound _ as) ->
          [n | (j, n) <- Set.toList (Map.findWithDefault Set.empty k meta), j < length as, as !! j == Var v]
        _ -> []

-- ─── Size-change graphs ──────────────────────────────────────────────────────

-- | Arcs from caller positions to callee positions: (i, j, strict). A strict
-- arc means the callee's argument j is a proper subterm of the caller's
-- argument i; a non-strict arc means it is equal.
type Arcs = Set (Int, Int, Bool)

data SCG = SCG
  { scgFrom :: PredKey,
    scgTo :: PredKey,
    scgArcs :: Arcs,
    -- | The first call of the path this graph summarises, for reports.
    scgCall :: (PredKey, Call)
  }

-- | The size-change graph of a call, given the caller positions that are
-- ground at this call, and the callee positions that are ground as a result.
callGraph :: Deps -> Set Int -> Call -> [Maybe Term] -> (Arcs, Set Int)
callGraph deps rigid c args = (arcs, groundOut)
  where
    hs = callHead c
    ground = groundVars deps rigid hs (callBefore c)
    groundOut = Set.fromList [j | (j, Just a) <- zip [0 ..] args, all (`Set.member` ground) (termVarIds a)]
    arcs =
      Set.fromList
        [ (i, j, strict)
        | (i, h) <- zip [0 ..] hs,
          Set.member i rigid,
          let (equal, smaller) = relatives h (callBefore c),
          (j, Just a) <- zip [0 ..] args,
          strict <- [True | Set.member a smaller] ++ [False | Set.member a equal, not (Set.member a smaller)]
        ]

-- | Arguments ground after a successful call when all the others were
-- ground at the call ('groundDependencies').
type Deps = Map PredKey [Bool]

-- | Variables certainly ground at the call: those of ground head arguments,
-- closed in order under the unifications, evaluations and calls that ran
-- before it. A call grounds argument j when its other arguments were ground
-- and the callee's dependencies say j follows from them.
groundVars :: Deps -> Set Int -> [Term] -> [Term] -> Set VarId
groundVars deps rigid hs before = foldl' step start before
  where
    start = Set.fromList (concat [termVarIds h | (i, h) <- zip [0 ..] hs, Set.member i rigid])
    groundIn g t = all (`Set.member` g) (termVarIds t)
    step g goal = case goal of
      Compound "unify" [a, b]
        | groundIn g a -> Set.union g (Set.fromList (termVarIds b))
        | groundIn g b -> Set.union g (Set.fromList (termVarIds a))
      Compound "is" [v, e] | groundIn g e -> Set.union g (Set.fromList (termVarIds v))
      Compound f as
        | Just ds <- Map.lookup (f, length as) deps ->
            Set.union g . Set.fromList $
              concat
                [ termVarIds a
                | (j, a, True) <- zip3 [0 :: Int ..] as ds,
                  and [groundIn g b | (i, b) <- zip [0 ..] as, i /= j]
                ]
      _ -> g

-- | Terms equal to a head argument, and terms that are proper subterms of
-- it, following the unifications that ran before the call.
relatives :: Term -> [Term] -> (Set Term, Set Term)
relatives h = foldl' step (Set.singleton h, Set.fromList (properSubterms h))
  where
    step (eq, sm) goal = case goal of
      Compound "unify" [a, b] -> pair (pair (eq, sm) a b) b a
      _ -> (eq, sm)
    pair (eq, sm) a b
      | Set.member a eq = (Set.insert b eq, Set.union sm (Set.fromList (properSubterms b)))
      | Set.member a sm = (eq, Set.insert b (Set.union sm (Set.fromList (properSubterms b))))
      | otherwise = (eq, sm)

properSubterms :: Term -> [Term]
properSubterms t = case t of
  Compound _ as -> concatMap (\a -> a : properSubterms a) as
  _ -> []

compose :: SCG -> SCG -> SCG
compose g1 g2 = SCG (scgFrom g1) (scgTo g2) arcs (scgCall g1)
  where
    -- A path through any strict arc is strict; keep one arc per pair.
    arcs =
      Set.fromList
        [ (i, k, s)
        | ((i, k), s) <-
            Map.toList
              ( Map.fromListWith
                  (||)
                  [ ((i, k), s1 || s2)
                  | (i, j, s1) <- Set.toList (scgArcs g1),
                    (j', k, s2) <- Set.toList (scgArcs g2),
                    j == j'
                  ]
              )
        ]

-- | Closure of a set of graphs under composition, keyed by (from, to, arcs).
closure :: [SCG] -> Map (PredKey, PredKey, Arcs) SCG
closure base = grow initial (Map.elems initial)
  where
    key g = (scgFrom g, scgTo g, scgArcs g)
    initial = Map.fromListWith (\_ old -> old) [(key g, g) | g <- base]
    grow known [] = known
    grow known (g : pending) =
      let new =
            [ h
            | b <- base,
              scgTo g == scgFrom b,
              let h = compose g b,
              not (Map.member (key h) known)
            ]
          known' = foldl' (\m h -> Map.insertWith (\_ old -> old) (key h) h m) known new
       in grow known' (pending ++ new)

-- | A failing idempotent graph from the predicate to itself, if any.
violation :: PredKey -> Map (PredKey, PredKey, Arcs) SCG -> Maybe SCG
violation k gs =
  case [ g
       | g <- Map.elems gs,
         scgFrom g == k,
         scgTo g == k,
         scgArcs (compose g g) == scgArcs g,
         not (any (\(i, j, s) -> s && i == j) (Set.toList (scgArcs g)))
       ] of
    (g : _) -> Just g
    [] -> Nothing

-- ─── Verdicts ────────────────────────────────────────────────────────────────

verdicts :: Program -> Map PredKey Verdict
verdicts prog = Map.fromList (concatMap component sccs)
  where
    meta = metaPositions prog
    deps = groundDependencies prog
    preds = [p | p <- programPreds prog, not (IM.null (predClauses p))]
    callsOf :: Map PredKey [Call]
    callsOf =
      Map.fromList
        [ (predKey p, concat [clauseCalls prog meta ci cl | (ci, cl) <- zip [1 ..] (IM.elems (predClauses p))])
        | p <- preds
        ]
    userEdges k = nub [t | Call {callTarget = CallUser t _} <- Map.findWithDefault [] k callsOf, Map.member t callsOf]
    sccs = stronglyConnComp [(predKey p, predKey p, userEdges (predKey p)) | p <- preds]
    component scc = case scc of
      AcyclicSCC k
        | k `notElem` userEdges k -> [(k, nonRecursive k)]
        | otherwise -> verdictsFor [k]
      CyclicSCC ks -> verdictsFor ks
    calls k = Map.findWithDefault [] k callsOf
    nonRecursive k = case [c | c <- calls k, CallOpaque <- [callTarget c]] of
      (c : _) -> Unproven (opaque k c)
      [] -> NotRecursive
    opaque k c =
      "calls a goal built at run time in clause " ++ show (callClause c) ++ " of "
        ++ showPredKey k ++ ", which could call back"
    verdictsFor ks = [(k, finish k (verdictIn group k)) | k <- ks]
      where
        group = Set.fromList ks
    finish k v = case v of
      Total _ -> v
      _ | Just p <- lookupPred k prog, FlagIo `elem` effectiveFlags prog p -> Reactive
      _ -> v
    verdictIn group k
      | Just p <- lookupPred k prog, predIsDynamic prog p = Unproven "dynamic: its clauses change at run time"
      | (c : _) <- [c | m <- Set.toList group, c <- calls m, CallOpaque <- [callTarget c]] = Unproven (opaque k c)
      | otherwise =
          let arity = snd k
              allPositions = [0 .. arity - 1]
              attempt s = prove group k (Set.fromList s)
              closures = any (\m -> any (isParameter . callTarget) (calls m)) (Set.toList group)
              -- Only positions that carry an arc out of k can be part of a
              -- minimal condition; others are searched only as the full set.
              relevant =
                Set.toList . Set.fromList $
                  [ i
                  | c <- calls k,
                    CallUser t args <- [callTarget c],
                    Set.member t group,
                    (i, _, _) <- Set.toList (fst (callGraph deps (Set.fromList allPositions) c args))
                  ]
              -- Every minimal set that suffices, smallest first: a proven
              -- set is kept unless it contains one already kept.
              minimal = foldl' keep [] [s | n <- [0 .. length relevant], s <- subsetsOf n relevant]
              keep found s
                | any (`subsetOf` s) found = found
                | either (const False) (const True) (attempt s) = found ++ [s]
                | otherwise = found
              subsetOf a b = all (`elem` b) a
           in case attempt allPositions of
                Left why -> Unproven why
                Right () ->
                  let found = if null minimal then [allPositions] else minimal
                   in Total (Proof (map (map (+ 1)) found) closures)
    isParameter CallParameter = True
    isParameter _ = False

    -- Size-change test for entry k with the positions s ground at entry.
    prove :: Set PredKey -> PredKey -> Set Int -> Either String ()
    prove group k s =
      let rigid = groundFixpoint group k s
          graphs =
            [ SCG m t arcs (m, c)
            | m <- Set.toList group,
              c <- calls m,
              CallUser t args <- [callTarget c],
              Set.member t group,
              let (arcs0, _) = callGraph deps (Map.findWithDefault Set.empty m rigid) c args,
              let arcs = Set.filter (\(_, j, _) -> Set.member j (Map.findWithDefault Set.empty t rigid)) arcs0
            ]
       in case violation k (closure graphs) of
            Nothing -> Right ()
            Just g -> Left (describe g)
    describe g =
      let (m, c) = scgCall g
       in "no argument certainly shrinks along the calls starting at the call to "
            ++ callee c ++ " in clause " ++ show (callClause c) ++ " of " ++ showPredKey m
    callee c = case callTarget c of
      CallUser t _ -> showPredKey t
      _ -> "a closure"

    -- Positions ground at every call in the group, when the entry k has s.
    groundFixpoint :: Set PredKey -> PredKey -> Set Int -> Map PredKey (Set Int)
    groundFixpoint group k s = go start
      where
        start = Map.fromList [(m, if m == k then s else Set.fromList [0 .. snd m - 1]) | m <- Set.toList group]
        go r =
          let incoming =
                Map.fromListWith Set.intersection
                  [ (t, out)
                  | m <- Set.toList group,
                    c <- calls m,
                    CallUser t args <- [callTarget c],
                    Set.member t group,
                    let (_, out) = callGraph deps (Map.findWithDefault Set.empty m r) c args
                  ]
              r' = Map.mapWithKey (\m v -> maybe v (Set.intersection v) (Map.lookup m incoming)) r
           in if r' == r then r else go r'

subsetsOf :: Int -> [a] -> [[a]]
subsetsOf 0 _ = [[]]
subsetsOf _ [] = []
subsetsOf n (x : xs) = map (x :) (subsetsOf (n - 1) xs) ++ subsetsOf n xs


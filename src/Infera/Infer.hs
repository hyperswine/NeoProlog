{-# OPTIONS_GHC -Wno-name-shadowing #-}

-- | Static inference of sorts, modes and determinism, plus the call-graph
-- facts (recursion, purity) used to decide default tabling.
--
-- Inferred signatures are advisory: the engine only uses the inferred
-- determinism (together with its 'sigSwitch' positions) to drop choice points.
-- Groundness proofs converge on finite Boolean environments; guards and
-- alternative declarations are checked conservatively. Declared signatures
-- are enforced at runtime.
module Infera.Infer
  ( inferProgram,
    subGoals,
    builtinDet,
    impureBuiltins,
    joinSort,
    exclusive,
  )
where

import Data.IntMap.Strict (IntMap)
import qualified Data.IntMap.Strict as IM
import Control.Monad (zipWithM)
import Data.List (foldl', nub, partition, sortOn)
import Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map
import Data.Maybe (fromMaybe, isJust, mapMaybe)
import Data.Set (Set)
import qualified Data.Set as Set
import Infera.Arith (arithOps, compareNumeric, evalNumeric)
import Infera.Program
import Infera.Syntax

-- ─── ENTRY POINT ─────────────────────────────────────────────────────────────

inferProgram :: Program -> Program
inferProgram prog0 =
  let prog1 = markGraphFacts prog0
      sorts = inferSorts prog1
      ins = inferInModes prog1
      (outs, deps) = inferGroundness prog1 ins
      dets = inferDets prog1 ins outs deps
      finish p =
        let k = predKey p
            arity = snd k
            ss = Map.findWithDefault (replicate arity SNone) k sorts
            is = Map.findWithDefault (replicate arity False) k ins
            os = Map.findWithDefault (replicate arity False) k outs
            (d, sw) = Map.findWithDefault (Nondet, []) k dets
            args =
              [ ArgSpec (display s) (mode i o)
              | (s, i, o) <- zip3 ss is os
              ]
         in p {predInferred = Signature d args sw}
      display SNone = SAny
      display (SList s) = SList (display s)
      display s = s
      mode True _ = ModeIn
      mode False True = ModeOut
      mode False False = ModeInOut
   in prog1 {progPreds = Map.map finish (progPreds prog1)}

-- ─── GOAL STRUCTURE ──────────────────────────────────────────────────────────

-- | All atomic goals that may run when a body goal runs (control constructs
-- and goal-taking builtins are looked through).
subGoals :: Term -> [Term]
subGoals g = case g of
  Compound "," [a, b] -> subGoals a ++ subGoals b
  Compound ";" [a, b] -> subGoals a ++ subGoals b
  Compound "->" [a, b] -> subGoals a ++ subGoals b
  Compound "not" [a] -> subGoals a
  Compound "once" [a] -> subGoals a
  Compound "forall" [a, b] -> subGoals a ++ subGoals b
  Compound "findall" [_, a, _] -> subGoals a
  Compound "minimize" [_, a] -> subGoals a
  _ -> [g]

bodyGoals :: Clause -> [Term]
bodyGoals = concatMap subGoals . clauseBody

impureBuiltins :: [String]
impureBuiltins = ["write", "writeln", "print", "nl", "emit", "read_file", "phrase_from_file", "assert", "retract", "retractall"]

isUserCall :: Program -> Term -> Maybe PredKey
isUserCall prog t = case functorOf t of
  Just k | isJust (lookupPred k prog) -> Just k
  _ -> Nothing

-- ─── RECURSION AND PURITY ────────────────────────────────────────────────────

markGraphFacts :: Program -> Program
markGraphFacts prog =
  let preds = programPreds prog
      callees :: Map PredKey [PredKey]
      callees =
        Map.fromList
          [ (predKey p, nub (mapMaybe (isUserCall prog) (concatMap bodyGoals (IM.elems (predClauses p)))))
          | p <- preds
          ]
      reachable k = go Set.empty (Map.findWithDefault [] k callees)
        where
          go seen [] = seen
          go seen (x : xs)
            | Set.member x seen = go seen xs
            | otherwise = go (Set.insert x seen) (Map.findWithDefault [] x callees ++ xs)
      recursive k = Set.member k (reachable k)
      directlyImpure p =
        any
          (\g -> maybe False (\name -> name `elem` impureBuiltins || nameHasFlag prog name FlagDynamic) (fst <$> functorOf g))
          (concatMap bodyGoals (IM.elems (predClauses p)))
      impure0 = Set.fromList [predKey p | p <- preds, directlyImpure p]
      closeImpure imp =
        let imp' = Set.union imp (Set.fromList [predKey p | p <- preds, any (`Set.member` imp) (Map.findWithDefault [] (predKey p) callees)])
         in if imp' == imp then imp else closeImpure imp'
      impure = closeImpure impure0
      mark p =
        p
          { predRecursive = recursive (predKey p),
            predPure = not (Set.member (predKey p) impure),
            predStructural = structurallyRecursive p,
            predCounterLoop = selfOnly (predKey p) && counterLoop p,
            predGuardedCounter = selfOnly (predKey p) && counterLoop p && guardExclusive p,
            predDistinctCounter = selfOnly (predKey p) && counterLoop p && distinctCounterGenerator p
          }
      -- No other predicate on a cycle through this one: mutual recursion
      -- stays under the general rule.
      selfOnly k = recursive k && all (\c -> c == k || not (Set.member k (reachable c))) (Map.findWithDefault [] k callees)
   in prog {progPreds = Map.map mark (progPreds prog)}

-- | A counter-driven loop: at least one clause recurses; in every clause the
-- only self-call (if any) is the last top-level body goal and occurs nowhere
-- else in the body; and for each such call there is an argument position
-- where the head has a variable @V@, the call has a variable @V1@, and a
-- top-level body goal is @V1 is V - c@, @V1 is V + c@ or @V1 is c + V@ with
-- a positive integer literal @c@. Determinism is checked separately.
counterLoop :: Pred -> Bool
counterLoop p = any recurses cls && all ok cls
  where
    key = predKey p
    cls = IM.elems (predClauses p)
    isSelf g = functorOf g == Just key
    recurses cl = any isSelf (bodyGoals cl)
    ok cl
      | not (recurses cl) = True
      | otherwise = case reverse (clauseBody cl) of
          lastGoal@(Compound _ callArgs) : _
            | isSelf lastGoal,
              length (filter isSelf (bodyGoals cl)) == 1,
              Compound _ headArgs <- clauseHead cl ->
                or (zipWith (stepped (clauseBody cl)) headArgs callArgs)
          _ -> False
    stepped body (Var v) (Var w) = any (step v w) body
    stepped _ _ _ = False
    step v w g = case g of
      Compound "is" [Var w', Compound op [Var v', IntLit c]]
        | w' == w, v' == v, op `elem` ["minus", "plus"], c > 0 -> True
      Compound "is" [Var w', Compound "plus" [IntLit c, Var v']]
        | w' == w, v' == v, c > 0 -> True
      _ -> False

-- | Clause selection on the counter is mutually exclusive: exactly one clause
-- recurses; at a counter position @i@ of that clause (head variable @V@
-- stepped into the self-call) every other clause has a distinct integer
-- literal, and the recursive clause has a top-level guard @V > k@, @V >= k@,
-- @V < k@ or @V <= k@ that every one of those literals fails. So for an
-- integer counter at most one clause applies at each step.
guardExclusive :: Pred -> Bool
guardExclusive p = case partition recurses (IM.elems (predClauses p)) of
  ([rc], bases)
    | Compound _ headArgs <- clauseHead rc,
      lastGoal@(Compound _ callArgs) : _ <- reverse (clauseBody rc),
      functorOf lastGoal == Just key ->
        or [ exclusive rc v (baseLits i bases)
           | (i, Var v, Var w) <- zip3 [0 :: Int ..] headArgs callArgs, any (isStep v w) (clauseBody rc) ]
  _ -> False
  where
    key = predKey p
    recurses cl = any (\g -> functorOf g == Just key) (bodyGoals cl)
    isStep v w g = case g of
      Compound "is" [Var w', Compound op [Var v', IntLit c]] -> w' == w && v' == v && op `elem` ["minus", "plus"] && c > 0
      Compound "is" [Var w', Compound "plus" [IntLit c, Var v']] -> w' == w && v' == v && c > 0
      _ -> False
    baseLits i bases = mapM (lit i) bases
    lit i cl = case clauseHead cl of
      Compound _ hs | i < length hs, IntLit b <- hs !! i -> Just b
      _ -> Nothing
    exclusive _ _ Nothing = False
    exclusive rc v (Just bs) = nub bs == bs && any (guards v bs) (clauseBody rc)
    guards v bs g = case g of
      Compound op [Var v', IntLit k] | v' == v -> case op of
        "gt" -> all (<= k) bs
        "gte" -> all (< k) bs
        "lt" -> all (>= k) bs
        "lte" -> all (> k) bs
        _ -> False
      _ -> False

-- | A nondeterministic counter generator whose untabled answers are exactly
-- the tabled ones, in the same multiplicity, and finitely many (the
-- @between/3@ shape). All of these hold:
--
-- * exactly two clauses: one base clause and one recursive clause;
-- * every body goal of both, except the recursive clause's last goal (the
--   self-call), is an arithmetic comparison (@<@, @>@, @<=@, @>=@) or, in the
--   recursive clause only, an @is@ goal;
-- * the recursive clause steps a counter: head position @i@ holds variable
--   @V@, the self-call holds @V1@, and @V1 is V + c@ (or @c + V@) with a
--   positive literal @c@ and a guard @V < B@ / @V <= B@ (or, for
--   @V1 is V - c@, @V > B@ / @V >= B@), where @B@ is an integer literal or a
--   variable passed unchanged at the same position to the self-call;
-- * an output position @j /= i@: the recursive clause has a variable there
--   that it passes unchanged to the self-call and uses nowhere else, and
--   the base clause has the same variable at @j@ as at @i@.
--
-- Every answer of a call is then the counter value of the base clause at
-- some depth, at position @j@; the counter moves strictly in one direction
-- (integers are unbounded), so the answers at different depths differ and
-- each depth gives at most one; and the guard ends the recursion at the
-- bound. Edge case: a float counter beyond 2^53 does not move under @+ c@,
-- and then the untabled loop runs forever where a table would stop at the
-- repeated variant.
distinctCounterGenerator :: Pred -> Bool
distinctCounterGenerator p = case partition recurses (IM.elems (predClauses p)) of
  ([rc], [bc])
    | Compound _ rHead <- clauseHead rc,
      Compound _ bHead <- clauseHead bc,
      lastGoal@(Compound _ callArgs) : before <- reverse (clauseBody rc),
      functorOf lastGoal == Just key,
      all (\g -> isCmp g || isIs g) before,
      all isCmp (clauseBody bc),
      length rHead == length callArgs,
      length bHead == length rHead ->
        or
          [ True
          | (i, Var v, Var w) <- zip3 [0 :: Int ..] rHead callArgs,
            dir <- [d | g <- before, Just d <- [stepDir v w g]],
            any (bounded dir v rHead callArgs) before,
            (j, Var x, Var x') <- zip3 [0 :: Int ..] rHead callArgs,
            j /= i,
            x == x',
            length (filter (== x) (concatMap termVarIds (rHead ++ callArgs ++ before))) == 2,
            Var bi <- [bHead !! i],
            Var bj <- [bHead !! j],
            bi == bj
          ]
  _ -> False
  where
    key = predKey p
    recurses cl = any (\g -> functorOf g == Just key) (bodyGoals cl)
    isCmp g = case g of
      Compound op [_, _] -> op `elem` ["gt", "lt", "gte", "lte"]
      _ -> False
    isIs g = case g of
      Compound "is" [_, _] -> True
      _ -> False
    stepDir v w g = case g of
      Compound "is" [Var w', Compound "plus" [Var v', IntLit c]] | w' == w, v' == v, c > 0 -> Just Up
      Compound "is" [Var w', Compound "plus" [IntLit c, Var v']] | w' == w, v' == v, c > 0 -> Just Up
      Compound "is" [Var w', Compound "minus" [Var v', IntLit c]] | w' == w, v' == v, c > 0 -> Just Down
      _ -> Nothing
    bounded dir v hs cs g = case g of
      Compound op [Var v', b] | v' == v, invariant b -> case dir of
        Up -> op `elem` ["lt", "lte"]
        Down -> op `elem` ["gt", "gte"]
      Compound op [b, Var v'] | v' == v, invariant b -> case dir of
        Up -> op `elem` ["gt", "gte"]
        Down -> op `elem` ["lt", "lte"]
      _ -> False
      where
        invariant (IntLit _) = True
        invariant (Var b) = b /= v && or [h == Var b && c == Var b | (h, c) <- zip hs cs]
        invariant _ = False

data StepDir = Up | Down

-- | Every direct self-call passes, at some argument position, a variable that
-- is a proper subterm of the head argument at that position.
structurallyRecursive :: Pred -> Bool
structurallyRecursive p =
  not (null selfCalls) && all structural selfCalls
  where
    selfCalls =
      [ (headArgs cl, as)
      | cl <- IM.elems (predClauses p),
        g@(Compound _ as) <- bodyGoals cl,
        functorOf g == Just (predKey p)
      ]
    headArgs cl = case clauseHead cl of
      Compound _ hs -> hs
      _ -> []
    structural (hs, as) = or (zipWith descends hs as)
    descends h (Var v) = case h of
      Compound _ _ -> v `elem` termVarIds h
      _ -> False
    descends _ _ = False

-- ─── SORT INFERENCE ──────────────────────────────────────────────────────────

joinSort :: Sort -> Sort -> Sort
joinSort SNone x = x
joinSort x SNone = x
joinSort a b
  | a == b = a
joinSort SInt SFloat = SNum
joinSort SFloat SInt = SNum
joinSort SInt SNum = SNum
joinSort SNum SInt = SNum
joinSort SFloat SNum = SNum
joinSort SNum SFloat = SNum
joinSort (SList a) (SList b) = capList (SList (joinSort a b))
joinSort _ _ = SAny

capList :: Sort -> Sort
capList = go (3 :: Int)
  where
    go 0 (SList _) = SAny
    go n (SList s) = SList (go (n - 1) s)
    go _ s = s

type SortEnv = Map PredKey [Sort]

type VarEv = IntMap Sort

evAdd :: VarId -> Sort -> VarEv -> VarEv
evAdd v s = IM.insertWith joinSort v s

evOf :: VarEv -> VarId -> Sort
evOf ev v = IM.findWithDefault SNone v ev

-- Sort of a term given variable evidence.
termSort :: VarEv -> Term -> Sort
termSort ev t = case t of
  Var v -> evOf ev v
  Atom "nil" -> SList SNone
  Atom _ -> SAtom
  IntLit _ -> SInt
  FloatLit _ -> SFloat
  CharLit _ -> SChar
  StrLit _ -> SStr
  Compound "cons" [h, tl] ->
    let hs = termSort ev h
        ts = termSort ev tl
     in case ts of
          SList e -> capList (SList (joinSort hs e))
          SNone -> capList (SList hs)
          _ -> SAny
  Compound _ _ -> SAny

-- Push a known sort into a pattern, adding evidence for its variables.
patternEvidence :: Term -> Sort -> VarEv -> VarEv
patternEvidence t s ev = case (t, s) of
  (Var v, _) | s /= SNone -> evAdd v s ev
  (Compound "cons" [h, tl], SList e) -> patternEvidence tl (SList e) (patternEvidence h e ev)
  _ -> ev

-- Sort of an arithmetic expression.
exprSort :: VarEv -> Term -> Sort
exprSort ev t = case t of
  IntLit _ -> SInt
  FloatLit _ -> SFloat
  Var v -> case evOf ev v of
    SInt -> SInt
    SFloat -> SFloat
    _ -> SNum
  Compound "div" [_, _] -> SNum
  Compound f as | f `elem` ["plus", "minus", "mul", "mod", "^", "neg", "abs", "min", "max"] ->
    let ss = map (exprSort ev) as
     in if all (== SInt) ss then SInt else if all (== SFloat) ss then SFloat else SNum
  _ -> SNum

builtinSorts :: Map (String, Int) [Sort]
builtinSorts =
  Map.fromList
    [ (("str_concat", 3), [SStr, SStr, SStr]),
      (("str_length", 2), [SStr, SInt]),
      (("str_chars", 2), [SStr, SList SChar]),
      (("str_atom", 2), [SStr, SAtom]),
      (("str_num", 2), [SStr, SNum]),
      (("str_upper", 2), [SStr, SStr]),
      (("str_lower", 2), [SStr, SStr]),
      (("label", 1), [SList SInt]),
      (("labeling", 1), [SList SInt]),
      (("all_different", 1), [SList SInt]),
      (("all_distinct", 1), [SList SInt])
    ]

clauseVarEvidence :: SortEnv -> Clause -> VarEv
clauseVarEvidence env cl = iterate pass IM.empty !! 3
  where
    goals = bodyGoals cl
    pass ev0 = foldl' goalEv ev0 goals

    goalEv ev g = case g of
      Compound "is" [l, r] ->
        let s = exprSort ev r
         in arithVars r (patternEvidence l s ev)
      Compound op [a, b]
        | op `elem` ["gt", "lt", "gte", "lte"] -> arithVars a (arithVars b ev)
        | op `elem` ["int_eq", "fd_ne", "fd_lt", "fd_gt", "fd_le", "fd_ge"] -> intVars a (intVars b ev)
      Compound "in" [x, _] -> intVars x ev
      Compound "reify" [relation, truth] -> intVars truth (goalEv ev relation)
      Compound "unify" [a, b] ->
        let ev1 = patternEvidence a (termSort ev b) ev
         in patternEvidence b (termSort ev1 a) ev1
      Compound "findall" [tmpl, _, l] -> patternEvidence l (capList (SList (termSort ev tmpl))) ev
      _ -> case functorOf g of
        Just k
          | Just ss <- Map.lookup k builtinSorts -> foldl' (\e (a, s) -> patternEvidence a s e) ev (zip (args g) ss)
          | Just ss <- Map.lookup k env -> foldl' (\e (a, s) -> patternEvidence a s e) ev (zip (args g) ss)
        _ -> ev

    args (Compound _ as) = as
    args _ = []

    arithVars t ev = foldl' (\e v -> evAdd v SNum e) ev (termVarIds t)
    intVars t ev = foldl' (\e v -> evAdd v SInt e) ev (termVarIds t)

inferSorts :: Program -> SortEnv
inferSorts prog = go (10 :: Int) env0
  where
    preds = programPreds prog
    env0 = Map.fromList [(predKey p, replicate (snd (predKey p)) SNone) | p <- preds]
    go 0 env = env
    go n env =
      let env' = Map.fromList [(predKey p, predSorts env p) | p <- preds]
       in if env' == env then env else go (n - 1) env'
    predSorts env p =
      let arity = snd (predKey p)
          perClause cl =
            let ev = clauseVarEvidence env cl
             in case clauseHead cl of
                  Compound _ as -> map (termSort ev) as
                  _ -> []
          rows = map perClause (IM.elems (predClauses p))
       in [foldl' joinSort SNone [row !! i | row <- rows, i < length row] | i <- [0 .. arity - 1]]

-- ─── MODE INFERENCE ──────────────────────────────────────────────────────────

type ModeEnv = Map PredKey [Bool]

type DeclEnv = Map PredKey [Signature]

declaredSignatures :: Program -> DeclEnv
declaredSignatures prog = Map.fromList
  [(predKey p, predDecls p) | p <- programPreds prog, not (null (predDecls p))]

-- The runtime selects the first mode whose inputs are ground. An earlier
-- mode whose inputs are not *known* ground can still be eligible at runtime.
-- Include every candidate up to the first definitely eligible signature.
possibleSignatures :: Set VarId -> [Term] -> [Signature] -> [Signature]
possibleSignatures _ _ [] = []
possibleSignatures known as (sig : rest) = sig :
  if and [all (`Set.member` known) (termVarIds a)
         | (ArgSpec _ ModeIn, a) <- zip (sigArgs sig) as]
    then [] else possibleSignatures known as rest

-- A single displayed signature can promise only modes common to every
-- alternative. Call-site analysis below retains the individual signatures.
declaredModes :: Program -> Map PredKey ([Bool], [Bool])
declaredModes prog =
  Map.fromList
    [ (predKey p, (common ModeIn sigs, common ModeOut sigs))
    | p <- programPreds prog,
      let sigs = predDecls p, not (null sigs)
    ]
  where
    common mode sigs = foldl1 (zipWith (&&))
      [map ((== mode) . argMode) (sigArgs sig) | sig <- sigs]

-- Head variables that are the sole content of an argument position.
plainHeadVars :: Clause -> [(Int, VarId)]
plainHeadVars cl = case clauseHead cl of
  Compound _ as -> [(i, v) | (i, Var v) <- zip [0 ..] as]
  _ -> []

-- | First plain head position of each head variable.  A variable that
-- occupies several positions (@max2 A B A@) charges its requirements to the
-- first one; the others are then outputs by aliasing.
firstPlainPos :: Clause -> Map VarId Int
firstPlainPos cl = Map.fromListWith (\_ old -> old) [(v, i) | (i, v) <- plainHeadVars cl]

-- | Paths at which each variable occurs in the head: the argument index
-- followed by subterm indices, in order of occurrence.
headPaths :: Clause -> Map VarId [[Int]]
headPaths cl = case clauseHead cl of
  Compound _ as -> Map.fromListWith (flip (++)) (concat [walk [i] a | (i, a) <- zip [0 ..] as])
  _ -> Map.empty
  where
    walk path t = case t of
      Var v -> [(v, [reverse path])]
      Compound _ xs -> concat [walk (j : path) x | (j, x) <- zip [0 ..] xs]
      _ -> []

termAtPath :: [Term] -> [Int] -> Maybe Term
termAtPath as (i : rest)
  | i < length as = go (as !! i) rest
  | otherwise = Nothing
  where
    go t [] = Just t
    go (Compound _ xs) (j : js) | j < length xs = go (xs !! j) js
    go _ _ = Nothing
termAtPath _ [] = Nothing

-- | Input modes (least fixpoint): a position is input when some clause needs
-- it ground before a goal is known to have grounded it. Requirements are
-- conservative hints, especially for predicates with several relational modes.
inferInModes :: Program -> ModeEnv
inferInModes prog = go env0
  where
    preds = programPreds prog
    decl = declaredModes prog
    signatures = declaredSignatures prog
    env0 = Map.fromList [(predKey p, replicate (snd (predKey p)) False) | p <- preds]
    go env =
      let (outs, deps) = inferGroundness prog env
          transfer = groundAfter signatures env outs deps
          found = Map.fromList [(predKey p, predIns env transfer p) | p <- preds]
          env' = Map.unionWith (zipWith (||)) env found
       in if env' == env then env else go env'
    predIns env transfer p = case Map.lookup (predKey p) decl of
      Just (ins, _) -> ins
      Nothing ->
        let arity = snd (predKey p)
            needed = Set.unions [clauseNeeds env transfer cl | cl <- IM.elems (predClauses p)]
         in [i `Set.member` needed | i <- [0 .. arity - 1]]

    clauseNeeds env transfer cl =
      let (required, _) = goalsNeeds env transfer Set.empty (clauseBody cl)
          owners = Map.union (firstPlainPos cl)
            (Map.map (\paths -> minimum [i | (i : _) <- paths]) (headPaths cl))
       in Set.fromList [i | (v, i) <- Map.toList owners, v `Set.member` required]

    goalsNeeds env transfer = foldl' (\(req, known) g ->
      let (needed, next) = goalNeeds env transfer known g
       in (Set.union req needed, next)) . (,) Set.empty

    -- Track definite grounding on each branch. A constraint or an alias
    -- between two unknowns does not discharge a later arithmetic input.
    goalNeeds env transfer known g = case g of
      Compound "," [a, b] -> goalsNeeds env transfer known [a, b]
      Compound ";" [Compound "->" [c, t], e] -> branches [Compound "," [c, t], e]
      Compound ";" [a, b] -> branches [a, b]
      Compound "->" [c, t] -> goalsNeeds env transfer known [c, t]
      Compound "once" [a] -> goalNeeds env transfer known a
      Compound "minimize" [_, a] -> goalNeeds env transfer known a
      Compound "not" [a] -> let (req, _) = goalNeeds env transfer known a in (req, known)
      Compound "forall" [a, b] -> let (req, _) = goalsNeeds env transfer known [a, b] in (req, known)
      Compound "findall" [_, a, _] -> let (req, _) = goalNeeds env transfer known a in (req, known)
      _ ->
        let needs = case g of
              Compound "is" [_, r] -> termVarIds r
              Compound op [a, b] | op `elem` ["gt", "lt", "gte", "lte"] -> termVarIds a ++ termVarIds b
              Compound f as | Just pins <- Map.lookup (f, length as) env ->
                concat [termVarIds a | (a, True) <- zip as pins]
              _ -> []
            required = Set.difference (Set.fromList needs) known
            assumed = Set.union known required
         in (required, transfer assumed g)
      where
        branches gs =
          let results = map (goalNeeds env transfer known) gs
           in (Set.unions (map fst results), foldl1 Set.intersection (map snd results))

groundingBuiltins :: [String]
groundingBuiltins =
  [ "str_concat", "str_length", "str_chars", "str_atom", "str_num", "str_upper", "str_lower",
    "ground"
  ]

-- | Variables known to be ground after a goal succeeds, given the variables
-- known ground before it.  A callee's output positions count when its input
-- positions are known ground at the call; its dependent positions count when
-- every other argument is known ground.
groundAfter :: DeclEnv -> ModeEnv -> ModeEnv -> ModeEnv -> Set VarId -> Term -> Set VarId
groundAfter signatures ins outs deps = go
  where
    go known g = case g of
      Compound "," [a, b] -> go (go known a) b
      Compound ";" [Compound "->" [c, t], e] -> Set.intersection (go (go known c) t) (go known e)
      Compound ";" [a, b] -> Set.intersection (go known a) (go known b)
      Compound "->" [c, t] -> go (go known c) t
      Compound "once" [a] -> go known a
      Compound "minimize" [_, a] -> go known a
      Compound "is" [l, r] -> add known [l, r]
      Compound op [a, b]
        | op `elem` ["gt", "lt", "gte", "lte"] -> add known [a, b]
        | op `elem` ["unify", "equiv"] ->
            if allKnown known a then add known [b] else if allKnown known b then add known [a] else known
      Compound name [l] | name `elem` ["label", "labeling"] ->
        -- One-argument labeling enumerates the visible prefix; it does not
        -- instantiate an unknown list or the tail of an open list.
        add known (fst (unfoldCons l))
      Compound "labeling" [options, l] -> add known [options, l]
      _ -> case (functorOf g, g) of
        (Just (name, _), Compound _ as)
          | name `elem` groundingBuiltins -> add known as
        (Just k, Compound _ as) ->
          case Map.lookup k signatures of
            Just sigs ->
              let guarantees sig = Set.fromList (concat
                    [termVarIds a | (ArgSpec _ mode, a) <- zip (sigArgs sig) as,
                     mode `elem` [ModeIn, ModeOut]])
               in Set.union known (foldl1 Set.intersection
                    (map guarantees (possibleSignatures known as sigs)))
            Nothing ->
              let is = Map.findWithDefault [] k ins
                  os = Map.findWithDefault [] k outs
                  ds = Map.findWithDefault [] k deps
                  viaOuts
                    | and [allKnown known a | (a, True) <- zip as is] = [a | (a, True) <- zip as os]
                    | otherwise = []
                  viaDeps =
                    [ a
                    | (j, a, True) <- zip3 [0 :: Int ..] as ds,
                      and [allKnown known b | (i, b) <- zip [0 ..] as, i /= j]
                    ]
              in add known (viaOuts ++ viaDeps)
        _ -> known
    add known ts = foldl' (\k t -> Set.union k (Set.fromList (termVarIds t))) known ts
    allKnown known t = all (`Set.member` known) (termVarIds t)

-- | Output modes and dependent outputs (joint greatest fixpoint).
--
-- * output: the position is ground after success whenever the input
--   positions were ground at the call;
-- * dependent: the position is ground after success whenever every other
--   argument was ground at the call.
--
-- Declared predicates use their declared outputs for both.
inferGroundness :: Program -> ModeEnv -> (ModeEnv, ModeEnv)
inferGroundness prog ins = go (env0, env0)
  where
    preds = programPreds prog
    decl = declaredModes prog
    signatures = declaredSignatures prog
    env0 = Map.fromList [(predKey p, initial p) | p <- preds]
    initial p = case Map.lookup (predKey p) decl of
      Just (_, outs) -> outs
      Nothing -> replicate (snd (predKey p)) (not (IM.null (predClauses p)))
    go envs =
      let outs' = Map.fromList [(predKey p, predOuts envs p) | p <- preds]
          deps' = Map.fromList [(predKey p, predDeps envs p) | p <- preds]
       in if (outs', deps') == envs then envs else go (outs', deps')
    arityOf p = snd (predKey p)
    predOuts (outs, deps) p = case Map.lookup (predKey p) decl of
      Just (_, os) -> os
      Nothing ->
        let pins = Map.findWithDefault [] (predKey p) ins
            rows = [clauseGround outs deps (\i -> i < length pins && pins !! i) cl | cl <- IM.elems (predClauses p)]
         in [not (null rows) && all (!! i) rows | i <- [0 .. arityOf p - 1]]
    predDeps (outs, deps) p = case Map.lookup (predKey p) decl of
      Just (_, os) -> os
      Nothing ->
        [ not (IM.null (predClauses p))
            && all (\cl -> clauseGround outs deps (/= j) cl !! j) (IM.elems (predClauses p))
        | j <- [0 .. arityOf p - 1]
        ]
    -- Which head arguments are ground after the clause succeeds, assuming the
    -- arguments selected by @assumed@ were ground at the call.
    clauseGround outs deps assumed cl =
      let hs = case clauseHead cl of Compound _ as -> as; _ -> []
          g0 = Set.fromList (concat [termVarIds a | (i, a) <- zip [0 ..] hs, assumed i])
          ordered = foldl' (groundAfter signatures ins outs deps) g0 (clauseBody cl)
          -- Aliasing persists after later bindings. Close only unifications;
          -- replaying calls could apply guarantees with inputs grounded later.
          aliases g = foldl' aliasAfter g (clauseBody cl)
          gEnd = stable aliases ordered
       in [all (`Set.member` gEnd) (termVarIds a) | a <- hs]
    stable f g = let g' = f g in if g' == g then g else stable f g'
    aliasAfter known g = case g of
      Compound op [a, b] | op `elem` ["unify", "equiv"] ->
        groundAfter signatures Map.empty Map.empty Map.empty known (Compound op [a, b])
      Compound "," [a, b] -> aliasAfter (aliasAfter known a) b
      Compound ";" [Compound "->" [c, t], e] ->
        Set.intersection (aliasAfter (aliasAfter known c) t) (aliasAfter known e)
      Compound ";" [a, b] -> Set.intersection (aliasAfter known a) (aliasAfter known b)
      Compound "->" [c, t] -> aliasAfter (aliasAfter known c) t
      Compound "once" [a] -> aliasAfter known a
      Compound "minimize" [_, a] -> aliasAfter known a
      _ -> known

-- ─── DETERMINISM INFERENCE ───────────────────────────────────────────────────

-- | Determinism of builtins (Nothing = not a builtin).
builtinDet :: String -> Int -> Maybe Det
builtinDet name arity = case (name, arity) of
  ("true", 0) -> Just Det
  ("fail", 0) -> Just Semidet
  ("false", 0) -> Just Semidet
  ("nl", 0) -> Just Det
  ("!", 0) -> Just Det
  ("$cut", 1) -> Just Det
  ("write", 1) -> Just Det
  ("writeln", 1) -> Just Det
  ("print", 1) -> Just Det
  ("unify", 2) -> Just Semidet
  ("equiv", 2) -> Just Semidet
  ("neq", 2) -> Just Semidet
  ("is", 2) -> Just Semidet
  ("gt", 2) -> Just Semidet
  ("lt", 2) -> Just Semidet
  ("gte", 2) -> Just Semidet
  ("lte", 2) -> Just Semidet
  ("int_eq", 2) -> Just Semidet
  ("fd_ne", 2) -> Just Semidet
  ("fd_lt", 2) -> Just Semidet
  ("fd_gt", 2) -> Just Semidet
  ("fd_le", 2) -> Just Semidet
  ("fd_ge", 2) -> Just Semidet
  ("in", 2) -> Just Semidet
  ("reify", 2) -> Just Semidet
  ("all_different", 1) -> Just Semidet
  ("all_distinct", 1) -> Just Semidet
  ("label", 1) -> Just Nondet
  ("labeling", 1) -> Just Nondet
  ("labeling", 2) -> Just Semidet
  ("minimize", 2) -> Just Semidet
  ("not", 1) -> Just Semidet
  ("once", 1) -> Just Semidet
  ("forall", 2) -> Just Semidet
  ("findall", 3) -> Just Det
  ("call", _) -> Just Nondet
  ("phrase", 2) -> Just Nondet
  ("var", 1) -> Just Semidet
  ("nonvar", 1) -> Just Semidet
  ("ground", 1) -> Just Semidet
  ("is_int", 1) -> Just Semidet
  ("is_float", 1) -> Just Semidet
  ("is_num", 1) -> Just Semidet
  ("is_str", 1) -> Just Semidet
  ("is_atom", 1) -> Just Semidet
  ("is_char", 1) -> Just Semidet
  ("is_list", 1) -> Just Semidet
  ("str_concat", 3) -> Just Nondet
  ("str_length", 2) -> Just Semidet
  ("str_chars", 2) -> Just Semidet
  ("str_atom", 2) -> Just Semidet
  ("str_num", 2) -> Just Semidet
  ("str_upper", 2) -> Just Semidet
  ("str_lower", 2) -> Just Semidet
  ("term_str", 2) -> Just Semidet
  ("char_code", 2) -> Just Semidet
  ("str_lines", 2) -> Just Semidet
  -- pure DCG helpers (two extra list arguments)
  ("seq", 3) -> Just Nondet
  ("wr", 3) -> Just Semidet
  ("nl", 2) -> Just Semidet
  ("sp", 2) -> Just Semidet
  ("fmt", 4) -> Just Semidet
  ("padl", 4) -> Just Semidet
  ("padr", 4) -> Just Semidet
  -- effects (require an unsafe declaration)
  ("emit", 1) -> Just Semidet
  ("read_file", 2) -> Just Semidet
  ("phrase_from_file", 2) -> Just Nondet
  ("assert", 1) -> Just Det
  ("retract", 1) -> Just Nondet
  ("retractall", 1) -> Just Det
  _ -> Nothing

type DetEnv = Map PredKey (Det, [Int])

conj :: Det -> Det -> Det
conj Det Det = Det
conj a b
  | a `elem` [Nondet, Multi] || b `elem` [Nondet, Multi] = Nondet
  | otherwise = Semidet

capSemidet :: Det -> Det
capSemidet Det = Det
capSemidet _ = Semidet

atMostOne :: Det -> Bool
atMostOne d = d == Det || d == Semidet

-- Orderings a guard admits between its two operands.
data Ordering' = OLT | OEQ | OGT deriving (Eq, Ord, Show)

flipO :: Ordering' -> Ordering'
flipO OLT = OGT
flipO OGT = OLT
flipO OEQ = OEQ

-- A guard operand: a head variable, identified by every path at which it
-- occurs in the head, a literal, or an arithmetic expression over operands.
data GuardOperand = VarPaths [[Int]] | Lit Term | Expr String [GuardOperand] deriving (Eq, Show)

data GuardKind = TermIdentity | ValueOrdering deriving (Eq)

type Guard = (GuardOperand, GuardOperand, Set Ordering', GuardKind)

-- | The constraints a clause's leading arithmetic goals place on its head
-- variables: comparisons between head variables, literals and expressions,
-- and @is@ goals whose left side is a literal or a head variable. An @is@
-- into a fresh body variable defines that variable as its expression for
-- the goals that follow. The prefix ends at the first other goal.
--
-- Term identity and value ordering have different equivalence classes
-- (integer 1 and float 1.0 are distinct terms, and @is@ unifies its result
-- by identity: @0 is 0.0@ fails), but a term identical to a literal has
-- that literal's value, so an identity equality is also a value equality.
guardsOf :: Clause -> [Guard]
guardsOf cl = go Map.empty (clauseBody cl)
  where
    paths = headPaths cl
    go defs goals = case goals of
      Compound "is" [lhs, rhs] : rest
        | Just e <- operand defs rhs -> case lhs of
            Var v
              | Map.notMember v paths, Map.notMember v defs -> go (Map.insert v e defs) rest
            _ | Just l <- operand defs lhs -> equality l e ++ go defs rest
            _ -> []
      Compound op [a, b] : rest
        | Just rels <- relOf op,
          Just x <- operand defs a,
          Just y <- operand defs b ->
            if op `elem` ["neq", "equiv"]
              then (x, y, rels, TermIdentity) : [g | rels == Set.singleton OEQ, g <- equality x y] ++ go defs rest
              else (x, y, rels, ValueOrdering) : go defs rest
      _ -> []
    equality x y = [(x, y, Set.singleton OEQ, TermIdentity), (x, y, Set.singleton OEQ, ValueOrdering)]
    operand defs t = case t of
      Var v -> case Map.lookup v defs of
        Just e -> Just e
        Nothing -> VarPaths <$> Map.lookup v paths
      Compound op xs | op `elem` arithOps -> Expr op <$> mapM (operand defs) xs
      _ | isLit t -> Just (Lit t)
      _ -> Nothing
    isLit t = case t of
      IntLit _ -> True
      FloatLit _ -> True
      Atom _ -> True
      StrLit _ -> True
      CharLit _ -> True
      _ -> False
    relOf op = case op of
      "gt" -> Just (Set.fromList [OGT])
      "lt" -> Just (Set.fromList [OLT])
      "gte" -> Just (Set.fromList [OGT, OEQ])
      "lte" -> Just (Set.fromList [OLT, OEQ])
      "equiv" -> Just (Set.fromList [OEQ])
      "neq" -> Just (Set.fromList [OLT, OGT])
      _ -> Nothing

-- | When do two guard operands denote the same call-time value?  Returns the
-- argument positions that must be ground for that to hold.
--
-- * the same literal: always;
-- * variables sharing a head path: only when the argument containing that
--   path is ground. Aliases among query arguments can otherwise let the two
--   clause heads bind the same variable to different values before the guard;
-- * the same operation over compatible operands: when every operand's
--   requirement holds (arithmetic is a function of its ground inputs).
compatibleOperands :: GuardOperand -> GuardOperand -> Maybe [Int]
compatibleOperands (Lit a) (Lit b) = if a == b then Just [] else Nothing
compatibleOperands (VarPaths p) (VarPaths q) =
    case [i | path@(i : _) <- p, path `elem` q] of
      (i : _) -> Just [i]
      [] -> Nothing
compatibleOperands (Expr f xs) (Expr g ys)
  | f == g && length xs == length ys = nub . concat <$> zipWithM compatibleOperands xs ys
compatibleOperands _ _ = Nothing

-- | Does a ground call argument distinguish the two head patterns?  True when
-- the patterns carry different principal functors at some common path.
distinctPatterns :: Int -> Term -> Term -> Bool
distinctPatterns depth a b = case (indexKey a, indexKey b) of
  (Just ka, Just kb)
    | ka /= kb -> True
    | depth > 0, Compound _ xs <- a, Compound _ ys <- b -> or (zipWith (distinctPatterns (depth - 1)) xs ys)
  _ -> False

-- | Are two clauses mutually exclusive?  Returns the argument positions that
-- must be ground at call time for the exclusivity to hold.  When several
-- justifications exist, the one with the fewest (and earliest) required
-- positions is chosen.
exclusive :: Clause -> Clause -> Maybe [Int]
exclusive c1 c2 = case options of
  [] -> Nothing
  _ -> Just (snd (minimum [(rank o, o) | o <- options]))
  where
    rank o = (length o, sum o)
    options =
      [[i] | i <- switchPositions]
        ++ guardOption
        ++ typeGuardOption
        ++ literalVsGuard c1 c2
        ++ literalVsGuard c2 c1
    -- Any guard of one clause against any guard of the other, in every
    -- orientation: both hold when their clauses succeed, so one
    -- contradiction excludes the pair.
    guardOption =
      [ o
        | g1 <- guardsOf c1,
          g2 <- guardsOf c2 ++ repeatGuards c2,
          a <- [g1, swapGuard g1],
          b <- [g2, swapGuard g2],
          o <- maybe [] pure (contradiction a b)
      ]
    -- Type guards (is_int, is_atom, is_char, is_float, is_str) and negated
    -- type guards on head variables against head constructors/literals or
    -- another clause's type guards at the same path.
    typeGuardOption =
      let (hf1, pos1, neg1) = clauseTypeFacts c1
          (hf2, pos2, neg2) = clauseTypeFacts c2
       in [ [i]
          | (p@(i : _), t1) <- pos1,
            any (\(q, t2) -> p == q && t1 /= t2) (hf2 ++ pos2)
              || (p, t1) `elem` neg2
          ]
            ++ [ [i]
               | (p@(i : _), t2) <- pos2,
                 any (\(q, t1) -> p == q && t1 /= t2) hf1
                   || (p, t2) `elem` neg1
               ]
            ++ [ [i]
               | (p@(i : _), t1) <- hf1,
                 (p, t1) `elem` neg2
               ]
            ++ [ [i]
               | (p@(i : _), t2) <- hf2,
                 (p, t2) `elem` neg1
               ]
    clauseTypeFacts cl =
      let hps = headPaths cl
          headFacts = concat [walkHead [i] a | (i, a) <- zip [0 ..] (args cl)]
          walkHead path t = case t of
            Var _ -> []
            IntLit _ -> [(reverse path, "int")]
            FloatLit _ -> [(reverse path, "float")]
            Atom _ -> [(reverse path, "atom")]
            CharLit _ -> [(reverse path, "char")]
            StrLit _ -> [(reverse path, "str")]
            Compound f xs ->
              (reverse path, "struct")
                : [ fact
                  | f `notElem` arithOps,
                    (j, x) <- zip [0 ..] xs,
                    fact <- walkHead (j : path) x
                  ]
          leadTypeGuards [] = ([], [])
          leadTypeGuards (g : gs) = case g of
            Compound op [Var v]
              | Just tag <- typeGuardTag op,
                Just ps <- Map.lookup v hps ->
                  let (pRest, nRest) = leadTypeGuards gs
                   in ([(p, tag) | p <- ps] ++ pRest, nRest)
            Compound "not" [Compound op [Var v]]
              | Just tag <- typeGuardTag op,
                Just ps <- Map.lookup v hps ->
                  let (pRest, nRest) = leadTypeGuards gs
                   in (pRest, [(p, tag) | p <- ps] ++ nRest)
            Compound op _
              | op `elem` ["is", "gt", "lt", "gte", "lte", "equiv", "neq", "ground", "nonvar", "var"] ->
                  leadTypeGuards gs
            Atom "true" -> leadTypeGuards gs
            _ -> ([], [])
          typeGuardTag op = case op of
            "is_int" -> Just "int"
            "is_float" -> Just "float"
            "is_atom" -> Just "atom"
            "is_char" -> Just "char"
            "is_str" -> Just "str"
            _ -> Nothing
          (posG, negG) = leadTypeGuards (clauseBody cl)
       in (headFacts, posG, negG)
    args (Clause (Compound _ as) _ _) = as
    args _ = []
    switchPositions =
      [i | (i, (a, b)) <- zip [0 ..] (zip (args c1) (args c2)), distinctPatterns 3 a b]
    -- c1 has a literal where c2 has a variable (occurring only there) guarded
    -- by a comparison against a literal that excludes c1's.
    literalVsGuard lit gd =
      [[i] | (x, y, rels, kind) <- guardsOf gd, Just i <- [excluded kind x y rels]]
      where
        excluded kind (VarPaths [p]) (Lit l) rels = check kind p l rels
        excluded kind (Lit l) (VarPaths [p]) rels = check kind p l (Set.map flipO rels)
        excluded _ _ _ _ = Nothing
        check kind p@(i : _) l rels
          | Just t <- termAtPath (args lit) p,
            Just o <- compareLits kind t l,
            not (o `Set.member` rels) =
              Just i
        check _ _ _ _ = Nothing

-- | A head variable at two or more paths equates the terms there: for
-- example @ins K V (t K _ L R) _@ requires the key at argument 0 to be the
-- one at path 2.0. Identical terms also compare equal, so this is recorded
-- as a value equality, which a comparison guard such as @K < K0@ in another
-- clause contradicts.
--
-- 'exclusive' uses these for the later clause of a pair only. When the
-- comparison clause comes first, it runs first: for terms it cannot
-- compare it raises its error before the repeated-variable clause is
-- reached, and committing after its success cannot skip an answer. In the
-- other order (@range N N [N]@ before @range I N _ <- I < N@), committing
-- after the first clause would hide the error the second raises for equal
-- non-numbers, so that pair stays non-exclusive.
repeatGuards :: Clause -> [Guard]
repeatGuards cl =
  [ (VarPaths ps, VarPaths ps, Set.singleton OEQ, ValueOrdering)
    | ps <- Map.elems (headPaths cl),
      length ps > 1
  ]

swapGuard :: Guard -> Guard
swapGuard (x, y, rels, kind) = (y, x, Set.map flipO rels, kind)

-- | Can the two guards not hold together? Their left operands must denote
-- the same value; their right operands are either the same value with
-- disjoint orderings, or two literals that the orderings keep apart.
-- Returns the positions that must be ground for the contradiction to hold.
contradiction :: Guard -> Guard -> Maybe [Int]
contradiction (x1, y1, r1, kind1) (x2, y2, r2, kind2)
  | kind1 /= kind2 = Nothing
  | otherwise = do
      px <- compatibleOperands x1 x2
      py <- apart
      pure (nub (px ++ py))
  where
    apart
      | Just py <- compatibleOperands y1 y2 = if Set.null (Set.intersection r1 r2) then Just py else Nothing
      | Lit a <- y1, Lit b <- y2, Just o <- compareLits kind1 a b = if jointlySat r1 r2 o then Nothing else Just []
      | otherwise = Nothing

-- | Can @e r1 a@ and @e r2 b@ hold together, given the ordering @o@ of
-- @a@ against @b@? Every position of @e@ relative to the two literals is
-- tried, and a position strictly between them is assumed to exist.
jointlySat :: Set Ordering' -> Set Ordering' -> Ordering' -> Bool
jointlySat r1 r2 o = or [Set.member p1 r1 && Set.member p2 r2 | (p1, p2) <- positions]
  where
    positions = case o of
      OEQ -> [(p, p) | p <- [OLT, OEQ, OGT]]
      OLT -> [(OLT, OLT), (OEQ, OLT), (OGT, OLT), (OGT, OEQ), (OGT, OGT)]
      OGT -> [(OLT, OLT), (OLT, OEQ), (OLT, OGT), (OEQ, OGT), (OGT, OGT)]

-- | The ordering of one literal relative to another under a guard kind:
-- identity tells equal from different only; value ordering compares
-- numbers numerically and atoms, strings and characters lexically.
compareLits :: GuardKind -> Term -> Term -> Maybe Ordering'
compareLits TermIdentity a b
  | null (termVarIds a) = Just (if a == b then OEQ else OLT)
  | otherwise = Nothing
compareLits ValueOrdering a b = case (a, b) of
  (Atom p, Atom q) -> Just (ordOf (compare p q))
  (StrLit p, StrLit q) -> Just (ordOf (compare p q))
  (CharLit p, CharLit q) -> Just (ordOf (compare p q))
  _ -> case (evalNumeric IM.empty a, evalNumeric IM.empty b) of
    (Right (Just p), Right (Just q)) -> Just (ordOf (compareNumeric p q))
    _ -> Nothing
  where
    ordOf LT = OLT
    ordOf EQ = OEQ
    ordOf GT = OGT

hasCut :: Clause -> Bool
hasCut cl = any isCut (clauseBody cl)
  where
    isCut (Atom "!") = True
    isCut _ = False

-- | Are a predicate's clauses pairwise exclusive, and which argument
-- positions must be ground for that (the union, in order of first
-- appearance over the pairs, of each pair's 'exclusive' positions)?
--
-- The general case checks every pair, which is quadratic: 2000 facts took
-- most of a second to load. Fact tables usually take 'atomicSwitch''s
-- linear path, which gives the same answer.
pairwiseExclusivity :: [Clause] -> (Bool, [Int])
pairwiseExclusivity cls
  | Just r <- atomicSwitch cls = r
  | otherwise = (ok, sw)
  where
    pairs = [(a, b) | (i, a) <- zip [0 :: Int ..] cls, (j, b) <- zip [0 ..] cls, i < j]
    ok = all (\(a, b) -> hasCut a || isJust (exclusive a b)) pairs
    sw = if ok then nub (concat (mapMaybe (\(a, b) -> if hasCut a then Just [] else exclusive a b) pairs)) else []

-- | The linear case of 'pairwiseExclusivity': no clause has a cut or a
-- guard (so 'exclusive' can only use 'distinctPatterns'), and for some
-- position @p@ every head argument at positions @0 .. p@ is atomic (its
-- 'indexKey' is not a functor), with pairwise different keys at @p@. Then
-- every pair is exclusive, and a pair's 'exclusive' result is its first
-- position with different keys, which is at most @p@. Position @k@ is in
-- the union when two clauses agree on @0 .. k-1@ and differ at @k@; the
-- union is ordered by each position's first pair in (i, j) order.
atomicSwitch :: [Clause] -> Maybe (Bool, [Int])
atomicSwitch cls
  | length cls < 2 = Nothing
  | any hasCut cls || any (not . null . guardsOf) cls = Nothing
  | otherwise = do
      rows <- mapM headKeys cls
      let width = minimum (map length rows)
          atomicUpTo = length (takeWhile (\k -> all (atomicAt k) rows) [0 .. width - 1])
          distinctAt k = let ks = map (!! k) rows in Set.size (Set.fromList ks) == length ks
      p <- case filter distinctAt [0 .. atomicUpTo - 1] of
        (p : _) -> Just p
        [] -> Nothing
      let indexed = zip [0 :: Int ..] rows
          firstPair k =
            -- groups agreeing on 0 .. k-1, in clause order
            let groups = Map.elems (Map.fromListWith (flip (++)) [(take k r, [(i, r !! k)]) | (i, r) <- indexed])
                candidates = concatMap pairIn groups
             in if null candidates then Nothing else Just (minimum candidates)
          -- the (i, j)-least pair in a group with different keys
          pairIn grp = case grp of
            ((i, ki) : rest) -> case [j | (j, kj) <- rest, kj /= ki] of
              (j : _) -> [(i, j)]
              [] -> pairIn rest
            [] -> []
          found = [(fp, k) | k <- [0 .. p], Just fp <- [firstPair k]]
      pure (True, map snd (sortOn fst found))
  where
    headKeys (Clause (Compound _ as) _ _) = Just (map indexKey as)
    headKeys _ = Nothing
    atomicAt k r = case r !! k of
      Just (IKFun _ _) -> False
      Just _ -> True
      Nothing -> False

inferDets :: Program -> ModeEnv -> ModeEnv -> ModeEnv -> DetEnv
inferDets prog ins outs deps = go env0
  where
    preds = programPreds prog
    signatures = declaredSignatures prog
    after = groundAfter signatures ins outs deps
    declared p = case predDecls p of
      [] -> Nothing
      sigs -> Just (declarationsDet sigs)
    declarationsDet sigs
      | all ((== Det) . sigDet) sigs = Det
      | all (atMostOne . sigDet) sigs = Semidet
      | otherwise = Nondet
    env0 = Map.fromList [(predKey p, initial p) | p <- preds]
    initial p = case declared p of
      Just d -> (d, [])
      Nothing -> case pairwise p of
        (True, sw) -> (Semidet, sw)
        (False, _) -> (Nondet, [])
    -- Pairwise exclusivity depends only on the clauses, so it is computed
    -- once per predicate, not on every fixpoint round. A predicate that
    -- starts Nondet stays Nondet, exactly as 'step' would make it.
    pairInfo = Map.fromList [(predKey p, pairwiseExclusivity (IM.elems (predClauses p))) | p <- preds]
    pairwise p = Map.findWithDefault (False, []) (predKey p) pairInfo
    pairwiseOK p = fst (pairwise p)

    go env =
      let env' = Map.fromList [(predKey p, step env p) | p <- preds]
       in if env' == env then env else go env'

    step env p = case declared p of
      Just d -> (d, [])
      Nothing ->
        let (cur, sw) = fromMaybe (Nondet, []) (Map.lookup (predKey p) env)
         in if cur == Nondet
              then (Nondet, [])
              else
                if pairwiseOK p && all (\cl -> atMostOne (clauseDet env sw cl)) (IM.elems (predClauses p))
                  then (Semidet, sw)
                  else (Nondet, [])

    clauseDet env sw cl =
      let known0 = Set.fromList (concat [termVarIds a | (i, a) <- zip [0 ..] (args cl), i `elem` sw])
          (pre, post) = break isCutGoal (clauseBody cl)
          (dPre, known1) = goalsDet env known0 pre
          (dPost, _) = goalsDet env known1 (drop 1 post)
       in if null post then dPre else conj (capSemidet dPre) dPost
    args (Clause (Compound _ as) _ _) = as
    args _ = []
    isCutGoal (Atom "!") = True
    isCutGoal _ = False

    goalsDet env known gs = foldl' (\(d, kn) g -> (conj d (goalDet env kn g), after kn g)) (Det, known) gs

    -- Determinism of one goal given the variables known ground before it.
    goalDet :: DetEnv -> Set VarId -> Term -> Det
    goalDet env known g = case g of
      Compound "," [a, b] -> conj (goalDet env known a) (goalDet env (after known a) b)
      Compound ";" [Compound "->" [c, t], e] ->
        let dc = goalDet env known c
            dt = goalDet env (after known c) t
            de = goalDet env known e
         in if atMostOne dc && atMostOne dt && atMostOne de
              then (if dt == Det && de == Det && dc == Det then Det else Semidet)
              else Nondet
      Compound ";" [_, _] -> Nondet
      Compound "->" [c, t] ->
        let dc = goalDet env known c
            dt = goalDet env (after known c) t
         in if atMostOne dc && atMostOne dt then Semidet else Nondet
      Atom "!" -> Det
      _ -> case functorOf g of
        Just (name, arity)
          | Just d <- builtinDet name arity -> d
          | Just sigs <- Map.lookup (name, arity) signatures ->
              let as = case g of Compound _ xs -> xs; _ -> []
               in declarationsDet (possibleSignatures known as sigs)
          | Just (d, sw) <- Map.lookup (name, arity) env ->
              let as = case g of Compound _ xs -> xs; _ -> []
                  groundAt i = i < length as && all (`Set.member` known) (termVarIds (as !! i))
               in if all groundAt sw then d else Nondet
        _ -> Nondet

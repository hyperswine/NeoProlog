{-# OPTIONS_GHC -Wno-name-shadowing #-}

-- | Static inference of sorts, modes and determinism, plus the call-graph
-- facts (recursion, purity) used to decide default tabling.
--
-- Inferred signatures are advisory: the engine only uses the inferred
-- determinism (together with its 'sigSwitch' positions) to drop choice points,
-- and that analysis is sound by construction.  Declared signatures are
-- enforced at runtime.
module Infera.Infer
  ( inferProgram,
    subGoals,
    builtinDet,
    impureBuiltins,
  )
where

import Data.IntMap.Strict (IntMap)
import qualified Data.IntMap.Strict as IM
import Data.List (foldl', nub)
import Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map
import Data.Maybe (fromMaybe, isJust, mapMaybe)
import Data.Set (Set)
import qualified Data.Set as Set
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
impureBuiltins = ["write", "writeln", "print", "nl"]

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
          (\g -> maybe False (`elem` impureBuiltins) (fst <$> functorOf g))
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
            predStructural = structurallyRecursive p
          }
   in prog {progPreds = Map.map mark (progPreds prog)}

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

-- Modes fixed by a predicate's (first) declaration: (inputs, outputs).  Both
-- are enforced at runtime, so the analyses may trust them.
declaredModes :: Program -> Map PredKey ([Bool], [Bool])
declaredModes prog =
  Map.fromList
    [ (predKey p, (map ((== ModeIn) . argMode) (sigArgs s), map ((== ModeOut) . argMode) (sigArgs s)))
    | p <- programPreds prog,
      (s : _) <- [predDecls p]
    ]

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
-- it ground before any goal could have bound it.
inferInModes :: Program -> ModeEnv
inferInModes prog = go (10 :: Int) env0
  where
    preds = programPreds prog
    decl = declaredModes prog
    env0 = Map.fromList [(predKey p, replicate (snd (predKey p)) False) | p <- preds]
    go 0 env = env
    go n env =
      let env' = Map.fromList [(predKey p, predIns env p) | p <- preds]
       in if env' == env then env else go (n - 1) env'
    predIns env p = case Map.lookup (predKey p) decl of
      Just (ins, _) -> ins
      Nothing ->
        let arity = snd (predKey p)
            needed = Set.unions [clauseNeeds env cl | cl <- IM.elems (predClauses p)]
         in [i `Set.member` needed | i <- [0 .. arity - 1]]

    clauseNeeds env cl =
      let required = requiredVars env (bodyGoals cl) Set.empty Set.empty
       in Set.fromList [i | (v, i) <- Map.toList (firstPlainPos cl), v `Set.member` required]

    -- Walk goals in order; @bound@ are vars that may have been bound already.
    requiredVars _ [] _ req = req
    requiredVars env (g : gs) bound req =
      let (needs, binds) = goalNeeds env g
          req' = Set.union req (Set.fromList [v | v <- needs, not (v `Set.member` bound)])
          bound' = Set.union bound (Set.fromList (needs ++ binds))
       in requiredVars env gs bound' req'

    -- (variables that must be ground, variables that may become bound)
    goalNeeds env g = case g of
      Compound "is" [l, r] -> (termVarIds r, termVarIds l)
      Compound op [a, b]
        | op `elem` ["gt", "lt", "gte", "lte"] -> (termVarIds a ++ termVarIds b, [])
        | op `elem` ["unify", "int_eq", "fd_ne", "fd_lt", "fd_gt", "fd_le", "fd_ge", "in", "equiv", "neq"] -> ([], termVarIds a ++ termVarIds b)
      Compound "write" [_] -> ([], [])
      _ -> case (functorOf g, g) of
        (Just k, Compound _ as)
          | Just ins <- Map.lookup k env ->
              ( concat [termVarIds a | (a, True) <- zip as ins],
                concat [termVarIds a | (a, False) <- zip as ins]
              )
        _ -> ([], termVarIds g)

groundingBuiltins :: [String]
groundingBuiltins =
  [ "str_concat", "str_length", "str_chars", "str_atom", "str_num", "str_upper", "str_lower",
    "ground", "label", "labeling"
  ]

-- | Variables known to be ground after a goal succeeds, given the variables
-- known ground before it.  A callee's output positions count when its input
-- positions are known ground at the call; its dependent positions count when
-- every other argument is known ground.
groundAfter :: ModeEnv -> ModeEnv -> ModeEnv -> Set VarId -> Term -> Set VarId
groundAfter ins outs deps = go
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
      _ -> case (functorOf g, g) of
        (Just (name, _), Compound _ as)
          | name `elem` groundingBuiltins -> add known as
        (Just k, Compound _ as) ->
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
inferGroundness prog ins = go (10 :: Int) (env0, env0)
  where
    preds = programPreds prog
    decl = declaredModes prog
    env0 = Map.fromList [(predKey p, initial p) | p <- preds]
    initial p = case Map.lookup (predKey p) decl of
      Just (_, outs) -> outs
      Nothing -> replicate (snd (predKey p)) (not (IM.null (predClauses p)))
    go 0 envs = envs
    go n envs =
      let outs' = Map.fromList [(predKey p, predOuts envs p) | p <- preds]
          deps' = Map.fromList [(predKey p, predDeps envs p) | p <- preds]
       in if (outs', deps') == envs then envs else go (n - 1) (outs', deps')
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
          step g = foldl' (groundAfter ins outs deps) g (clauseBody cl)
          gEnd = stable (3 :: Int) step g0
       in [all (`Set.member` gEnd) (termVarIds a) | a <- hs]
    stable 0 _ g = g
    stable n f g = let g' = f g in if g' == g then g else stable (n - 1) f g'

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
-- occurs in the head, or a literal.
data GuardOperand = VarPaths [[Int]] | Lit Term deriving (Eq, Show)

-- | The first body goal when it is a comparison between head variables and
-- literals: (left operand, right operand, admitted orderings, needs ground).
-- @needs ground@ marks == and != guards, which do not fail on unbound
-- variables and therefore only exclude when their arguments are ground.
guardOf :: Clause -> Maybe (GuardOperand, GuardOperand, Set Ordering', Bool)
guardOf cl = case clauseBody cl of
  (Compound op [a, b] : _)
    | Just rels <- relOf op -> do
        x <- operand a
        y <- operand b
        pure (x, y, rels, op `elem` ["neq", "equiv"])
  _ -> Nothing
  where
    paths = headPaths cl
    operand t = case t of
      Var v -> VarPaths <$> Map.lookup v paths
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
-- * variables where one head path set includes the other: always, because
--   the clause with the smaller set only evaluates its guard once one of
--   those paths is bound in the call, and the other clause's variable is
--   unified with that same subterm;
-- * variables sharing a head path: when the argument containing that path
--   is ground, so both clauses read the same subterm.
compatibleOperands :: GuardOperand -> GuardOperand -> Maybe [Int]
compatibleOperands (Lit a) (Lit b) = if a == b then Just [] else Nothing
compatibleOperands (VarPaths p) (VarPaths q)
  | subset p q || subset q p = Just []
  | otherwise = case [i | path@(i : _) <- p, path `elem` q] of
      (i : _) -> Just [i]
      [] -> Nothing
  where
    subset xs ys = all (`elem` ys) xs
compatibleOperands _ _ = Nothing

operandArgs :: GuardOperand -> [Int]
operandArgs (VarPaths ps) = [i | (i : _) <- ps]
operandArgs (Lit _) = []

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
        ++ maybe [] pure (literalVsGuard c1 c2)
        ++ maybe [] pure (literalVsGuard c2 c1)
    guardOption = case (guardOf c1, guardOf c2) of
      (Just (x1, y1, r1, ng1), Just (x2, y2, r2, ng2)) ->
        let groundAll = if ng1 || ng2 then concatMap operandArgs [x1, y1, x2, y2] else []
            option rx ry disjoint = do
              px <- rx
              py <- ry
              if disjoint then Just (nub (groundAll ++ px ++ py)) else Nothing
            same = option (compatibleOperands x1 x2) (compatibleOperands y1 y2) (Set.null (Set.intersection r1 r2))
            swapped = option (compatibleOperands x1 y2) (compatibleOperands y1 x2) (Set.null (Set.intersection r1 (Set.map flipO r2)))
         in maybe [] pure same ++ maybe [] pure swapped
      _ -> []
    args (Clause (Compound _ as) _ _) = as
    args _ = []
    switchPositions =
      [i | (i, (a, b)) <- zip [0 ..] (zip (args c1) (args c2)), distinctPatterns 3 a b]
    -- c1 has a literal where c2 has a variable (occurring only there) guarded
    -- by a comparison against a literal that excludes c1's.
    literalVsGuard lit gd = case guardOf gd of
      Just (x, y, rels, ng)
        | Just i <- excluded x y rels ->
            Just (if ng then [i] else [])
      _ -> Nothing
      where
        excluded (VarPaths [p]) (Lit l) rels = check p l rels
        excluded (Lit l) (VarPaths [p]) rels = check p l (Set.map flipO rels)
        excluded _ _ _ = Nothing
        check p@(i : _) l rels
          | Just t <- termAtPath (args lit) p,
            Just o <- compareLits t l,
            not (o `Set.member` rels) =
              Just i
        check _ _ _ = Nothing
        -- ordering of the head literal relative to the guard literal
        compareLits a b = case (a, b) of
          (IntLit p, IntLit q) -> Just (ordOf (compare p q))
          (IntLit p, FloatLit q) -> Just (ordOf (compare (fromIntegral p) q))
          (FloatLit p, IntLit q) -> Just (ordOf (compare p (fromIntegral q)))
          (FloatLit p, FloatLit q) -> Just (ordOf (compare p q))
          _ | a == b -> Just OEQ
            | isAtomic a && isAtomic b -> Just OLT -- distinct non-numeric literals: only != can exclude
            | otherwise -> Nothing
        ordOf LT = OLT
        ordOf EQ = OEQ
        ordOf GT = OGT
        isAtomic t = case t of
          Atom _ -> True
          StrLit _ -> True
          CharLit _ -> True
          _ -> False

hasCut :: Clause -> Bool
hasCut cl = any isCut (clauseBody cl)
  where
    isCut (Atom "!") = True
    isCut _ = False

inferDets :: Program -> ModeEnv -> ModeEnv -> ModeEnv -> DetEnv
inferDets prog ins outs deps = go env0
  where
    preds = programPreds prog
    after = groundAfter ins outs deps
    declared p = case predDecls p of
      (s : _) -> Just (sigDet s)
      [] -> Nothing
    env0 = Map.fromList [(predKey p, initial p) | p <- preds]
    initial p = case declared p of
      Just d -> (d, [])
      Nothing -> (Semidet, switchOf p)
    -- Positions required ground for pairwise exclusivity (union over pairs).
    switchOf p =
      let cls = IM.elems (predClauses p)
          pairs = [(a, b) | (i, a) <- zip [0 :: Int ..] cls, (j, b) <- zip [0 ..] cls, i < j]
       in nub (concat (mapMaybe (\(a, b) -> if hasCut a then Just [] else exclusive a b) pairs))
    pairwiseOK p =
      let cls = IM.elems (predClauses p)
          pairs = [(a, b) | (i, a) <- zip [0 :: Int ..] cls, (j, b) <- zip [0 ..] cls, i < j]
       in all (\(a, b) -> hasCut a || isJust (exclusive a b)) pairs

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
          | Just (d, sw) <- Map.lookup (name, arity) env ->
              let as = case g of Compound _ xs -> xs; _ -> []
                  groundAt i = i < length as && all (`Set.member` known) (termVarIds (as !! i))
               in if all groundAt sw then d else Nondet
        _ -> Nondet

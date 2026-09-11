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
      outs = inferOutModes prog1 ins
      dets = inferDets prog1
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

-- Head variables that are the sole content of an argument position.
plainHeadVars :: Clause -> [(Int, VarId)]
plainHeadVars cl = case clauseHead cl of
  Compound _ as -> [(i, v) | (i, Var v) <- zip [0 ..] as]
  _ -> []

-- | Input modes (least fixpoint): a position is input when some clause needs
-- it ground before any goal could have bound it.
inferInModes :: Program -> ModeEnv
inferInModes prog = go (10 :: Int) env0
  where
    preds = programPreds prog
    env0 = Map.fromList [(predKey p, replicate (snd (predKey p)) False) | p <- preds]
    go 0 env = env
    go n env =
      let env' = Map.fromList [(predKey p, predIns env p) | p <- preds]
       in if env' == env then env else go (n - 1) env'
    predIns env p =
      let arity = snd (predKey p)
          needed = Set.unions [clauseNeeds env cl | cl <- IM.elems (predClauses p)]
       in [i `Set.member` needed | i <- [0 .. arity - 1]]

    clauseNeeds env cl =
      let hv = plainHeadVars cl
          required = requiredVars env (bodyGoals cl) Set.empty Set.empty
       in Set.fromList [i | (i, v) <- hv, v `Set.member` required]

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

-- | Output modes (advisory): a position is output when every clause either
-- has a ground term there or a plain variable produced by the body.
inferOutModes :: Program -> ModeEnv -> ModeEnv
inferOutModes prog ins = go (10 :: Int) env0
  where
    preds = programPreds prog
    env0 = Map.fromList [(predKey p, replicate (snd (predKey p)) False) | p <- preds]
    go 0 env = env
    go n env =
      let env' = Map.fromList [(predKey p, predOuts env p) | p <- preds]
       in if env' == env then env else go (n - 1) env'
    predOuts env p =
      let arity = snd (predKey p)
          rows = [clauseOuts env cl | cl <- IM.elems (predClauses p)]
       in [not (null rows) && all (!! i) rows | i <- [0 .. arity - 1]]
    clauseOuts env cl =
      let produced = Set.fromList (concatMap (producedBy env) (bodyGoals cl))
          available = Set.fromList [v | (i, v) <- plainHeadVars cl, inAt (clauseHead cl) i]
          ok t = case t of
            Var v -> v `Set.member` produced
            Compound _ as -> all (\a -> case a of Var v -> v `Set.member` produced || v `Set.member` available; _ -> ok a) as
            _ -> True
       in case clauseHead cl of
            Compound _ as -> map ok as
            _ -> []
    inAt hd i = case functorOf hd of
      Just k -> maybe False (\bs -> i < length bs && bs !! i) (Map.lookup k ins)
      Nothing -> False
    producedBy env g = case g of
      Compound "is" [l, _] -> termVarIds l
      Compound "unify" [Var v, t] | notVar t -> [v]
      Compound "unify" [t, Var v] | notVar t -> [v]
      Compound "findall" [_, _, l] -> termVarIds l
      _ -> case (functorOf g, g) of
        (Just k, Compound _ as)
          | Just outs <- Map.lookup k env -> concat [termVarIds a | (a, True) <- zip as outs]
        _ -> []
    notVar (Var _) = False
    notVar _ = True

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

-- A guard on canonical operands: variables are replaced by their head
-- position (@PosArg i@), literals stay.
data GuardOperand = PosArg Int | Lit Term deriving (Eq, Ord, Show)

guardOf :: Clause -> Maybe (GuardOperand, GuardOperand, Set Ordering', Bool)
guardOf cl = case clauseBody cl of
  (Compound op [a, b] : _)
    | Just rels <- relOf op -> do
        x <- operand a
        y <- operand b
        let needsGround = op `elem` ["neq", "equiv"]
        pure (orient x y rels needsGround)
  _ -> Nothing
  where
    -- first position at which a variable is the whole head argument
    positions = Map.fromListWith (\_ old -> old) [(v, i) | (i, v) <- plainHeadVars cl]
    operand t = case t of
      Var v -> PosArg <$> Map.lookup v positions
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
    orient x y rels ng
      | x <= y = (x, y, rels, ng)
      | otherwise = (y, x, Set.map flipO rels, ng)
    flipO OLT = OGT
    flipO OGT = OLT
    flipO OEQ = OEQ

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
      (Just (x1, y1, r1, ng1), Just (x2, y2, r2, ng2))
        | x1 == x2 && y1 == y2 && Set.null (Set.intersection r1 r2) ->
            [if ng1 || ng2 then operandPositions [x1, y1] else []]
      _ -> []
    args (Clause (Compound _ as) _ _) = as
    args _ = []
    switchPositions =
      [ i
      | (i, (a, b)) <- zip [0 ..] (zip (args c1) (args c2)),
        Just ka <- [indexKey a],
        Just kb <- [indexKey b],
        ka /= kb
      ]
    operandPositions ops = [i | PosArg i <- ops]
    -- c1 has a literal at position i; c2 has a plain variable there guarded
    -- by a comparison against the same literal that excludes equality.
    literalVsGuard lit gd = case guardOf gd of
      Just (x, y, rels, ng)
        | Just i <- excluded x y rels ->
            Just (if ng then [i] else [])
      _ -> Nothing
      where
        -- position i of the literal clause is excluded by the guard on the
        -- variable clause when the guard cannot hold for that literal
        excluded (PosArg i) (Lit l) rels = check i l rels
        excluded (Lit l) (PosArg i) rels = check i l (Set.map flipO rels)
        excluded _ _ _ = Nothing
        flipO OLT = OGT
        flipO OGT = OLT
        flipO OEQ = OEQ
        check i l rels
          | i < length (args lit),
            Just o <- compareLits (args lit !! i) l,
            not (o `Set.member` rels) =
              Just i
          | otherwise = Nothing
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

inferDets :: Program -> DetEnv
inferDets prog = go env0
  where
    preds = programPreds prog
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

    goalsDet env known gs = foldl' (\(d, kn) g -> let (d', kn') = goalDet env kn g in (conj d d', kn')) (Det, known) gs

    goalDet :: DetEnv -> Set VarId -> Term -> (Det, Set VarId)
    goalDet env known g = case g of
      Compound "," [a, b] ->
        let (da, k1) = goalDet env known a
            (db, k2) = goalDet env k1 b
         in (conj da db, k2)
      Compound ";" [Compound "->" [c, t], e] ->
        let (dc, kc) = goalDet env known c
            (dt, _) = goalDet env kc t
            (de, _) = goalDet env known e
            d = if atMostOne dc && atMostOne dt && atMostOne de then (if dt == Det && de == Det && dc == Det then Det else Semidet) else Nondet
         in (d, known)
      Compound ";" [_, _] -> (Nondet, known)
      Compound "->" [c, t] ->
        let (dc, kc) = goalDet env known c
            (dt, _) = goalDet env kc t
         in (if atMostOne dc && atMostOne dt then Semidet else Nondet, known)
      Compound "is" [l, _] -> (Semidet, Set.union known (Set.fromList (termVarIds l)))
      Atom "!" -> (Det, known)
      _ -> case functorOf g of
        Just (name, arity)
          | Just d <- builtinDet name arity -> (d, known)
          | Just (d, sw) <- Map.lookup (name, arity) env ->
              let as = case g of Compound _ xs -> xs; _ -> []
                  groundAt i = i < length as && all (`Set.member` known) (termVarIds (as !! i))
               in if all groundAt sw then (d, known) else (Nondet, known)
        _ -> (Nondet, known)

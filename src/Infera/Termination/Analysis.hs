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
-- Supported norms are term size, list length, bounded linear integer values,
-- pair sums and guard differences. Verified successful-answer relations carry
-- size and groundness through callees. Proof search is deliberately incomplete:
-- a rejected candidate yields a warning, never an assumed termination proof.
module Infera.Termination.Analysis
  ( Verdict (..),
    Proof (..),
    verdictsWith,
    CallSite (..), callSites, calledPredicates,
    hasMeasure,
    renderVerdict,
    verdictStatus,
  )
where

import Data.Graph (SCC (..), stronglyConnComp)
import Data.List (foldl', nub, zip3, isSuffixOf)
import qualified Data.IntMap.Strict as IM
import Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map
import Data.Maybe (isJust)
import Data.Set (Set)
import qualified Data.Set as Set
import Infera.Error (showPredKey)
import Infera.Program
import Infera.Syntax

-- | A proof that a recursive predicate's calls always end.
data Proof = Proof
  { -- | Alternative conditions: the recursion ends when every position
    -- (1-based) of at least one of these sets is ground at the call.
    proofConditions :: [[Int]],
    -- | The predicate calls a closure it was given, so its calls end only
    -- when that closure's calls do.
    proofClosures :: Bool,
    -- Integer-norm proofs additionally require these positions to be integers.
    proofIntegers :: [[Int]],
    proofReason :: String
  }
  deriving (Eq, Show)

data Verdict
  = -- | The predicate cannot reach itself.
    NotRecursive
  | Total Proof
  | TotalByTable
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
  TotalByTable -> "total-tabled"
  Unproven _ -> "unproven"
  Reactive -> "reactive"

renderVerdict :: Verdict -> String
renderVerdict v = case v of
  NotRecursive -> "not recursive"
  Reactive -> "reactive: an io loop that runs while the world feeds it"
  Unproven why -> "recursion not proven total: " ++ why
  TotalByTable -> "total by tabling over a finite ground domain"
  Total (Proof conds closures ints reason) ->
    "total when "
      ++ joinWith " or " ([condition cs ++ integerCondition ns | (cs,ns)<-zip conds ints])
      ++ " (" ++ reason ++ ")"
      ++ (if closures then ", given that its closure arguments and invoked attribute hooks are total" else "")
  where
    integerCondition [] = ""
    integerCondition ns = "; integer arguments " ++ joinWith ", " (map show ns)
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
      Compound ";" [Compound "->" [c, t], e] -> inner dom c ++ go (dom ++ definite c) [t] ++ go (dom ++ opposite c) [e]
      Compound ";" [a, b] -> inner dom a ++ inner dom b
      Compound "->" [c, t] -> inner dom c ++ go (dom ++ definite c) [t]
      Compound "not" [a] -> inner dom a
      Compound "once" [a] -> inner dom a
      Compound "forall" [a, b] -> inner dom a ++ go (dom ++ definite a) [b]
      Compound "findall" [_, a, _] -> inner dom a
      Compound f [_, a, _] | f `elem` ["bagof", "setof", "std_native_bagof", "std_native_setof"] -> inner dom (strip a)
      Compound "minimize" [_, a] -> inner dom a
      _ -> [(g, dom)]
    opposite (Compound op as) = case lookup op [("lt","gte"),("lte","gt"),("gt","lte"),("gte","lt")] of
      Just inverse->[Compound inverse as]
      _->[]
    opposite _=[]
    definite g = case g of
      Compound "," [a, b] -> definite a ++ definite b
      Compound "once" [a] -> definite a
      Compound "->" [a, b] -> definite a ++ definite b
      Compound ";" _ -> []
      Compound "not" _ -> []
      Compound "forall" _ -> []
      Compound "findall" _ -> [g]
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
    user k captured = CallUser k (map Just captured ++ extra)

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
                [ mk dom g (closureTarget prog hs c n (metaArguments prog k i args n))
                | (i, n) <- Set.toList (Map.findWithDefault Set.empty k meta),
                  i < length args,
                  let c = args !! i
                ]
           in direct : closures
        Just k -> [mk dom g (CallUser k (map Just (case g of Compound _ as -> as; _ -> [])))]
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
structuralGraph :: Deps -> Set Int -> Call -> [Maybe Term] -> (Arcs, Set Int)
structuralGraph deps rigid c args = (arcs, groundOut)
  where
    hs = callHead c
    ground = groundVars deps rigid hs (callBefore c)
    groundOut = Set.fromList [j | (j, Just a) <- zip [0 ..] args, all (`Set.member` ground) (termVarIds a)]
    arcs =
      Set.fromList
        [ (4*i, 4*j, strict)
        | (i, h) <- zip [0 ..] hs,
          Set.member i rigid,
          let (equal, smaller) = relatives h (callBefore c),
          (j, Just a) <- zip [0 ..] args,
          strict <- [True | Set.member a smaller] ++ [False | Set.member a equal, not (Set.member a smaller)]
        ]

-- | Arguments ground after a successful call when all the others were
-- ground at the call ('groundDependencies').
type RawDeps = Map PredKey [Bool]
type Deps = (RawDeps, Map PredKey [([Int], [Int])])

-- Successful-answer groundness, independently verified for each singleton
-- input mode. Greatest fixpoint is induction on finite successful derivations;
-- it makes no claim that the callee terminates.
modeDependencies :: (String -> Int -> Maybe Det) -> RawDeps -> Program -> Deps
modeDependencies builtin raw p = (ds, fixed initial)
  where
    ds = Map.filterWithKey (\(n,a) _ -> builtin n a == Nothing) raw
    ps = [q | q <- programPreds p, builtin (fst(predKey q)) (snd(predKey q)) == Nothing, not (predIsDynamic p q), not (IM.null (predClauses q))]
    positions q = [0 .. snd (predKey q)-1]
    modes q = nub ([[]] ++ [[i] | i <- positions q] ++ [positions q])
    initial = Map.fromList [(predKey q, [(ins, positions q) | ins <- modes q]) | q <- ps]
    fixed old =
      let next = Map.fromList [(predKey q, [(ins, filter (verified old q ins) outs) |
                       (ins,outs) <- Map.findWithDefault [] (predKey q) old]) | q <- ps]
      in if next == old then old else fixed next
    verified old q ins out = all clause (IM.elems (predClauses q))
      where
        clause cl = all (path cl) (successPaths (clauseBody cl))
        path cl goals =
          let hs = headArgs cl
              start = groundVars (ds,old) (Set.fromList ins) hs goals
              aliases g = foldl' (\known t -> case t of
                Compound "unify" [x,y]
                  | all (`Set.member` known) (termVarIds x) -> Set.union known (Set.fromList (termVarIds y))
                  | all (`Set.member` known) (termVarIds y) -> Set.union known (Set.fromList (termVarIds x))
                _ -> known) g goals
              close g = let next=aliases g in if next==g then g else close next
          in out < length hs && all (`Set.member` close start) (termVarIds (hs!!out))

-- | Variables certainly ground at the call: those of ground head arguments,
-- closed in order under the unifications, evaluations and calls that ran
-- before it. A call grounds argument j when its other arguments were ground
-- and the callee's dependencies say j follows from them.
groundVars :: Deps -> Set Int -> [Term] -> [Term] -> Set VarId
groundVars (deps, modes) rigid hs before = foldl' step start before
  where
    start = Set.fromList (concat [termVarIds h | (i, h) <- zip [0 ..] hs, Set.member i rigid])
    groundIn g t = all (`Set.member` g) (termVarIds t)
    step g goal = case goal of
      Compound "unify" [a, b]
        | groundIn g a -> Set.union g (Set.fromList (termVarIds b))
        | groundIn g b -> Set.union g (Set.fromList (termVarIds a))
      Compound "is" [v, e] | groundIn g e -> Set.union g (Set.fromList (termVarIds v))
      Compound "findall" [template,inner,out]
        | groundIn (step g inner) template -> Set.union g (Set.fromList(termVarIds out))
      Compound "is_int" [a] -> Set.union g (Set.fromList(termVarIds a))
      Compound f as | f `elem` ["str_chars","str_num","str_atom","str_length","char_code","gt","gte","lt","lte","std_native_between"] ->
        Set.union g (Set.fromList(concatMap termVarIds as))
      Compound f as ->
        let ds=Map.findWithDefault [] (f,length as) deps
            dependencyOutputs=[j | (j,True)<-zip[0..]ds, and[groundIn g b | (i,b)<-zip[0..]as,i/=j]]
            modeOutputs=concat [outs | (ins,outs)<-Map.findWithDefault [] (f,length as) modes,
                                 all(\i->i<length as && groundIn g(as!!i))ins]
        in Set.union g(Set.fromList(concat[termVarIds(as!!j) | j<-dependencyOutputs++modeOutputs,j<length as]))
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
closure :: [SCG] -> Maybe (Map (PredKey, PredKey, Arcs) SCG)
closure base = grow initial (Map.elems initial)
  where
    key g = (scgFrom g, scgTo g, scgArcs g)
    initial = Map.fromListWith (\_ old -> old) [(key g, g) | g <- base]
    grow known [] = Just known
    grow known _ | Map.size known > 4096 = Nothing
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

verdictsWith :: (String -> Int -> Maybe Det) -> RawDeps -> Program -> Map PredKey Verdict
verdictsWith builtin raw prog = foldl' component Map.empty sccs
  where
    deps = modeDependencies builtin raw prog
    meta = metaPositions prog
    domains = finiteDomainRelations builtin prog
    sizes = Map.filterWithKey (\(n,a) _->builtin n a==Nothing) (sizeRelations builtin prog)
    preds = [p | p <- programPreds prog, not (IM.null (predClauses p))]
    callsOf = Map.fromList [(predKey p, concat [clauseCalls prog meta ci cl | (ci,cl)<-zip [1..] (IM.elems(predClauses p))]) | p<-preds]
    calls k = Map.findWithDefault [] k callsOf
    edges k = nub [t | Call{callTarget=CallUser t _}<-calls k,Map.member t callsOf]
    sccs = stronglyConnComp [(predKey p,predKey p,edges(predKey p)) | p<-preds]
    component known scc =
      let ks=case scc of AcyclicSCC k->[k]; CyclicSCC xs->xs
          group=Set.fromList ks
          cyclic k=k `elem` edges k || length ks>1
          values=[(k,finish known group k (cyclic k)) | k<-ks]
      in Map.union (Map.fromList values) known
    finish known group k recursive
      | Just p<-lookupPred k prog, predIsDynamic prog p = Unproven "dynamic: its clauses change at run time"
      | Just p<-lookupPred k prog, FlagIo `elem` effectiveFlags prog p = Reactive
      | (c:_)<-[c | m<-Set.toList group,c<-calls m,CallOpaque<-[callTarget c]] =
          Unproven ("calls a goal built at run time in clause "++show(callClause c)++" of "++showPredKey k++", which could call back")
      | otherwise =
          let allPositions=[0..snd k-1]
              parameter=any (\m->any (\c->case callTarget c of CallParameter->True; _->False) (calls m)) (Set.toList group)
              hooks=any (isSuffixOf ":attr_unify_hook" . fst . predKey) preds
              attempt numeric positions = prove known group k (Set.fromList positions) numeric
              candidates = nub ([[]] ++ [[i] | i<-allPositions] ++ subsetsOf 2 allPositions ++ subsetsOf 3 allPositions ++ [allPositions])
              minimal numeric = foldl' (\found s -> if any (\a->all (`elem` s) a) found then found else case attempt numeric s of Right ()->found++[s]; _->found) (if numeric then structural else []) candidates
              structural=minimal False
              integers=drop (length structural) (minimal True)
              found=structural++integers
              proof=Proof (map(map(+1))found) (parameter || hooks) (replicate (length structural) [] ++ map (map(+1)) integers)
                (if null integers then "subterm/list-length size-change descent" else "structural/integer/guard-difference size-change descent")
              table=finiteTable builtin prog group
          in case found of
            _:_ | not recursive && found==[[]] && not parameter && not hooks -> NotRecursive
                | otherwise -> Total proof
            [] | recursive && table -> TotalByTable
               | otherwise -> case attempt False allPositions of Left why->Unproven why; Right ()->Unproven "no supported finite entry mode"
    prove known group entry entryRigid numeric = do
      if numeric && any (\cl->any (\i->i<length(headArgs cl) && case headArgs cl!!i of Var _->False; IntLit _->False; _->True) (Set.toList entryRigid))
             (maybe [] (IM.elems . predClauses) (lookupPred entry prog))
        then Left "integer norm requires an integer-compatible head position" else Right ()
      let rigid=groundFixpoint group entry entryRigid
          ints=if numeric then integerFixpoint group entry entryRigid else Map.empty
          graphs=[SCG m t (Set.filter (\(_,node,_)->all (`Set.member` Map.findWithDefault Set.empty t rigid) (nodePositions (snd t) node)) arcs) (m,c)
            | m<-Set.toList group,c<-calls m,CallUser t args<-[callTarget c],Set.member t group,
              let (arcs,_)=callGraph sizes (predEvalArgs <$> lookupPred t prog) deps
                    (Map.findWithDefault Set.empty m rigid) (Map.findWithDefault Set.empty m ints) c args]
          failures=[(m,c,why) | m<-Set.toList group,c<-calls m,why<-outside known group rigid ints m c]
      case failures of
        (m,c,why):_->Left ("call "++show(callGoal c)++" in clause "++show(callClause c)++" of "++showPredKey m++": "++why)
        []->pure ()
      completed<-maybe (Left "size-change graph budget exceeded; proof is conservatively unavailable") Right (closure graphs)
      case [g | m<-Set.toList group,Just g<-[violation m completed]] of
        []->Right ()
        g:_->let (m,c)=scgCall g in Left ("call "++show(callGoal c)++" in clause "++show(callClause c)++" of "++showPredKey m++": no well-founded argument norm certainly decreases; integer descent needs a preceding lower/upper guard")
    outside known group rigid ints m c = case callTarget c of
      CallOpaque->["unknown closure"]
      CallParameter->[]
      CallUser t args | Set.member t group->[]
        | otherwise ->
          let ground=groundVars deps (Map.findWithDefault Set.empty m rigid) (callHead c) (callBefore c)
              integer=integerVars (Map.findWithDefault Set.empty m ints) (callHead c) (callBefore c)
              valid proof=any (\(positions,ip)->all (groundArgument ground args . subtract 1) positions && all (integerArgument integer args . subtract 1) ip) (zip(proofConditions proof)(proofIntegers proof))
          in case if builtin (fst t) (snd t) /= Nothing then Nothing else Map.lookup t known of
            Just NotRecursive->[]
            Just TotalByTable->[]
            Just(Total p) | valid p->[]
            Just(Reactive)->["reactive io call"]
            Just _->["callee "++showPredKey t++" is not proven total in this mode"]
            Nothing | fst t `elem` ["label","labeling"], Just value <- if null args then Nothing else last args,
                      all (`Set.member` domainVars domains ground (callBefore c)) (termVarIds (expand False (callBefore c) value)) -> []
                    | builtin (fst t) (snd t) /= Nothing -> builtinFailure t ground integer args
                    | t==("length",2) -> ["length requires a bound list or bound integer length" | not(groundArgument ground args 0 || integerArgument integer args 1)]
                    | otherwise->["unknown predicate "++showPredKey t]
    groundFixpoint group entry seed = fixIncoming group entry seed (\rigid c args -> snd(structuralGraph deps rigid c args))
    integerFixpoint group entry seed = fixIncoming group entry seed (\rigid c args -> Set.fromList[j | (j,a)<-zip[0..]args,maybe False (\term -> numericActual (case callTarget c of CallUser t _->predEvalArgs <$> lookupPred t prog; _->Nothing) j term && integerTerm(integerVars rigid(callHead c)(callBefore c)) term) a])
    fixIncoming group entry seed out = go (Map.fromList[(m,if m==entry then seed else Set.fromList[0..snd m-1]) | m<-Set.toList group])
      where
        go r = let incoming=Map.fromListWith Set.intersection[(t,out (Map.findWithDefault Set.empty m r) c args) | m<-Set.toList group,c<-calls m,CallUser t args<-[callTarget c],Set.member t group]
                   next=Map.mapWithKey(\m vs->maybe vs (Set.intersection vs)(Map.lookup m incoming)) r
               in if next==r then r else go next

hasMeasure :: Verdict -> Bool
hasMeasure(Total _)=True
hasMeasure NotRecursive=True
hasMeasure _=False

groundArgument :: Set VarId -> [Maybe Term] -> Int -> Bool
groundArgument ground args i = i<length args && maybe False (all (`Set.member` ground) . termVarIds) (args!!i)
integerArgument :: Set VarId -> [Maybe Term] -> Int -> Bool
integerArgument ints args i = i<length args && maybe False (integerTerm ints) (args!!i)

builtinFailure :: PredKey -> Set VarId -> Set VarId -> [Maybe Term] -> [String]
builtinFailure (name,_) ground ints args
  | name `elem` ["repeat"] = ["unbounded builtin generator"]
  | name `elem` ["std_native_between","between"] = ["between needs bound integer limits" | not(integerArgument ints args 0 && integerArgument ints args 1)]
  | name `elem` ["label","labeling"] = ["labeling needs a verified finite CLP domain"]
  | name `elem` ["std_native_bagof","std_native_setof","aggregate_all"] = ["collection requires a statically total goal"]
  | name `elem` ["call","phrase","put_attr","freeze","when"] = ["unknown closure or attribute hook"]
  | otherwise = []

subsetsOf :: Int -> [a] -> [[a]]
subsetsOf 0 _ = [[]]
subsetsOf _ [] = []
subsetsOf n (x : xs) = map (x :) (subsetsOf (n - 1) xs) ++ subsetsOf n xs


-- ─── Verified norms and callee relations ────────────────────────────────────

data Norm = TermSize | ListLength deriving (Eq,Ord,Show)
data Expr = Expr !Integer (Map VarId Integer) deriving (Eq,Ord,Show)
plus :: Expr -> Expr -> Expr
plus (Expr a x) (Expr b y)=Expr(a+b)(Map.filter(/=0)(Map.unionWith(+) x y))
scale :: Integer -> Expr -> Expr
scale n(Expr c xs)=Expr(n*c)(Map.filter(/=0)(Map.map(*n)xs))
minus :: Expr -> Expr -> Expr
minus a b=plus a(scale (-1)b)
constant :: Integer -> Expr
constant n=Expr n Map.empty
variable :: VarId -> Expr
variable v=Expr 0(Map.singleton v 1)

-- Only dominating equalities/evaluations are substituted. A cyclic equation
-- is not an assignment and never causes the analysis itself to recurse.
expand :: Bool -> [Term] -> Term -> Term
expand arithmetic before = go Set.empty
  where
    bindings=Map.fromListWith(\_ old->old)
      (concatMap binding before)
    binding(Compound "unify" [Var v,t]) | t/=Var v=[(v,t)]
    binding(Compound "unify" [t,Var v]) | t/=Var v=[(v,t)]
    binding(Compound "is" [Var v,t]) | arithmetic=[(v,t)]
    binding _=[]
    go seen(Var v) | not(Set.member v seen),Just t<-Map.lookup v bindings=go(Set.insert v seen)t
    go seen(Compound f xs)=Compound f(map(go seen)xs)
    go _ t=t

norm :: Norm -> Term -> Expr
norm _ (Var v)=variable v
norm ListLength (Compound "cons" [_,xs])=plus(constant 1)(norm ListLength xs)
norm ListLength _=constant 0
norm TermSize (Compound f xs)=foldl' plus (constant 1)(map(norm TermSize)xs)
norm TermSize _=constant 1
linear :: Term -> Maybe Expr
linear(IntLit n)=Just(constant n)
linear(Var v)=Just(variable v)
linear(Compound "plus"[a,b])=plus <$> linear a <*> linear b
linear(Compound "minus"[a,b])=minus <$> linear a <*> linear b
linear(Compound "neg"[a])=scale (-1) <$> linear a
linear(Compound "mul"[IntLit n,a])=scale n <$> linear a
linear(Compound "mul"[a,IntLit n])=scale n <$> linear a
linear _=Nothing

nonnegative :: Norm -> Expr -> Maybe Bool
nonnegative kind (Expr c vs)
  | all(>=0)(Map.elems vs), lower>=0 = Just(lower>0)
  | otherwise=Nothing
  where lower=c+if kind==TermSize then sum(Map.elems vs) else 0

type Bounds = [(Expr,Expr,Bool)]
compareNorm :: Norm -> Bounds -> Expr -> Expr -> Maybe Bool
compareNorm kind edges source target =
  case nonnegative kind(minus source target) of
    Just answer->Just answer
    Nothing->case [strict || extra | (a,b,strict)<-closed,
                     Just extra<-[nonnegative kind(minus(minus source a)(minus target b))]] of
      []->Nothing
      xs->Just(or xs)
  where
    closed=close (Map.fromListWith(||)[((a,b),s) | (a,b,s)<-edges])
    close known =
      let new=Map.fromListWith(||)[((a,c),s||t) | ((a,b),s)<-Map.toList known,((b',c),t)<-Map.toList known,b==b']
          next=Map.unionWith(||)known new
      in if next==known || Map.size next>512 then [(a,b,s) | ((a,b),s)<-Map.toList known] else close next

-- Each relation is verified for every successful clause path. Starting from
-- all candidates and deleting failures is induction on finite derivations;
-- no termination assumption about the recursive callee is used here.
type Relations = Map PredKey (Set (Int,Int,Norm,Bool))
sizeRelations :: (String -> Int -> Maybe Det) -> Program -> Relations
sizeRelations builtin p=go initial
  where
    ps=[q | q<-programPreds p,builtin(fst(predKey q))(snd(predKey q))==Nothing]
    initial=Map.fromList[(predKey q,Set.fromList[(i,j,k,s) | i<-[0..snd(predKey q)-1],j<-[0..snd(predKey q)-1],i/=j,k<-[TermSize,ListLength],s<-[False,True]]) | q<-ps,not(predIsDynamic p q)]
    go old=let next=Map.fromList[(predKey q,Set.filter(valid old q)(Map.findWithDefault Set.empty(predKey q)old)) | q<-ps]
           in if next==old then old else go next
    valid old q (i,j,kind,strict)=all clause(IM.elems(predClauses q))
      where
        clause cl=let hs=headArgs cl in i<length hs && j<length hs && all (\path->
          let a=norm kind(expand False path(hs!!i)); b=norm kind(expand False path(hs!!j))
          in case compareNorm kind (bounds old kind path) a b of Just s->not strict || s; Nothing->False) (successPaths(clauseBody cl))

successPaths :: [Term] -> [[Term]]
successPaths = foldl' (\paths g->[a++b | a<-paths,b<-one g]) [[]]
  where
    one(Compound ","[a,b])=successPaths[a,b]
    one(Compound ";"[Compound "->"[c,t],e])=successPaths[c,t]++successPaths[e]
    one(Compound ";"[a,b])=successPaths[a]++successPaths[b]
    one(Compound "->"[c,t])=successPaths[c,t]
    one(Compound "once"[a])=successPaths[a]
    one(Compound f _) | f `elem` ["not","forall","findall","bagof","setof","std_native_bagof","std_native_setof","minimize"]=[[]]
    one g=[[g]]

bounds :: Relations -> Norm -> [Term] -> Bounds
bounds relations kind path=
  [(norm kind(expand False path(as!!i)),norm kind(expand False path(as!!j)),s)
   | Compound name as<-path,(i,j,k,s)<-Set.toList(Map.findWithDefault Set.empty(name,length as)relations),k==kind,i<length as,j<length as]

pairs :: Int -> [(Int,Int)]
pairs n=[(i,j) | i<-[0..n-1],j<-[i+1..n-1]]
nodePositions :: Int -> Int -> [Int]
nodePositions arity node
  | node<4*arity=[node `div` 4]
  | index<length(pairs arity)=let(i,j)=pairs arity!!index in [i,j]
  | otherwise=[]
  where index=(node-4*arity) `div` 4

callGraph :: Relations -> Maybe [Bool] -> Deps -> Set Int -> Set Int -> Call -> [Maybe Term] -> (Arcs,Set Int)
callGraph relations evaluated deps rigid integer c args=(Set.unions[old,ordinary,sums,numeric,differences,elements],groundOut)
  where
    hs=callHead c
    n=length hs
    target=length args
    before=callBefore c
    (old,groundOut)=structuralGraph deps rigid c args
    ordinary=Set.fromList[(4*i+tag,4*j+tag,s) | (i,h)<-zip[0..]hs,Set.member i rigid,(j,Just a)<-zip[0..]args,(kind,tag)<-[(TermSize,0),(ListLength,1)],
      Just s<-[compareNorm kind(bounds relations kind before)(norm kind(expand False before h))(norm kind(expand False before a))]]
    sums=Set.fromList[(4*n+4*ix+tag,4*target+4*jx+tag,s) |
      (ix,(i,j))<-zip[0..](pairs n),all (`Set.member` rigid)[i,j],
      (jx,(a,b))<-zip[0..](pairs target),target<=6 || (i,j)==(a,b),
      Just x<-[args!!a],Just y<-[args!!b],(kind,tag)<-[(ListLength,0),(TermSize,1)],
      let normed t=norm kind(expand False before t),
      Just s<-[compareNorm kind(bounds relations kind before)(plus(normed(hs!!i))(normed(hs!!j)))(plus(normed x)(normed y))]]
    ivars=integerVars integer hs before
    isInteger t=integerTerm ivars t
    actual j t=case t of Var _->True; IntLit _->True; _->maybe False (\xs->j<length xs && xs!!j) evaluated
    numeric=Set.fromList[(4*i+tag,4*j+tag,s) | (i,h)<-zip[0..]hs,Set.member i integer,
      (j,Just a)<-zip[0..]args,actual j a,isInteger(expand True before a),
      Just x<-[linear(expand True before h)],Just y<-[linear(expand True before a)],
      (direction,tag)<-[(1,2),(-1,3)],Just s<-[numericArc before (scale direction x)(scale direction y)]]
    differences=Set.fromList[(4*n+4*ix+tag,4*target+4*jx+tag,s) |
      (ix,(i,j))<-zip[0..](pairs n),all (`Set.member` integer)[i,j],
      (jx,(a,b))<-zip[0..](pairs target),target<=6 || (i,j)==(a,b),
      Just x<-[args!!a],Just y<-[args!!b],actual a x,actual b y,
      isInteger(expand True before x),isInteger(expand True before y),
      Just hi<-[linear(expand True before(hs!!j))],Just lo<-[linear(expand True before(hs!!i))],
      Just hi'<-[linear(expand True before y)],Just lo'<-[linear(expand True before x)],
      (direction,tag)<-[(1,2),(-1,3)],
      Just s<-[numericArc before(scale direction(minus hi lo))(scale direction(minus hi' lo'))]]
    elements=Set.fromList[(4*i,4*j,True) | (i,h)<-zip[0..]hs,Set.member i rigid,(j,Just(Compound "$element"[list]))<-zip[0..]args,
      let(eq,sm)=relatives h before,Set.member list eq || Set.member list sm]

numericArc :: [Term] -> Expr -> Expr -> Maybe Bool
numericArc before source target=case minus source target of
  Expr delta vs | Map.null vs,delta>=0 ->Just(delta>0 && bounded)
  _->Nothing
  where
    bounded=any guards before
    guards (Compound op [a,b]) | op `elem` ["gt","gte","lt","lte"] =
      case (linear(expand True before a),linear(expand True before b)) of
        (Just x,Just y)->let lower=if op `elem` ["gt","gte"] then minus x y else minus y x
                        in case minus source lower of Expr _ vs->Map.null vs
        _->False
    guards _=False

integerTerm :: Set VarId -> Term -> Bool
integerTerm _ (IntLit _)=True
integerTerm vars(Var v)=Set.member v vars
integerTerm vars(Compound f xs) | f `elem` ["plus","minus","mul","div","mod","neg","abs","min","max"] = all(integerTerm vars)xs
integerTerm _ _=False
integerVars :: Set Int -> [Term] -> [Term] -> Set VarId
integerVars rigid hs=foldl' step initial
  where
    initial=Set.fromList(concat[termVarIds h | (i,h)<-zip[0..]hs,Set.member i rigid])
    step known(Compound "is"[Var v,e]) | integerTerm known e=Set.insert v known
    step known(Compound "is_int"[Var v])=Set.insert v known
    step known(Compound "unify"[a,b]) | integerTerm known a=Set.union known(Set.fromList(termVarIds b))
                                         | integerTerm known b=Set.union known(Set.fromList(termVarIds a))
    step known _=known

-- Statically verified correspondence between a closure's extra parameters
-- and the meta-predicate's head. Element roles are inferred from cons heads,
-- not from the name maplist (which a user may shadow).
metaArguments :: Program -> PredKey -> Int -> [Term] -> Int -> [Maybe Term]
metaArguments p key closurePosition supplied count=case lookupPred key p of
  Nothing->replicate count Nothing
  Just q ->
    let observations=[(headArgs cl,extra) | cl<-IM.elems(predClauses q),closurePosition<length(headArgs cl),
          Var v<-[headArgs cl!!closurePosition],(Compound "call"(Var u:extra),_)<-dominated(clauseBody cl),v==u,length extra==count]
        role hs value=case [(j,False) | (j,x)<-zip[0..]hs,x==value] ++
                          [(j,True) | (j,Compound "cons"[x,_])<-zip[0..]hs,x==value] of
          first:_->Just first
          _->Nothing
        directOnly=all (\cl -> case drop closurePosition (headArgs cl) of
          Var v:_ -> all (\(g,_) -> case g of
            Compound "call" (Var u:_) | u==v -> True
            Compound name xs | (name,length xs)==key,closurePosition<length xs,xs!!closurePosition==Var v -> True
            _ -> v `notElem` termVarIds g) (dominated(clauseBody cl))
          _ -> True) (IM.elems(predClauses q))
        preserved (j,_) = all (\cl -> all (\(g,before) -> case g of
          Compound name xs | (name,length xs)==key,j<length xs,j<length(headArgs cl) ->
            let (equal,smaller)=relatives(headArgs cl!!j)before
            in Set.member(xs!!j)equal || Set.member(xs!!j)smaller
          _ -> True) (dominated(clauseBody cl))) (IM.elems(predClauses q))
        at i=case [role hs(xs!!i) | (hs,xs)<-observations,directOnly] of
          Just r:rs | all(==Just r)rs,preserved r,let(j,element)=r,j<length supplied -> Just(if element then Compound "$element"[supplied!!j] else supplied!!j)
          _->Nothing
    in map at [0..count-1]

-- Finite-domain tabling is a syntactic Datalog proof. Calls may only use
-- constants or variables, facts are ground, and each head variable must be
-- range-restricted by a positive finite relation in every successful branch.
finiteTable :: (String -> Int -> Maybe Det) -> Program -> Set PredKey -> Bool
finiteTable builtin p group=go Set.empty(Set.toList group)
  where
    atomArg(Compound _ _)=False
    atomArg _=True
    go _ []=True
    go seen(k:ks) | Set.member k seen=go seen ks
    go seen(k:ks)=case lookupPred k p of
      Nothing->False
      Just q | predIsDynamic p q || not(predPure q) || FlagNoTable `elem` effectiveFlags p q && predRecursive q ->False
      Just q | predRecursive q && not(progTableDefault p || FlagTable `elem` effectiveFlags p q)->False
      Just q ->
        let clauses=IM.elems(predClauses q)
            hs cl=headArgs cl
            safe cl=all atomArg(hs cl) && if null(clauseBody cl) then null(concatMap termVarIds(hs cl))
                    else all (\path->all allowed path && all (`elem` concatMap termVarIds path) (concatMap termVarIds(hs cl))) (successPaths(clauseBody cl))
            bounded (Compound f [IntLit _,IntLit _,value]) | f `elem` ["between","std_native_between"] = atomArg value &&
              (f=="std_native_between" || not(isJust(lookupPred(f,3)p)))
            bounded (Compound "unify" [x,y]) = atomArg x && atomArg y && (null(termVarIds x) || null(termVarIds y))
            bounded _ = False
            allowed t=bounded t || case t of
              Compound f as->all atomArg as && builtin f (length as)==Nothing && isJust(lookupPred(f,length as)p)
              Atom f->builtin f 0==Nothing && isJust(lookupPred(f,0)p)
              _->False
            deps'=[target | cl<-clauses,path<-successPaths(clauseBody cl),g<-path,not(bounded g),Just target<-[functorOf g]]
        in not(null clauses) && all safe clauses && go(Set.insert k seen)(deps'++ks)

-- ─── Source-grounded call-site modes ────────────────────────────────────────
data CallSite = CallSite
  { siteCaller :: PredKey, siteClause :: Int, siteGoal :: Term,
    siteCallee :: Maybe PredKey, siteCovered :: Bool, siteReason :: String }
  deriving(Eq,Show)

callSites :: (String -> Int -> Maybe Det) -> RawDeps -> Program -> Map PredKey Verdict -> [CallSite]
callSites builtin raw p found=
  [CallSite (predKey pred) (callClause c) (callGoal c) (target c) covered why |
   pred<-programPreds p,(ci,cl)<-zip[1..](IM.elems(predClauses pred)),c<-clauseCalls p(metaPositions p)ci cl,
   let (covered,why)=check pred c]
  where
    deps=modeDependencies builtin raw p
    target c=case callTarget c of CallUser k _->Just k; _->Nothing
    check pred c=case callTarget c of
      CallUser k args->case Map.lookup k found of
        Just(Total proof)->
          let declared=Set.fromList[i | i<-[0..snd(predKey pred)-1],not(null(predDecls pred)),all(\s->i<length(sigArgs s) && argMode(sigArgs s!!i)==ModeIn)(predDecls pred)]
              declaredInts=Set.fromList[i | i<-Set.toList declared,all(\s->argSort(sigArgs s!!i)==SInt)(predDecls pred)]
              modes=case Map.lookup(predKey pred)found of
                Just(Total own)->zip(proofConditions own)(proofIntegers own)
                _->[([],[])]
              coveredMode (positions,ip)=
                let rigid=Set.union declared(Set.fromList(map(subtract 1)positions))
                    integers=Set.union declaredInts(Set.fromList(map(subtract 1)ip))
                    ground=groundVars deps rigid(callHead c)(callBefore c)
                    ints=integerVars integers(callHead c)(callBefore c)
                in any(\(ps,ns)->all(groundArgument ground args . subtract 1)ps && all(integerArgument ints args . subtract 1)ns)(zip(proofConditions proof)(proofIntegers proof))
          in (all coveredMode modes,renderVerdict(Total proof))
        Just(Unproven why)->(False,why)
        _->(True,"")
      CallOpaque->(False,"unknown closure")
      CallParameter->(True,"conditional on a total closure")

numericActual :: Maybe [Bool] -> Int -> Term -> Bool
numericActual _ _ (Var _)=True
numericActual _ _ (IntLit _)=True
numericActual flags j _=maybe False (\xs->j<length xs && xs!!j) flags

calledPredicates :: Program -> Map PredKey [PredKey]
calledPredicates p = Map.fromList [(predKey q,nub [k | (ci,cl)<-zip[1..](IM.elems(predClauses q)),c<-clauseCalls p(metaPositions p)ci cl,CallUser k _<-[callTarget c]]) | q<-programPreds p]

-- Every variable of a finite-domain argument ranges over finitely many
-- integers. This is distinct from groundness: CLP variables remain unbound.
type Domains = Map PredKey (Set Int)
finiteDomainRelations :: (String -> Int -> Maybe Det) -> Program -> Domains
finiteDomainRelations builtin p = fixed initial
  where
    ps=[q | q<-programPreds p,builtin(fst(predKey q))(snd(predKey q))==Nothing,not(predIsDynamic p q),not(IM.null(predClauses q))]
    initial=Map.fromList[(predKey q,Set.fromList[0..snd(predKey q)-1]) | q<-ps]
    fixed old=let next=Map.fromList[(predKey q,Set.filter (valid old q) (Map.findWithDefault Set.empty(predKey q)old)) | q<-ps]
              in if next==old then old else fixed next
    valid old q i=all (\cl->all (\path->i<length(headArgs cl) &&
      all (`Set.member` domainVars old Set.empty path) (termVarIds(expand False path(headArgs cl!!i))))
      (successPaths(clauseBody cl))) (IM.elems(predClauses q))

domainVars :: Domains -> Set VarId -> [Term] -> Set VarId
domainVars relations initial path=foldl' step initial path
  where
    vars t=Set.fromList(termVarIds(expand False path t))
    step known(Compound "in" [value,Compound "range" [IntLit _,IntLit _]])=Set.union known(vars value)
    step known(Compound name args)=Set.union known(Set.unions[vars(args!!i) |
      i<-Set.toList(Map.findWithDefault Set.empty(name,length args)relations),i<length args])
    step known _=known

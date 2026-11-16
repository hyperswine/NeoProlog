-- | Pure term reflection shared by all execution backends.
module Infera.TermToolkit (toolkit, toolkitKeys, toolkitSignatures, compareTerms) where

import qualified Data.IntMap.Strict as IM
import Data.List (nub, sortBy, groupBy)
import qualified Data.Map.Strict as Map
import Infera.Arith (compareNumeric, NumericValue (..))
import Infera.Syntax
import Infera.Program
import Infera.Error
import Infera.CLP
import Infera.Unify (deepWalk)

toolkitKeys :: [(String, Int)]
toolkitKeys = [("std_native_between",3),("std_native_msort",2),("std_native_sort",2),("std_native_sort_by",4),("functor",3),("arg",3),("univ",2),("copy_term",2),
               ("term_variables",2),("compare",3),("clause",2)]

-- | Conservative relational declarations, also shown by :sig.
toolkitSignatures :: [(String, Signature)]
toolkitSignatures =
  [(name, Signature det [ArgSpec sort ModeInOut | sort <- sorts] []) |
    (name,det,sorts) <-
      [("put_attr",Semidet,[SAny,SAtom,SAny]), ("get_attr",Semidet,[SAny,SAtom,SAny]),
       ("del_attr",Semidet,[SAny,SAtom]), ("copy_term_nat",Semidet,[SAny,SAny]),
       ("functor",Semidet,[SAny,SAtom,SInt]), ("arg",Nondet,[SInt,SAny,SAny]),
       ("univ",Semidet,[SAny,SList SAny]), ("copy_term",Semidet,[SAny,SAny]),
       ("term_variables",Semidet,[SAny,SList SAny]), ("compare",Semidet,[SAtom,SAny,SAny]),
       ("clause",Nondet,[SAny,SAny])]]

-- | Variables compare by logical ID. Integer and floating representations
-- are ordered separately, avoiding lossy conversion of arbitrary integers.
compareTerms :: Term -> Term -> Ordering
compareTerms a b = case compare (rank a) (rank b) of
  EQ -> case (a,b) of
    (FloatLit x, FloatLit y) -> compareNumeric (NVFloat x) (NVFloat y)
    (Compound f xs, Compound g ys) -> compare (length xs) (length ys) <> compare f g <> lists xs ys
    _ -> compare a b
  other -> other
  where
    rank t = case t of
      Var _ -> 0 :: Int
      IntLit _ -> 1
      FloatLit _ -> 2
      CharLit _ -> 3
      Atom _ -> 4
      StrLit _ -> 5
      Compound _ _ -> 6
    lists [] [] = EQ
    lists (x:xs) (y:ys) = compareTerms x y <> lists xs ys
    lists xs ys = compare (length xs) (length ys)

-- | Each alternative owns its store and fresh-variable frontier. A malformed
-- structural request is a SolveError, never a host-language exception.
toolkit :: Program -> Map.Map PredKey [(Term, Int)] -> Store -> Int -> Term -> Maybe [Either SolveError (Store, Int)]
toolkit program dynamic store fresh goal = case goal of
  Compound name args | (name,length args) `elem` toolkitKeys -> Just (concatMap distribute (alternatives name (map (deepWalk (stSubst store)) args)))
  _ -> Nothing
  where
    -- Keep alternative errors and answers in search order, and do not force
    -- later clauses when a caller only consumes a prefix.
    distribute (Left err) = [Left err]
    distribute (Right xs) = map Right xs
    alternatives "arg" [n@(Var _),t,a] = case structure t of
      Left err -> [Left err]
      Right (_,xs) -> [unifyMany fresh [(n,IntLit i),(a,x)] | (i,x) <- zip [1..] xs]
    alternatives "clause" [h,b] = case clausesFor h of
      Left err -> [Left err]
      Right clauses -> map (reflect h b) clauses
    -- Integers from Lo to Hi in order; a bound X is a range check.
    alternatives "std_native_between" [lo,hi,x] = case (lo,hi) of
      (IntLit l, IntLit h) -> case x of
        Var _ -> [unifyMany fresh [(x,IntLit i)] | i <- [l..h]]
        IntLit v | l <= v && v <= h -> [Right [(store,fresh)]]
        _ -> []
      (IntLit _, other) -> [Left (boundError other)]
      (other, _) -> [Left (boundError other)]
    alternatives name args = [run name args]
    boundError t = case t of Var _ -> InstantiationError t; _ -> TypeError "integer bound" t
    bad t = Left (TypeError "positive-arity non-list compound term toolkit request" t)
    unifyMany n pairs = go store pairs
      where
        go st [] = Right [(st,n)]
        go st ((a,b):rest) = case storeUnify st a b of
          Left e -> Left e
          Right Nothing -> Right []
          Right (Just st') -> go st' rest
    structure t = case t of
      Compound f xs | f /= "cons", not (null xs) -> Right (f,xs)
      _ -> bad t
    construct name xs = case name of
      Atom f | f /= "cons", f /= "nil", not (null xs) -> Right (Compound f xs)
      _ -> bad name
    rename terms =
      let ids = nub (concatMap termVarIds terms)
          mapping = Map.fromList (zip ids [fresh..])
          go t = case t of
            Var v -> Var (mapping Map.! v)
            Compound f xs -> Compound f (map go xs)
            _ -> t
      in (map go terms, fresh + length ids)
    body [] = Atom "true"
    body [x] = x
    body (x:xs) = Compound "," [x,body xs]
    proper t = case unfoldCons t of
      (xs,Nothing) -> Right xs
      _ -> Left (TypeError "proper list" t)
    run "std_native_msort" [xs,out] = do
      values <- proper xs
      unifyMany fresh [(out,mkList (sortBy compareTerms values) Nothing)]
    run "std_native_sort" [xs,out] = do
      values <- proper xs
      let groups=groupBy (\a b -> compareTerms a b == EQ) (sortBy compareTerms values)
      unifyMany fresh [(out,mkList [x | x:_ <- groups] Nothing)]
    run "std_native_sort_by" [field,order,xs,out] = do
      values <- proper xs
      n <- case field of IntLit k | k>=0,k<=fromIntegral(maxBound::Int) -> Right(fromInteger k); _ -> Left(TypeError "sort field" field)
      o <- case order of Atom name | name `elem` ["lt","lte","gt","gte"] -> Right name; _ -> Left(TypeError "sort order lt/lte/gt/gte" order)
      let key x | n==0 = Right x
                | otherwise = case x of Compound _ as | n<=length as -> Right(as !! (n-1)); _ -> Left(TypeError "sort field in compound" x)
      decorated <- mapM (\x -> (\k -> (k,x)) <$> key x) values
      let cmp (a,_) (b,_) = if o `elem` ["gt","gte"] then compareTerms b a else compareTerms a b
          sorted=sortBy cmp decorated
          selected=if o `elem` ["lt","gt"] then [x | x:_ <- groupBy (\(a,_) (b,_) -> compareTerms a b == EQ) sorted] else sorted
      unifyMany fresh [(out,mkList (map snd selected) Nothing)]
    run "functor" [t,n,a] = case t of
      Var _ -> case a of
        -- Any arity memory allows; exhausting memory is a fault.
        IntLit k | k > 0, k <= fromIntegral (maxBound :: Int) -> do
            term <- construct n (map Var [fresh..fresh+fromInteger k-1])
            unifyMany (fresh+fromInteger k) [(t,term)]
        _ -> bad a
      _ -> do
        (f,xs) <- structure t
        unifyMany fresh [(n,Atom f),(a,IntLit (fromIntegral (length xs)))]
    run "arg" [n,t,a] = do
      (_,xs) <- structure t
      case n of
        Var _ -> fmap concat $ mapM (\(i,x) -> unifyMany fresh [(n,IntLit i),(a,x)]) (zip [1..] xs)
        IntLit i | i > 0, i <= fromIntegral (length xs) -> unifyMany fresh [(a,xs !! (fromInteger i-1))]
        _ -> bad n
    run "univ" [t,l] = case t of
      Var _ -> case unfoldCons l of
        (n:xs,Nothing) -> do
          term <- construct n xs
          unifyMany fresh [(t,term)]
        _ -> bad l
      _ -> do
        (f,xs) <- structure t
        unifyMany fresh [(l,mkList (Atom f:xs) Nothing)]
    run "copy_term" [t,c] = case rename [t] of
      ([copy],next) -> unifyMany next [(c,copy)]
      _ -> bad t
    run "term_variables" [t,vs] = unifyMany fresh [(vs,mkList (map Var (nub (termVarIds t))) Nothing)]
    run "compare" [o,a,b] = unifyMany fresh [(o,Atom (case compareTerms a b of LT -> "lt"; EQ -> "eq"; GT -> "gt"))]
    run _ _ = bad goal
    clausesFor h = do
      candidates <- case h of
        Var _ -> Right (programPreds program)
        _ -> case functorOf h of
          Nothing -> bad h
          Just key -> Right (maybe [] (:[]) (lookupPred key program))
      let static = [cl | p <- candidates, cl <- IM.elems (predClauses p)]
          facts = [Clause t [] n | (key, fs) <- Map.toAscList dynamic,
                     case h of Var _ -> True; _ -> functorOf h == Just key,
                     (t,n) <- fs]
      Right (static ++ facts)
    reflect h b cl = case rename [clauseHead cl,body (clauseBody cl)] of
      ([hd,bd],next) -> unifyMany next [(h,hd),(b,bd)]
      _ -> bad h

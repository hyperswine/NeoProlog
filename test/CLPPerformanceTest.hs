{-# LANGUAGE OverloadedStrings #-}

-- Keep the pre-optimisation store as a bounded differential oracle. The new
-- scheduler may strengthen a residual sooner; compare complete assignments,
-- not its internal queue or the exact spelling of an equivalent residual.
module CLPPerformanceTest (clpPerformanceGroup) where

import Data.List (intercalate, nub, sort)
import Hedgehog hiding (Var)
import qualified Hedgehog.Gen as Gen
import qualified Hedgehog.Range as Range
import Infera
import qualified ReferenceCLP as Ref

data Operation
  = Bounds Int Integer Integer
  | Relation Rel Term Term
  | Alias Int Int
  | Disequal Term Term
  deriving Show

genExpression :: Gen Term
genExpression = Gen.choice
  [ Var <$> Gen.int (Range.linear 0 2),
    IntLit <$> Gen.integral (Range.linear (-3) 3),
    Compound <$> Gen.element ["plus", "minus", "mul"]
      <*> sequence [Var <$> Gen.int (Range.linear 0 2),
                    Gen.choice [Var <$> Gen.int (Range.linear 0 2),
                                IntLit <$> Gen.integral (Range.linear (-3) 3)]],
    Compound "abs" . (: []) . Var <$> Gen.int (Range.linear 0 2)
  ]

genOperation :: Gen Operation
genOperation = Gen.choice
  [ do v <- Gen.int (Range.linear 0 2)
       lo <- Gen.integral (Range.linear (-3) 2)
       width <- Gen.integral (Range.linear 0 5)
       pure (Bounds v lo (lo + width)),
    Relation <$> Gen.element [RelEq, RelNe, RelLe] <*> genExpression <*> genExpression,
    Alias <$> Gen.int (Range.linear 0 2) <*> Gen.int (Range.linear 0 2),
    Disequal <$> genExpression <*> genExpression
  ]

post :: Operation -> Store -> Either SolveError (Maybe Store)
post op st = case op of
  Bounds v lo hi -> addDomain (Var v) (Fin lo) (Fin hi) st
  Relation rel a b -> addRelation rel a b st
  Alias a b -> storeUnify st (Var a) (Var b)
  Disequal a b -> addDiseq a b st

postReference :: Operation -> Ref.Store -> Either SolveError (Maybe Ref.Store)
postReference op st = case op of
  Bounds v lo hi -> Ref.addDomain (Var v) (Ref.Fin lo) (Ref.Fin hi) st
  Relation rel a b -> Ref.addRelation (case rel of
    RelEq -> Ref.RelEq; RelNe -> Ref.RelNe; RelLe -> Ref.RelLe) a b st
  Alias a b -> Ref.storeUnify st (Var a) (Var b)
  Disequal a b -> Ref.addDiseq a b st

continue :: (a -> Either SolveError (Maybe a)) -> Either SolveError (Maybe a)
  -> Either SolveError (Maybe a)
continue f result = result >>= maybe (Right Nothing) f

accepted :: Either SolveError (Maybe a) -> Either SolveError Bool
accepted = fmap (maybe False (const True))

prop_store_reference :: Property
prop_store_reference = withTests 300 $ property $ do
  operations <- forAll (Gen.list (Range.linear 0 12) genOperation)
  boundedFirst <- forAll Gen.bool
  classify "initially infinite bounds" (not boundedFirst)
  let current0 = if boundedFirst then addDomains (map Var [0..2]) (Fin (-2)) (Fin 2) emptyStore
        else Right (Just emptyStore)
      reference0 = if boundedFirst then
        foldl (\r v -> continue (Ref.addDomain (Var v) (Ref.Fin (-2)) (Ref.Fin 2)) r)
          (Right (Just Ref.emptyStore)) [0..2]
        else Right (Just Ref.emptyStore)
      current = foldl (\r op -> continue (post op) r) current0 operations
      reference = foldl (\r op -> continue (postReference op) r) reference0 operations
  mapM_ (\values -> do
      let bindings = zip [0..2] values
          actual = foldl (\r (v,n) -> continue (\st -> storeBind st v n) r) current bindings
          referenceBound = foldl (\r (v,n) -> continue (\st -> Ref.storeBind st v n) r) reference bindings
          -- The frozen store does not remap its watched-variable set when an
          -- alias rewrites a nonlinear residual. Settle the complete assignment
          -- explicitly so that a missed reference wake-up cannot accept an
          -- invalid answer (for example abs X = X, X = Y, Y = -1).
          expected = continue Ref.propagate referenceBound
      accepted actual === accepted expected
    ) (sequence (replicate 3 [-2..2]))

prop_absolute_alias_fixed_point :: Property
prop_absolute_alias_fixed_point = withTests 1 $ property $ do
  mapM_ (\(reverseSides, aliasFirst, bindingOrder, n) -> do
      let variable = Var 1
          absolute = Compound "abs" [variable]
          relation = if reverseSides then Relation RelEq variable absolute
            else Relation RelEq absolute variable
          alias = Alias 1 0
          operations = if aliasFirst then [alias, relation] else [relation, alias]
          current = foldl (\r op -> continue (post op) r) (Right (Just emptyStore)) operations
          reference = foldl (\r op -> continue (postReference op) r) (Right (Just Ref.emptyStore)) operations
          actual = foldl (\r v -> continue (\st -> storeBind st v n) r) current bindingOrder
          expected = continue Ref.propagate $
            foldl (\r v -> continue (\st -> Ref.storeBind st v n) r) reference bindingOrder
      annotateShow (reverseSides, aliasFirst, bindingOrder, n)
      -- This oracle is the integer equation itself, independent of either
      -- store's scheduler, domain narrowing, or residual representation.
      accepted actual === Right (abs n == n)
      accepted expected === Right (abs n == n)
    ) [(reverseSides, aliasFirst, bindingOrder, n)
      | reverseSides <- [False, True], aliasFirst <- [False, True],
        bindingOrder <- [[0,1], [1,0]], n <- [-3..3]]

solve :: [String] -> String -> PropertyT IO [[Integer]]
solve names query = do
  annotate query
  prog <- evalEither (loadProgramText "")
  q <- evalEither (parseQuery query)
  let result = solveAll prog q
  summaryErrors result === []
  summaryExhausted result === False
  sort <$> mapM (\answer -> mapM (\name ->
    case lookup name (answerBindings answer) of
      Just (IntLit n) -> pure n
      other -> annotateShow other >> failure) names) (summaryAnswers result)

prop_reification_model :: Property
prop_reification_model = withTests 300 $ property $ do
  op <- forAll (Gen.element ["#=", "#!=", "#<", "#<=", "#>", "#>="])
  coefficient <- forAll (Gen.integral (Range.linear (-2) 2))
  offset <- forAll (Gen.integral (Range.linear (-2) 2))
  expectedTruth <- forAll (Gen.element [Nothing, Just (0 :: Integer), Just 1])
  reversePosting <- forAll Gen.bool
  let relation = "reify (((" ++ show coefficient ++ ") * X + (" ++ show offset ++ ")) " ++ op ++ " Y) B"
      domains = ["[X, Y] in -2..2", "B in 0..1"]
      binding = maybe [] (\n -> ["B = " ++ show n]) expectedTruth
      goals = (if reversePosting then [relation] ++ domains else domains ++ [relation]) ++ binding
      holds a b = case op of
        "#=" -> a == b; "#!=" -> a /= b; "#<" -> a < b
        "#<=" -> a <= b; "#>" -> a > b; _ -> a >= b
      expected = sort [[x,y,b] | x <- [-2..2], y <- [-2..2],
        let b = if holds (coefficient*x+offset) y then 1 else 0,
        maybe True (== b) expectedTruth]
  actual <- solve ["X","Y","B"] (intercalate ", " (goals ++ ["label [X, Y, B]"]) ++ "?")
  actual === expected

prop_absolute_model :: Property
prop_absolute_model = withTests 200 $ property $ do
  cap <- forAll (Gen.integral (Range.linear 0 6))
  reversePosting <- forAll Gen.bool
  let relation = "D #= abs (X - Y)"
      domains = ["[X, Y] in -3..3", "D in 0..6", "D #<= " ++ show cap]
      goals = if reversePosting then relation : domains else domains ++ [relation]
  actual <- solve ["X","Y","D"] (intercalate ", " (goals ++ ["label [X, Y, D]"]) ++ "?")
  actual === sort [[x,y,abs(x-y)] | x <- [-3..3], y <- [-3..3], abs(x-y) <= cap]

prop_global_distinct_model :: Property
prop_global_distinct_model = withTests 200 $ property $ do
  count <- forAll (Gen.int (Range.linear 0 5))
  domains <- forAll $ Gen.list (Range.singleton count) $ do
    lo <- Gen.integral (Range.linear (-2) 2)
    width <- Gen.integral (Range.linear 0 3)
    pure (lo,lo+width)
  let names = take count ["A","B","C","D","E"]
      list = "[" ++ intercalate ", " names ++ "]"
      goals = [name ++ " in " ++ show lo ++ ".." ++ show hi | (name,(lo,hi)) <- zip names domains]
      expected = sort [xs | xs <- sequence [[lo..hi] | (lo,hi) <- domains], length (nub xs) == length xs]
  actual <- solve names (intercalate ", " (goals ++ ["all_different " ++ list, "label " ++ list]) ++ "?")
  actual === expected

prop_propagation_regressions :: Property
prop_propagation_regressions = withTests 1 $ property $ do
  -- Hall failure and Hall pruning happen before labeling.
  runInfera "" "[X,Y,Z] in 1..2, all_different [X,Y,Z]?" === Right ["false."]
  runInfera "" "[X,Y] in 1..2, Z in 1..3, all_different [X,Y,Z], Z #!= 3?" === Right ["false."]
  runInfera "" "X in 0..1, all_different [X,X]?" === Right ["false."]
  -- A watcher on a structured term must follow a later alias and its binding.
  runInfera "" "node X != node 1, X = Y, Y = 1?" === Right ["false."]
  runInfera "" "X * Y #= 6, X = Z, Z = 2, Y = 4?" === Right ["false."]
  runInfera "" "reify (X #<= Y) B, B = 0, X = Y?" === Right ["false."]
  runInfera "" "D #= abs X, D = -1?" === Right ["false."]
  runInfera "" "reify (1 #= 1) 2?" === Right ["false."]
  runInfera "" "all_different [bad]?" === Right ["true."]
  runInfera "" "all_different [1, 0 + 1]?" === Right ["false."]
  -- Sparse Hall sets require matching, rather than just interval capacities.
  runInfera "" "[X,Y,Z] in 0..2, X #!= 1, Y #!= 1, all_different [X,Y,Z], Z #!= 1?"
    === Right ["false."]
  -- A delayed arithmetic error in an earlier list element must still precede
  -- a later invalid integer-domain membership.
  let dividend = Compound "div" [IntLit 1, Var 0]
      current = continue (addDomains [Var 0, IntLit 2] (Fin 0) (Fin 0))
        (addRelation RelEq (IntLit 0) dividend emptyStore)
      reference = continue (Ref.addDomain (IntLit 2) (Ref.Fin 0) (Ref.Fin 0)) $
        continue (Ref.addDomain (Var 0) (Ref.Fin 0) (Ref.Fin 0)) $
          Ref.addRelation Ref.RelEq (IntLit 0) dividend Ref.emptyStore
  accepted current === accepted reference
  -- Symbolic arithmetic entries keep the old pairwise typing guarantees even
  -- before all list entries are ground.
  prog <- evalEither (loadProgramText "")
  mapM_ (\text -> do
      query <- evalEither (parseQuery text)
      let result = solveAll prog query
      summaryAnswers result === []
      summaryErrors result === [CLPTypeError (Atom "bad")]
    ) ["all_different [X + 0, Y], X = bad?",
       "all_different [X * 2, Y], Y = bad?",
       "all_different [X, Y], X = bad?"]
  runInfera "" "D #= abs (1 / X), X = 0, fail?" === Right ["false."]
  runInfera "" "D #= abs X, X = bad, fail?" === Right ["false."]
  -- Cancelling coefficients inside abs must not erase the original delayed
  -- expression's validation, on either side or after an alias is introduced.
  mapM_ (\(lhs,rhs,variable) -> mapM_ (\value -> do
      let cancelledCurrent = continue (\s -> storeUnify s (Var variable) value)
            (addRelation RelEq lhs rhs emptyStore)
          cancelledReference = continue (\s -> Ref.storeUnify s (Var variable) value)
            (Ref.addRelation Ref.RelEq lhs rhs Ref.emptyStore)
          close bind r = continue (\s -> bind s (1-variable) 0) r
      accepted (close storeBind cancelledCurrent) === accepted (close Ref.storeBind cancelledReference)
    ) [Atom "bad", FloatLit 1.5, IntLit 3])
    [(Var 1, Compound "abs" [Compound "minus" [Var 0,Var 0]], 0),
     (Var 1, Compound "abs" [Compound "mul" [Var 0,IntLit 0]], 0),
     (Compound "minus" [Var 1,Var 1], Compound "abs" [Var 0], 1)]
  let expression = Compound "plus" [Var 0, IntLit 0]
      currentGlobal = continue (\s -> storeUnify s (Var 0) (Atom "bad"))
        (propagate emptyStore {stConstraints = [CAllDifferent [expression,Var 1]]})
      referencePair = continue (\s -> Ref.storeUnify s (Var 0) (Atom "bad"))
        (Ref.addRelation Ref.RelNe expression (Var 1) Ref.emptyStore)
  accepted currentGlobal === accepted referencePair

clpPerformanceGroup :: Group
clpPerformanceGroup = Group "CLP performance correctness"
  [ ("store_reference", prop_store_reference),
    ("absolute_alias_fixed_point", prop_absolute_alias_fixed_point),
    ("reification_model", prop_reification_model),
    ("absolute_model", prop_absolute_model),
    ("global_distinct_model", prop_global_distinct_model),
    ("propagation_regressions", prop_propagation_regressions)
  ]

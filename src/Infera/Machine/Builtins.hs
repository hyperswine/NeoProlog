-- | Pure dispatch for deterministic native arithmetic and CLP goals. Results
-- describe one transaction for the control driver; constraint algorithms
-- remain in the persistent store and language unification runs on the heap.
module Infera.Machine.Builtins
  ( Builtin (..),
    builtin,
    ordinaryBuiltin,
    dynamicCall,
    readFileContents,
  )
where

import Data.Char (toLower, toUpper)
import qualified Data.Map.Strict as Map
import Infera.Arith (compareNumeric, deepEval, evalArithSafe, evalNumeric)
import Infera.CLP
import Infera.Engine.Reference (Env (..), OutputEvent (..), Search, SearchItem (..), SolverState (..))
import Infera.Error (PredKey, SolveError (..), showPredKey)
import Infera.Program (nameHasFlag)
import Infera.Syntax (Flag (FlagDynamic), Term (..), functorOf, mkList, parseTerm, unfoldCons)
import Infera.Unify (Subst, canonicalize, deepWalk, emptySubst, instantiate, isGround, unifyPlain, walk)

data Builtin
  = NotBuiltin
  | Accept
  | Reject
  | Raise SolveError
  | Unify Term Term
  | Post (Store -> Either SolveError (Maybe Store))

-- | Preserve the reference evaluator's shallow outer walk. In particular,
-- raw variables inside a bound compound remain syntax for its builtin, while
-- a goal variable bound to a builtin compound is dispatched normally.
builtin :: Store -> Term -> Builtin
builtin store goal = case walk substitution goal of
  Compound "unify" [left, right] -> Unify left right
  Compound "equiv" [left, right] -> accept (deepWalk substitution left == deepWalk substitution right)
  Compound "neq" [left, right] -> Post (addDiseq left right)
  Compound "is" [left, right] -> case evalArithSafe substitution right of
    Left err -> Raise err
    Right Nothing -> Raise (InstantiationError (deepWalk substitution right))
    Right (Just value) -> Unify left value
  Compound "gt" [left, right] -> comparison (== GT) substitution left right
  Compound "lt" [left, right] -> comparison (== LT) substitution left right
  Compound "gte" [left, right] -> comparison (/= LT) substitution left right
  Compound "lte" [left, right] -> comparison (/= GT) substitution left right
  Compound "int_eq" [left, right] -> Post (addRelation RelEq left right)
  Compound "fd_ne" [left, right] -> Post (addRelation RelNe left right)
  Compound "fd_le" [left, right] -> Post (addRelation RelLe left right)
  Compound "fd_lt" [left, right] -> Post (addRelation RelLe (plusOne left) right)
  Compound "fd_ge" [left, right] -> Post (addRelation RelLe right left)
  Compound "fd_gt" [left, right] -> Post (addRelation RelLe (plusOne right) left)
  Compound "in" [target, range] -> inDomain substitution target range
  Compound "all_different" [terms] -> allDifferent substitution terms
  Compound "all_distinct" [terms] -> allDifferent substitution terms
  Compound "reify" [relation, truth] -> reifyRelation substitution relation truth
  _ -> NotBuiltin
  where
    substitution = stSubst store

accept :: Bool -> Builtin
accept True = Accept
accept False = Reject

plusOne :: Term -> Term
plusOne term = Compound "plus" [term, IntLit 1]

comparison :: (Ordering -> Bool) -> Subst -> Term -> Term -> Builtin
comparison ok substitution left right = case (walk substitution left, walk substitution right) of
  (CharLit a, CharLit b) -> accept (ok (compare a b))
  (StrLit a, StrLit b) -> accept (ok (compare a b))
  (Atom a, Atom b) -> accept (ok (compare a b))
  _ -> case (evalNumeric substitution left, evalNumeric substitution right) of
    (Left err, _) -> Raise err
    (_, Left err) -> Raise err
    (Right Nothing, _) -> Raise (InstantiationError (deepWalk substitution left))
    (_, Right Nothing) -> Raise (InstantiationError (deepWalk substitution right))
    (Right (Just a), Right (Just b)) -> accept (ok (compareNumeric a b))

parseBound :: Term -> Maybe Bound
parseBound (IntLit value) = Just (Fin value)
parseBound (Atom "inf") = Just NegInf
parseBound (Atom "sup") = Just PosInf
parseBound _ = Nothing

inDomain :: Subst -> Term -> Term -> Builtin
inDomain substitution target range = case deepWalk substitution range of
  Compound "range" [lo, hi]
    | Just lower <- parseBound lo,
      Just upper <- parseBound hi ->
        let targets = case deepWalk substitution target of
              terms@(Compound "cons" _) -> fst (unfoldCons terms)
              term -> [term]
         in Post (addDomains targets lower upper)
  other -> Raise (TypeError "range (Lo..Hi)" other)

allDifferent :: Subst -> Term -> Builtin
allDifferent substitution terms =
  let list = deepWalk substitution terms
      (items, rest) = unfoldCons list
   in case rest of
        Just _ -> Raise (InstantiationError list)
        Nothing -> Post (addAllDifferent items)

reifyRelation :: Subst -> Term -> Term -> Builtin
reifyRelation substitution relation truth = case walk substitution relation of
  Compound "int_eq" [left, right] -> post RelEq left right
  Compound "fd_ne" [left, right] -> post RelNe left right
  Compound "fd_le" [left, right] -> post RelLe left right
  Compound "fd_lt" [left, right] -> post RelLe (plusOne left) right
  Compound "fd_ge" [left, right] -> post RelLe right left
  Compound "fd_gt" [left, right] -> post RelLe (plusOne right) left
  other@(Var _) -> Raise (InstantiationError other)
  other -> Raise (TypeError "integer relation (#=, #!=, #<, #<=, #>, #>=)" other)
  where
    post rel left right = Post (addReified rel left right truth)

-- | Ordinary builtins perform no recursive resolution. Their finite answer
-- iterators belong to the native driver's choice points, so retries restore
-- the heap and the complete persistent state together. In particular output
-- and dynamic facts remain branch-local, and enumeration is demand-driven.
--
-- As for 'builtin', only the outer goal is walked. Deep evaluation is done
-- exactly where each language builtin requests it; normalizing the whole
-- goal first would change shallow control and malformed-input behavior.
ordinaryBuiltin :: Env -> SolverState -> Term -> Maybe Search
ordinaryBuiltin environment state original = case walk substitution original of
  Atom "nl" -> one (emit NewlineEvent state)
  Compound "read_file" [path, result] -> Just $ withFile environment substitution path $ \contents ->
    checked state (storeUnify store result (StrLit contents))
  Compound "assert" [fact] -> Just (assertFact environment state fact)
  Compound "retract" [fact] -> Just (retractFact state fact)
  Compound "retractall" [fact] -> Just (retractAll state fact)
  Compound "seq" [items, input, rest] -> Just (seqGoal state items input rest)
  Compound "wr" [value, input, rest] -> Just (dcgText state (showValue (deepEval substitution value)) input rest)
  Compound "nl" [input, rest] -> Just (dcgText state "\n" input rest)
  Compound "sp" [input, rest] -> Just (dcgText state " " input rest)
  Compound "padl" [value, width, input, rest] -> Just (padGoal True state value width input rest)
  Compound "padr" [value, width, input, rest] -> Just (padGoal False state value width input rest)
  Compound "fmt" [format, arguments, input, rest] -> Just $ case formatText substitution format arguments of
    Left err -> [BranchError err]
    Right text -> dcgText state text input rest
  Compound "char_code" [character, number] -> Just $ case (walk substitution character, walk substitution number) of
    (CharLit value, _) -> checked state (storeUnify store number (IntLit (fromIntegral (fromEnum value))))
    (_, IntLit value) -> checked state (storeUnify store character (CharLit (toEnum (fromIntegral value))))
    (other, _) -> [BranchError (InstantiationError other)]
  Compound "term_str" [term, text] -> Just (checked state (storeUnify store text (StrLit (showValue (deepEval substitution term)))))
  Compound "str_lines" [text, items] -> Just $ case walk substitution text of
    StrLit contents -> checked state (storeUnify store items (mkList (map StrLit (lines contents)) Nothing))
    other -> [BranchError (TypeError "string" other)]
  Compound "write" [value] -> output value
  Compound "print" [value] -> output value
  Compound "writeln" [value] -> one (emit NewlineEvent (emit (WriteEvent (showValue (deepEval substitution value))) state))
  Compound "var" [term] -> yesNo (isVar (walk substitution term))
  Compound "nonvar" [term] -> yesNo (not (isVar (walk substitution term)))
  Compound "ground" [term] -> yesNo (isGround substitution term)
  Compound "is_int" [term] -> yesNo (case walk substitution term of IntLit _ -> True; _ -> False)
  Compound "is_float" [term] -> yesNo (case walk substitution term of FloatLit _ -> True; _ -> False)
  Compound "is_num" [term] -> yesNo (case walk substitution term of IntLit _ -> True; FloatLit _ -> True; _ -> False)
  Compound "is_str" [term] -> yesNo (case walk substitution term of StrLit _ -> True; _ -> False)
  Compound "is_atom" [term] -> yesNo (case walk substitution term of Atom _ -> True; _ -> False)
  Compound "is_char" [term] -> yesNo (case walk substitution term of CharLit _ -> True; _ -> False)
  Compound "is_list" [term] -> yesNo (isProperList substitution term)
  Compound "str_concat" [left, right, result] -> Just (strConcat state left right result)
  Compound "str_length" [text, number] -> Just $ case walk substitution text of
    StrLit contents -> checked state (storeUnify store number (IntLit (fromIntegral (length contents))))
    other -> [BranchError (TypeError "string" other)]
  Compound "str_chars" [text, characters] -> Just $ case walk substitution text of
    StrLit contents -> checked state (storeUnify store characters (mkList (map CharLit contents) Nothing))
    Var _ -> case deepWalk substitution characters of
      term | Just contents <- charList term -> checked state (storeUnify store text (StrLit contents))
      other -> [BranchError (InstantiationError other)]
    other -> [BranchError (TypeError "string" other)]
  Compound "str_atom" [text, atom] -> Just $ case (walk substitution text, walk substitution atom) of
    (StrLit contents, _) -> checked state (storeUnify store atom (Atom contents))
    (_, Atom name) -> checked state (storeUnify store text (StrLit name))
    (other, _) -> [BranchError (InstantiationError other)]
  Compound "str_num" [text, number] -> Just $ case (walk substitution text, walk substitution number) of
    (StrLit contents, _) -> case parseTerm contents of
      Right value@(IntLit _) -> checked state (storeUnify store number value)
      Right value@(FloatLit _) -> checked state (storeUnify store number value)
      _ -> []
    (_, value@(IntLit _)) -> checked state (storeUnify store text (StrLit (show value)))
    (_, value@(FloatLit _)) -> checked state (storeUnify store text (StrLit (show value)))
    (other, _) -> [BranchError (InstantiationError other)]
  Compound "str_upper" [left, right] -> Just (strMap toUpper state left right)
  Compound "str_lower" [left, right] -> Just (strMap toLower state left right)
  _ -> Nothing
  where
    store = ssStore state
    substitution = stSubst store
    one accepted = Just [Found accepted]
    yesNo accepted = Just [Found state | accepted]
    output value = one (emit (WriteEvent (showValue (deepEval substitution value))) state)
    isVar (Var _) = True
    isVar _ = False

checked :: SolverState -> Either SolveError (Maybe Store) -> Search
checked _ (Left err) = [BranchError err]
checked _ (Right Nothing) = []
checked state (Right (Just store)) = [Found state {ssStore = store}]

emit :: OutputEvent -> SolverState -> SolverState
emit event state = state {ssOutput = event : ssOutput state, ssOutLen = ssOutLen state + 1}

showValue :: Term -> String
showValue (StrLit contents) = contents
showValue term = show term

isProperList :: Subst -> Term -> Bool
isProperList substitution term = case walk substitution term of
  Atom "nil" -> True
  Compound "cons" [_, rest] -> isProperList substitution rest
  _ -> False

charList :: Term -> Maybe String
charList term = case unfoldCons term of
  (characters, Nothing) -> mapM (\character -> case character of CharLit value -> Just value; _ -> Nothing) characters
  _ -> Nothing

strConcat :: SolverState -> Term -> Term -> Term -> Search
strConcat state left right result =
  case (walk substitution left, walk substitution right, walk substitution result) of
    (StrLit x, StrLit y, _) -> checked state (storeUnify store result (StrLit (x ++ y)))
    (_, _, StrLit contents) -> concat
      [ checked state (storeUnify store left (StrLit prefix) >>= maybe (Right Nothing) (\next -> storeUnify next right (StrLit suffix)))
      | index <- [0 .. length contents], let (prefix, suffix) = splitAt index contents
      ]
    (x, y, _) -> [BranchError (InstantiationError (if isString x then y else x))]
  where
    substitution = stSubst store
    store = ssStore state
    isString (StrLit _) = True
    isString _ = False

strMap :: (Char -> Char) -> SolverState -> Term -> Term -> Search
strMap function state left right = case walk (stSubst (ssStore state)) left of
  StrLit contents -> checked state (storeUnify (ssStore state) right (StrLit (map function contents)))
  other -> [BranchError (TypeError "string" other)]

-- The contents are preloaded by the program loader. The solver performs no
-- file IO and reports the same missing-path error as the language runtime.
readFileContents :: Env -> Store -> Term -> Either SolveError String
readFileContents environment store path = readFilePath environment (stSubst store) path

readFilePath :: Env -> Subst -> Term -> Either SolveError String
readFilePath environment substitution path = case walk substitution path of
  StrLit name -> case Map.lookup name (envFiles environment) of
    Just contents -> Right contents
    Nothing -> Left (UserError ("read_file: \"" ++ name ++ "\" was not loaded (paths must be string literals in the program or query)"))
  other -> Left (TypeError "file path string" other)

withFile :: Env -> Subst -> Term -> (String -> Search) -> Search
withFile environment substitution path continuation =
  either (\err -> [BranchError err]) continuation (readFilePath environment substitution path)

dcgText :: SolverState -> String -> Term -> Term -> Search
dcgText state text input rest = checked state (storeUnify (ssStore state) input (mkList (map CharLit text) (Just rest)))

seqGoal :: SolverState -> Term -> Term -> Term -> Search
seqGoal state items input rest = case deepWalk substitution items of
  StrLit contents -> dcgText state contents input rest
  term | (xs, Nothing) <- unfoldCons term -> checked state (storeUnify store input (mkList xs (Just rest)))
  _ -> case deepWalk substitution input of
    term | (xs, Nothing) <- unfoldCons term -> concat
      [ checked state (storeUnify store items (mkList prefix Nothing) >>= maybe (Right Nothing) (\next -> storeUnify next rest (mkList suffix Nothing)))
      | index <- [0 .. length xs], let (prefix, suffix) = splitAt index xs
      ]
    other -> [BranchError (InstantiationError other)]
  where
    store = ssStore state
    substitution = stSubst store

padGoal :: Bool -> SolverState -> Term -> Term -> Term -> Term -> Search
padGoal left state value width input rest = case walk substitution width of
  IntLit number ->
    let text = showValue (deepEval substitution value)
        padding = replicate (fromIntegral number - length text) ' '
     in dcgText state (if left then padding ++ text else text ++ padding) input rest
  other -> [BranchError (TypeError "integer width" other)]
  where
    substitution = stSubst (ssStore state)

formatText :: Subst -> Term -> Term -> Either SolveError String
formatText substitution format arguments = case (walk substitution format, unfoldCons (deepWalk substitution arguments)) of
  (StrLit contents, (values, Nothing)) -> go contents values
  (StrLit _, _) -> Left (TypeError "argument list" (deepWalk substitution arguments))
  (other, _) -> Left (TypeError "format string" other)
  where
    go ('~' : '~' : rest) values = ('~' :) <$> go rest values
    go ('~' : 'n' : rest) values = ('\n' :) <$> go rest values
    go ('~' : directiveName : rest) (value : values) | directiveName `elem` "wsda" = do
      piece <- directive directiveName (deepEval substitution value)
      (piece ++) <$> go rest values
    go ('~' : directiveName : _) [] | directiveName `elem` "wsda" = Left (UserError "fmt: not enough arguments for the format string")
    go ('~' : directiveName : _) _ = Left (UserError ("fmt: unknown directive ~" ++ [directiveName]))
    go (character : rest) values = (character :) <$> go rest values
    go [] [] = Right []
    go [] _ = Left (UserError "fmt: too many arguments for the format string")
    directive 'w' term = Right (showValue term)
    directive 'a' (Atom name) = Right name
    directive 'd' (IntLit number) = Right (show number)
    directive 's' (StrLit contents) = Right contents
    directive 's' term | Just contents <- charList term = Right contents
    directive name term = Left (TypeError (case name of 'd' -> "integer for ~d"; 'a' -> "atom for ~a"; _ -> "string for ~s") term)

dynamicKey :: Env -> Subst -> Term -> Either SolveError (PredKey, Term)
dynamicKey environment substitution term =
  let fact = deepWalk substitution term
   in case functorOf fact of
        Nothing -> Left (TypeError "callable fact" fact)
        Just key@(name, _)
          | nameHasFlag (envProg environment) name FlagDynamic -> Right (key, fact)
          | otherwise -> Left (UserError (showPredKey key ++ " is not declared dynamic (add `" ++ name ++ " : dynamic.`)"))

assertFact :: Env -> SolverState -> Term -> Search
assertFact environment state term = case dynamicKey environment (stSubst (ssStore state)) term of
  Left err -> [BranchError err]
  Right (key, fact) ->
    let (canonical, variables) = canonicalize emptySubst fact
     in [Found state {ssDynamic = Map.insertWith (flip (++)) key [(canonical, length variables)] (ssDynamic state)}]

dynamicFacts :: SolverState -> PredKey -> [(Int, Term, SolverState)]
dynamicFacts state key =
  [ (index, instantiate (ssFresh state) canonical, state {ssFresh = ssFresh state + count})
  | (index, (canonical, count)) <- zip [0 ..] (Map.findWithDefault [] key (ssDynamic state))
  ]

-- | Resolve only the branch-local asserted facts. The control driver still
-- owns declared contracts, static clauses, fuel and the enclosing cut scope.
dynamicCall :: SolverState -> PredKey -> Term -> Search
dynamicCall state key goal = concat
  [checked freshState (storeUnify (ssStore freshState) goal fact) | (_, fact, freshState) <- dynamicFacts state key]

retractFact :: SolverState -> Term -> Search
retractFact state term = case functorOf (deepWalk substitution term) of
  Nothing -> [BranchError (TypeError "callable fact" term)]
  Just key -> concat
    [ checked (dropFact key index freshState) (storeUnify (ssStore freshState) term fact)
    | (index, fact, freshState) <- dynamicFacts state key
    ]
  where
    substitution = stSubst (ssStore state)
    dropFact key index freshState = freshState
      {ssDynamic = Map.adjust (\facts -> [fact | (other, fact) <- zip [0 :: Int ..] facts, other /= index]) key (ssDynamic freshState)}

retractAll :: SolverState -> Term -> Search
retractAll state term = case functorOf (deepWalk (stSubst (ssStore state)) term) of
  Nothing -> [BranchError (TypeError "callable fact" term)]
  Just key ->
    let originals = Map.findWithDefault [] key (ssDynamic state)
        kept = [originals !! index | (index, fact, freshState) <- dynamicFacts state key,
          Nothing <- [unifyPlain (stSubst (ssStore freshState)) term fact]]
     in [Found state {ssDynamic = Map.insert key kept (ssDynamic state)}]

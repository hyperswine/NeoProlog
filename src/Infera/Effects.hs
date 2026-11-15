-- | The single registry shared by checking and the effect runner.
module Infera.Effects (effectKeys, isEffect, effectViolations) where
import Infera.Syntax
import Infera.Program
import qualified Data.IntMap.Strict as IM

-- Arities include the hidden world pair.
effectKeys :: [(String,Int)]
effectKeys = [("open",5),("close",3),("say",3),("say",4),("say_to",4),("say_to",5),
  ("write",5),("write_bytes",5),("read_line",4),("read_chars",5),("read_bytes",5),
  ("phrase_from",4),("phrase_from_file",4),("accept",4),("wait",5),("send_to",6),("recv_from",5),
  ("getenv",4),("now",3),("monotonic",3),("sleep",3),("random_seed",3),
  ("list_dir",4),("stat",4),("remove",4),("rename",5),("make_dir",4),("halt",3),
  ("handle_address",4)]
isEffect :: Term -> Bool
isEffect t = maybe False (`elem` effectKeys) (functorOf t)

-- Check explicit world use and provable effects in nondeterministic contexts.
-- Runtime checks remain authoritative for dynamic calls and aliasing.
effectViolations :: Program -> [(PredKey,String)]
effectViolations p = concat
  [check pred cl | pred <- programPreds p, cl <- IM.elems (predClauses pred)]
  where
    io pred = FlagIo `elem` effectiveFlags p pred
    effect t = isEffect t || case functorOf t >>= (`lookupPred` p) of
      Just q -> io q
      _ -> False
    check pred cl = [(predKey pred,"effects require an io declaration") | not (io pred), any contains (clauseBody cl)]
      ++ [(predKey pred,"an effect cannot occur in a backtracking or collecting scope") | any forbidden (clauseBody cl)]
      ++ [(predKey pred,"world values must form one linear chain") | io pred, not (linear cl)]
    contains t = effect t || case t of Compound _ xs -> any contains xs; _ -> False
    forbidden t = case t of
      Compound f xs | f `elem` ["findall","bagof","setof","not","forall","minimize"] -> any contains xs
      Compound _ xs -> any forbidden xs
      _ -> False
    -- The DCG translator guarantees this for ordinary grammar syntax. Check
    -- manually written io clauses too, without inferring from variable names.
    linear cl = case clauseHead cl of
      Compound _ hs | length hs >= 2 ->
        case paths (hs !! (length hs-2)) [] (clauseBody cl) of
          Nothing -> False
          Just ends -> all (\(end,pairs)->canonical pairs end == canonical pairs (last hs)) ends
      _ -> False
    canonical pairs (Var v)=Var(root pairs v)
    canonical _ t=t
    root pairs v = minimum (closure [v])
      where closure seen = let next=seen ++ [b | (a,b)<-pairs,a `elem` seen,b `notElem` seen]
                                         ++ [a | (a,b)<-pairs,b `elem` seen,a `notElem` seen]
                           in if length next==length seen then seen else closure next
    paths current pairs [] = Just [(current,pairs)]
    paths current pairs (g:gs) = case g of
      Compound "," [a,b] -> paths current pairs (a:b:gs)
      Compound ";" [Compound "->" [c,t],e] | not(contains c) -> do
        conditions<-paths current pairs [c]
        yes<-concat <$> mapM (\(w,ps)->paths w ps [t]) conditions
        no<-paths current pairs [e]
        concat <$> mapM (\(w,ps)->paths w ps gs) (yes++no)
      Compound "->" [c,t] | not(contains c) -> paths current pairs (c:t:gs)
      Compound ";" [a,b] | not(contains g) -> do
        left<-paths current pairs [a]; right<-paths current pairs [b]
        concat <$> mapM (\(w,ps)->paths w ps gs) (left++right)
      Compound "unify" [Var a,Var b] -> paths current ((a,b):pairs) gs
      Compound _ xs | effect g, length xs >= 2 ->
        let a=canonical pairs (xs !! (length xs-2)); b=canonical pairs(last xs)
        in if a == canonical pairs current && a /= b then paths b pairs gs else Nothing
      _ | contains g -> Nothing
        | otherwise -> paths current pairs gs

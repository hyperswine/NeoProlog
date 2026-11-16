{-# LANGUAGE TemplateHaskell #-}
-- | Shipped, embedded standard modules; no installation-relative paths.
module Infera.Standard (standardModule, expandStandard, standardItems) where
import Infera.Syntax
import qualified Data.Set as Set
import Language.Haskell.TH.Syntax (addDependentFile, lift, runIO)

sources :: [(String,String)]
sources = $(do
  let names = ["list","order","aggregate","assoc","str","dcg","coroutine","io","net","os"]
  pairs <- mapM (\n -> do
    let path = "std/" ++ n ++ ".nprolog"
    addDependentFile path
    src <- runIO (readFile path)
    pure ("std/" ++ n,src)) names
  lift pairs)

standardModule :: String -> Either String [LocatedTopLevel]
standardModule name = maybe (Left ("Unknown standard module: " ++ name)) id (lookup name parsedModules)

parsedModules :: [(String, Either String [LocatedTopLevel])]
parsedModules = [(name,parse name src) | (name,src) <- sources]
  where
  parse name src = either (Left . snd) Right (parseLocatedFile ("<" ++ name ++ ">") src)

-- | User clauses shadow the whole library predicate, including declarations.
-- Modules are expanded once per load and all std names remain unqualified.
expandStandard :: [LocatedTopLevel] -> Either String [LocatedTopLevel]
expandStandard items = do
  let noPrelude = any ((== TLDirective [Atom "noprelude"]) . locatedItem) items
      requested = [name | i <- items, TLDirective [Compound "import" [StrLit name]] <- [locatedItem i], take 4 name == "std/"]
  (_,lib) <- gather Set.empty (requested ++ if noPrelude then [] else ["std/list","std/order","std/aggregate"])
  let own = [i | i <- items, not (directive (locatedItem i))]
      keys = Set.fromList [key | i <- own, TLClause c <- [locatedItem i], Just key <- [clauseKey c]]
      names = Set.map fst keys
      -- A flags-only declaration covers every arity of its name, so any user
      -- clause of that name shadows it, not only one of the same arity.
      keep i = case locatedItem i of
        TLClause c -> maybe True (`Set.notMember` keys) (clauseKey c)
        TLDecl d | null (declArgs d) && declDet d == Nothing -> Set.notMember (declName d) names
        TLDecl d -> Set.notMember (declName d,length (declArgs d)) keys
        _ -> False
  pure (filter keep lib ++ own)
  where
    directive (TLDirective [Atom "noprelude"]) = True
    directive (TLDirective [Compound "import" [StrLit n]]) = take 4 n == "std/"
    directive _ = False
    gather seen [] = Right (seen,[])
    gather seen (name:rest)
      | Set.member name seen = gather seen rest
      | otherwise = do
        xs <- standardModule name
        let deps = [n | i <- xs, TLDirective [Compound "import" [StrLit n]] <- [locatedItem i]]
        (visited,before) <- gather (Set.insert name seen) deps
        (done,after) <- gather visited rest
        pure (done,before ++ [i | i <- xs, not (directive (locatedItem i))] ++ after)

standardItems :: [TopLevel] -> Either String [TopLevel]
standardItems items = do
  sample <- either (Left . snd) Right (parseLocatedFile "<standard>" "true.")
  case sample of
    i:_ -> map locatedItem <$> expandStandard [i {locatedItem=x} | x <- items]
    _ -> Left "Cannot create standard source location"

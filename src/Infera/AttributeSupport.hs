module Infera.AttributeSupport (attributeNames, usesAttributes) where
import Infera.Program
import Infera.Syntax
import qualified Data.IntMap.Strict as IM
import Data.List (isSuffixOf)
attributeNames :: [String]
attributeNames=["put_attr","get_attr","del_attr","copy_term_nat"]
usesAttributes :: Program -> [Term] -> Bool
usesAttributes p gs = any named [fst(predKey q) | q<-programPreds p] || any term (gs ++ concat [clauseHead cl:clauseBody cl | q<-programPreds p,cl<-IM.elems(predClauses q)])
  where named n=n `elem` attributeNames || "attr_unify_hook" `isSuffixOf` n || "attribute_goals" `isSuffixOf` n
        term (Atom n)=named n
        term (Compound n xs)=named n || any term xs
        term _=False

-- | Immutable, source-owned clause plans. Compilation is lazy and depends
-- only on clause syntax; runtime flags, contracts and source maps belong to
-- the program snapshot that selects the clause.
--
-- 'Infera.Program.Pred' is a public record, so callers may replace its clauses
-- without refreshing this cache. Every lookup therefore checks an exact
-- source witness before reusing a plan. The machine memoizes this check once
-- per selected clause in each query, including unsupported clauses.
module Infera.Compile.Cache
  ( ClauseCache,
    emptyClauseCache,
    insertClause,
    buildClauseCache,
    lookupClauseCode,
  )
where

import Data.IntMap.Strict (IntMap)
import qualified Data.IntMap.Strict as IM
import GHC.Float (castDoubleToWord64)
import Infera.Compile (ClauseCode, compileClause)
import Infera.Syntax (Clause (..), Term (..))

-- The plan field must stay lazy: loading or showing a predicate must not
-- compile clauses that no query reaches. Reusing this immutable entry also
-- shares the evaluated plan across queries and table-producer startups.
data CachedClause = CachedClause !Clause (Maybe ClauseCode)

newtype ClauseCache = ClauseCache (IntMap CachedClause)

-- Do not force plan thunks while displaying the public predicate record.
instance Show ClauseCache where
  showsPrec precedence (ClauseCache entries) =
    showParen (precedence > 10) (showString "ClauseCache " . shows (IM.size entries))

emptyClauseCache :: ClauseCache
emptyClauseCache = ClauseCache IM.empty

-- | Replace one source witness and its lazy plan, retaining every other
-- entry. Older immutable caches and checkpoints keep their original plans.
insertClause :: Int -> Clause -> ClauseCache -> ClauseCache
insertClause ordinal clause (ClauseCache entries) =
  ClauseCache (IM.insert ordinal (cachedClause clause) entries)

buildClauseCache :: IntMap Clause -> ClauseCache
buildClauseCache = ClauseCache . IM.map cachedClause

cachedClause :: Clause -> CachedClause
cachedClause clause = CachedClause clause (compileClause clause)

-- | Return whether the source witness matched and the corresponding lazy
-- compilation result. A missing or stale witness compiles the actual source
-- instead. In particular, 'Nothing' is a valid cached fallback result.
lookupClauseCode :: Int -> Clause -> ClauseCache -> (Bool, Maybe ClauseCode)
lookupClauseCode ordinal clause (ClauseCache entries) =
  case IM.lookup ordinal entries of
    Just (CachedClause source code) | sameClause source clause -> (True, code)
    _ -> (False, compileClause clause)

sameClause :: Clause -> Clause -> Bool
sameClause left right =
  clauseNVars left == clauseNVars right
    && sameTerm (clauseHead left) (clauseHead right)
    && sameTerms (clauseBody left) (clauseBody right)

sameTerms :: [Term] -> [Term] -> Bool
sameTerms [] [] = True
sameTerms (left : lefts) (right : rights) =
  sameTerm left right && sameTerms lefts rights
sameTerms _ _ = False

-- Derived Term equality equates signed zero and rejects identical NaNs.
-- Both are wrong for source identity: construction retains exact scalar bits.
sameTerm :: Term -> Term -> Bool
sameTerm (Atom left) (Atom right) = left == right
sameTerm (Var left) (Var right) = left == right
sameTerm (IntLit left) (IntLit right) = left == right
sameTerm (FloatLit left) (FloatLit right) =
  castDoubleToWord64 left == castDoubleToWord64 right
sameTerm (CharLit left) (CharLit right) = left == right
sameTerm (StrLit left) (StrLit right) = left == right
sameTerm (Compound leftName left) (Compound rightName right) =
  leftName == rightName && sameTerms left right
sameTerm _ _ = False

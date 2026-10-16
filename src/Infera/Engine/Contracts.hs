-- | Predicate contracts shared by the reference resolver and the explicit
-- control machine.  Callers supply terms already dereferenced in their own
-- representation so both drivers make the same mode, sort and determinism
-- decisions.
module Infera.Engine.Contracts
  ( selectSignature,
    sortMatches,
    checkOutputs,
    commitsAfterSuccess,
    requiredSuccess,
  )
where

import Infera.Error
import Infera.Program
import Infera.Syntax
import Infera.Unify (isGroundTerm)

-- | Pick the declared signature matching the call (first whose input args
-- are ground), checking sorts of bound arguments.  Nothing when undeclared.
selectSignature :: PredKey -> Pred -> [Term] -> Either SolveError (Maybe Signature)
selectSignature key p argsW = case predDecls p of
  [] -> Right Nothing
  sigs ->
    case [sig | sig <- sigs, all inOk (zip (sigArgs sig) argsW)] of
      (sig : _) -> do
        mapM_ (checkSort key) (zip3 [1 ..] (sigArgs sig) argsW)
        Right (Just sig)
      [] ->
        let bad = [(i, a) | sig <- take 1 sigs, (i, ArgSpec _ ModeIn, a) <- zip3 [1 ..] (sigArgs sig) argsW, not (isGroundTerm a)]
         in case bad of
              ((i, a) : _) -> Left (ModeError key i a)
              [] -> Right Nothing
  where
    inOk (ArgSpec _ ModeIn, a) = isGroundTerm a
    inOk _ = True

checkSort :: PredKey -> (Int, ArgSpec, Term) -> Either SolveError ()
checkSort key (i, ArgSpec sort _, a)
  | sortMatches sort a = Right ()
  | otherwise = Left (SortError key i sort a)

-- | Does a (dereferenced) term conform to a sort?  Unbound parts always do.
sortMatches :: Sort -> Term -> Bool
sortMatches sort t = case (sort, t) of
  (_, Var _) -> True
  (SAny, _) -> True
  (SNone, _) -> True
  (SInt, IntLit _) -> True
  (SFloat, FloatLit _) -> True
  (SNum, IntLit _) -> True
  (SNum, FloatLit _) -> True
  (SStr, StrLit _) -> True
  (SChar, CharLit _) -> True
  (SAtom, Atom _) -> True
  (SList _, Atom "nil") -> True
  (SList e, Compound "cons" [h, tl]) -> sortMatches e h && sortMatches (SList e) tl
  _ -> False

-- | The first post-call error: output arguments must be ground and every
-- argument must match its declared sort.  Terms are already dereferenced.
checkOutputs :: PredKey -> Signature -> [Term] -> Maybe SolveError
checkOutputs key sig argsW = case problems of
  (e : _) -> Just e
  [] -> Nothing
  where
    problems =
      [ err
      | (i, ArgSpec sort mode, a) <- zip3 [1 ..] (sigArgs sig) argsW,
        err <- outErr i sort mode a
      ]
    outErr i sort mode a
      | mode == ModeOut && not (isGroundTerm a) = [OutputModeError key i a]
      | not (sortMatches sort a) = [SortError key i sort a]
      | otherwise = []

-- | Whether a successful, output-checked call commits to its first result.
-- Inferred semidet is trusted only when every inferred switch is ground.
commitsAfterSuccess :: Pred -> Maybe Signature -> [Term] -> Bool
commitsAfterSuccess p msig argsW = case msig of
  Just sig -> sigDet sig == Det || sigDet sig == Semidet
  Nothing ->
    let inf = predInferred p
        switchGround = all (\i -> i < length argsW && isGroundTerm (argsW !! i)) (sigSwitch inf)
     in sigDet inf == Semidet && switchGround

-- | Declared contracts requiring at least one output-checked solution.
requiredSuccess :: Maybe Signature -> Maybe Det
requiredSuccess (Just sig) = case sigDet sig of
  Det -> Just Det
  Multi -> Just Multi
  _ -> Nothing
requiredSuccess Nothing = Nothing

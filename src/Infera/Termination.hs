-- | Public termination analysis, using the compiler's groundness facts.
module Infera.Termination
  ( module Infera.Termination.Analysis, verdicts ) where
import Infera.Termination.Analysis
import Infera.Infer (groundDependencies, inferProgram, builtinDet)
import Infera.Program
import qualified Data.Map.Strict as Map
verdicts :: Program -> Map.Map PredKey Verdict
verdicts p = let inferred = inferProgram p in verdictsWith builtinDet (groundDependencies inferred) inferred

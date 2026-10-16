{-# LANGUAGE OverloadedStrings #-}

-- Tail-frame retirement needs a closed first-order call graph rather than a
-- syntactic self-recursion test. These tests distinguish source eligibility
-- from the runtime continuation/contract checks that authorize actual reuse.
module MachineTailProofTest (machineTailProofGroup) where

import Control.Monad (forM_)
import Hedgehog hiding (Var)
import qualified Hedgehog.Gen as Gen
import qualified Hedgehog.Range as Range
import qualified Infera.Engine.Reference as Reference
import qualified Infera.Machine.Control as Machine
import qualified Infera.Machine.Tail as Tail
import Infera.Program
import Infera.Syntax

unit :: PropertyT IO () -> Property
unit = withTests 1 . property

name :: Int -> String
name index = "p" ++ show index

cycleItems :: Int -> [TopLevel]
cycleItems count = TLDirective [Atom "notable"] : concat
  [ [ TLClause (Clause (Compound (name index) [IntLit 0]) [] 0),
      TLClause (Clause (Compound (name index) [Var 0])
        [ Compound "gt" [Var 0, IntLit 0],
          Compound "is" [Var 1, Compound "minus" [Var 0, IntLit 1]],
          Compound (name ((index + 1) `mod` count)) [Var 1]
        ] 2)
    ]
  | index <- [0 .. count - 1]
  ]

eligible :: Program -> (String, Int) -> PropertyT IO Bool
eligible program key = case lookupPred key program of
  Nothing -> annotateShow key >> failure
  Just definition -> pure (Tail.eligiblePredicate program definition)

prop_generated_pure_mutual_cycles :: Property
prop_generated_pure_mutual_cycles = withTests 200 . property $ do
  count <- forAll (Gen.int (Range.linear 1 8))
  let program = buildProgram (cycleItems count)
  forM_ [0 .. count - 1] $ \index -> eligible program (name index, 1) >>= (=== True)

prop_generated_recursive_edge_does_not_hide_effect :: Property
prop_generated_recursive_edge_does_not_hide_effect = withTests 300 . property $ do
  count <- forAll (Gen.int (Range.linear 1 8))
  poisoned <- forAll (Gen.int (Range.linear 0 (count - 1)))
  bad <- forAll (Gen.element
    [ Var 0,
      Atom "!",
      Compound "call" [Atom "true"],
      Compound "once" [Atom "true"],
      Compound "not" [Atom "false"],
      Compound "in" [Var 0, Compound "range" [IntLit 0, IntLit 1]],
      Compound "neq" [Var 0, IntLit 2],
      Compound "write" [Atom "value"],
      Compound "str_length" [StrLit "text", Var 0],
      Compound "unify" [Var 0, Compound "box" [Compound "$cut" [IntLit 1]]],
      Atom "unknown"
    ])
  -- The safe recursive edge comes first in this extra clause; checking only
  -- a visited SCC edge and returning early would incorrectly admit bad.
  let extra = TLClause (Clause (Compound (name poisoned) [Var 0])
        [Compound (name ((poisoned + 1) `mod` count)) [Var 0], bad] 1)
      program = buildProgram (cycleItems count ++ [extra])
  forM_ [0 .. count - 1] $ \index -> eligible program (name index, 1) >>= (=== False)

prop_generated_reachable_flags_reject :: Property
prop_generated_reachable_flags_reject = withTests 200 . property $ do
  count <- forAll (Gen.int (Range.linear 1 8))
  flagged <- forAll (Gen.int (Range.linear 0 (count - 1)))
  flag <- forAll (Gen.element [FlagUnsafe, FlagDynamic, FlagTable])
  let declaration = TLDecl (Decl (name flagged) Nothing [flag] [])
      program = buildProgram (cycleItems count ++ [declaration])
  forM_ [0 .. count - 1] $ \index -> eligible program (name index, 1) >>= (=== False)

prop_unreachable_bad_definitions_are_independent :: Property
prop_unreachable_bad_definitions_are_independent = unit $ do
  let extras =
        [ TLDecl (Decl "bad" Nothing [FlagUnsafe] []),
          TLClause (Clause (Atom "bad") [Compound "write" [Atom "effect"]] 0),
          TLClause (Clause (Compound "data" [Compound "box" [Compound "$cut" [IntLit 1]]]) [] 0),
          TLDecl (Decl (name 0) Nothing [FlagNoIndex] [])
        ]
      program = buildProgram (cycleItems 2 ++ extras)
  eligible program (name 0, 1) >>= (=== True)
  eligible program (name 1, 1) >>= (=== True)
  eligible program ("bad", 0) >>= (=== False)
  eligible program ("data", 1) >>= (=== False)

prop_completed_helpers_and_mutual_runtime_parity :: Property
prop_completed_helpers_and_mutual_runtime_parity = withTests 100 . property $ do
  count <- forAll (Gen.int (Range.linear 0 60))
  program <- evalEither . Reference.loadProgramText $ unlines
    [ "<- notable.",
      "decrement N M <- M is N - 1.",
      "even 0 done.",
      "even N R <- N > 0, decrement N M, odd M R.",
      "odd 0 done.",
      "odd N R <- N > 0, decrement N M, even M R."
    ]
  eligible program ("even", 2) >>= (=== True)
  eligible program ("odd", 2) >>= (=== True)
  eligible program ("decrement", 2) >>= (=== True)
  query <- evalEither (parseQuery ("even " ++ show count ++ " R?"))
  let expected = Reference.solveAll program query
      actual = Reference.summarizeSearch query (Machine.solveQuery program query)
  actual === expected
  map Reference.showAnswer (Reference.summaryAnswers actual) === ["R = done"]

prop_builtin_dispatch_precedes_redefinitions :: Property
prop_builtin_dispatch_precedes_redefinitions = unit $ do
  let program = buildProgram
        [ TLDirective [Atom "notable"],
          TLClause (Clause (Atom "caller") [Compound "write" [Atom "value"]] 0),
          TLClause (Clause (Compound "write" [Var 0]) [] 1),
          TLClause (Clause (Atom "arity") [Compound "gt" [IntLit 1]] 0),
          TLClause (Clause (Compound "gt" [Var 0]) [] 1),
          TLClause (Clause (Atom "missing") [Compound "gt" [IntLit 1, IntLit 0, IntLit 2]] 0)
        ]
  eligible program ("caller", 0) >>= (=== False)
  eligible program ("arity", 0) >>= (=== True)
  eligible program ("missing", 0) >>= (=== False)

prop_argument_contract_and_cut_data_gate :: Property
prop_argument_contract_and_cut_data_gate = unit $ do
  let signature = Just (defaultSignature 1)
      groundData = Compound "box" [mkList [IntLit 1, Atom "value"] Nothing]
      freeData = Compound "box" [Var 0, Var 0]
      cutData = Compound "box" [Compound "$cut" [IntLit 7]]
  Tail.eligibleArguments Nothing [freeData] === True
  Tail.eligibleArguments signature [groundData] === True
  Tail.eligibleArguments signature [freeData] === False
  Tail.eligibleArguments Nothing [cutData] === False
  Tail.eligibleArguments signature [cutData] === False

prop_source_eligibility_does_not_retire_non_tail_calls :: Property
prop_source_eligibility_does_not_retire_non_tail_calls = unit $ do
  program <- evalEither . Reference.loadProgramText $ unlines
    [ "<- notable.", "down 0.",
      "down N <- N > 0, M is N - 1, down M, true."
    ]
  eligible program ("down", 1) >>= (=== True)
  query <- evalEither (parseQuery "down 30?")
  initial <- evalEither (Machine.startMeasured program query)
  let drain checkpoint = do
        step <- Machine.resume checkpoint
        case step of
          Machine.Finished -> Right ([], checkpoint)
          Machine.Yield item next -> do
            (rest, final) <- drain next
            Right (item : rest, final)
  (items, final) <- evalEither (drain initial)
  Reference.summarizeSearch query items === Reference.solveAll program query
  Machine.metricTailCalls (Machine.checkpointMetrics final) === 0

-- Forty shared two-call levels used to require over a trillion independent
-- descendant visits. A single proof-wide visited set examines every clause
-- once, including a late hazard after an already-visited recursive edge.
prop_shared_diamond_and_late_cycle_hazard :: Property
prop_shared_diamond_and_late_cycle_hazard = unit $ do
  let depth = 40 :: Int
      node :: Int -> String
      node index = "diamond" ++ show index
      shared = TLDirective [Atom "notable"] :
        [ TLClause (Clause (Atom (node index))
            [Atom (node (index + 1)), Atom (node (index + 1))] 0)
        | index <- [0 .. depth - 1]
        ] ++
        [ TLClause (Clause (Atom (node depth)) [Atom "cycle_a"] 0),
          TLClause (Clause (Atom "cycle_a") [Atom "cycle_b", Atom "cycle_b"] 0),
          TLClause (Clause (Atom "cycle_b") [Atom "cycle_a", Atom "true"] 0)
        ]
      safe = buildProgram shared
      poisoned = buildProgram (shared ++
        [TLClause (Clause (Atom "cycle_b") [Atom "cycle_a", Compound "write" [Atom "bad"]] 0)])
  eligible safe (node 0, 0) >>= (=== True)
  eligible poisoned (node 0, 0) >>= (=== False)

machineTailProofGroup :: Group
machineTailProofGroup = Group "machine tail call proof"
  [ ("generated_pure_mutual_cycles", prop_generated_pure_mutual_cycles),
    ("generated_recursive_edge_does_not_hide_effect", prop_generated_recursive_edge_does_not_hide_effect),
    ("generated_reachable_flags_reject", prop_generated_reachable_flags_reject),
    ("unreachable_bad_definitions_are_independent", prop_unreachable_bad_definitions_are_independent),
    ("completed_helpers_and_mutual_runtime_parity", prop_completed_helpers_and_mutual_runtime_parity),
    ("builtin_dispatch_precedes_redefinitions", prop_builtin_dispatch_precedes_redefinitions),
    ("argument_contract_and_cut_data_gate", prop_argument_contract_and_cut_data_gate),
    ("source_eligibility_does_not_retire_non_tail_calls", prop_source_eligibility_does_not_retire_non_tail_calls),
    ("shared_diamond_and_late_cycle_hazard", prop_shared_diamond_and_late_cycle_hazard)
  ]

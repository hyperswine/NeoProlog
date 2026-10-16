{-# LANGUAGE OverloadedStrings #-}

-- General tail transfers and collection with live retry/opaque state. Keep
-- deterministic machine-state bounds separate from process residency gates.
module MachineGeneralTailTest (machineGeneralTailGroup) where

import Control.Exception (evaluate)
import Control.Monad (forM_)
import Hedgehog hiding (Var)
import qualified Hedgehog.Gen as Gen
import qualified Hedgehog.Range as Range
import Infera.CLP (Store (..))
import qualified Infera.Engine.Reference as Reference
import Infera.Error
import qualified Infera.Machine.Control as Machine
import qualified Infera.Machine.Heap as Heap
import Infera.Program (Program)
import Infera.Syntax
import Infera.Unify (canonicalize, emptySubst)

data Event
  = Answer String [Reference.OutputEvent]
  | Exhausted
  | Error String
  | Cut Int
  | Incomplete Term
  deriving (Eq, Show)

observe :: Query -> Reference.Search -> [Event]
observe query = map event
  where
    event item = case item of
      Reference.Found state ->
        let answer = Reference.projectAnswer query state
         in Answer (Reference.showAnswer answer) (Reference.answerOutput answer)
      Reference.BranchExhausted -> Exhausted
      Reference.BranchError err -> Error (show err)
      Reference.CutMarker owner -> Cut owner
      Reference.ConsumedIncomplete key -> Incomplete (fst (canonicalize emptySubst key))

unit :: PropertyT IO () -> Property
unit = withTests 1 . property

load :: String -> PropertyT IO Program
load text = annotate text >> evalEither (Reference.loadProgramText text)

queryText :: String -> PropertyT IO Query
queryText text = annotate text >> evalEither (parseQuery text)

source :: String
source = unlines
  [ "<- notable.",
    "result 0 done.",
    "result N R <- N > 0, M is N - 1, result M R.",
    "even 0 done.",
    "even N R <- N > 0, M is N - 1, odd M R.",
    "odd 0 done.",
    "odd N R <- N > 0, M is N - 1, even M R.",
    "step N M <- M is N - 1.",
    "helper 0 done.",
    "helper N R <- N > 0, step N M, helper M R.",
    "pick first.", "pick second.",
    "branch N R Choice <- pick Choice, result N R.",
    "scoped N Out <- Hidden = before, once (Carry = (box Leaf), Leaf = done, result N R), Out = (pair Hidden Carry).",
    "streamed N Out <- Hidden = before, call (Carry = (box Leaf), Leaf = done, result N R), Out = (pair Hidden Carry).",
    "conditional N Out <- Hidden = before, ((Carry = (box Leaf), Leaf = done, result N R) -> Out = (pair Hidden Carry) ; Out = bad).",
    "collected N Out <- Hidden = before, findall (box X) (X = done, result N R) List, Out = (pair Hidden List).",
    "render N -> { helper N R }, \"ok\".",
    "cached : table.", "cached X <- cached X.", "cached seed.",
    "fact : dynamic."
  ]

drain :: Machine.Checkpoint -> Either Heap.HeapError (Reference.Search, Machine.Checkpoint)
drain checkpoint = do
  step <- Machine.resume checkpoint
  case step of
    Machine.Finished -> pure ([], checkpoint)
    Machine.Yield item next -> do
      (rest, final) <- drain next
      pure (item : rest, final)

run :: Program -> Query -> PropertyT IO (Reference.Search, Machine.Metrics)
run program query = do
  initial <- evalEither (Machine.startMeasured program query)
  (items, final) <- evalEither (drain initial)
  _ <- evalIO (evaluate (length (show (observe query items))))
  pure (items, Machine.checkpointMetrics final)

compareQuery :: Program -> Query -> PropertyT IO (Reference.Search, Machine.Metrics)
compareQuery program query = do
  result'@(items, _) <- run program query
  observe query items === observe query (Reference.solveQuery program query)
  observe query items === observe query (Machine.solveQuery program query)
  pure result'

substitute :: Int -> String -> String
substitute _ [] = []
substitute count ('%' : rest) = show count ++ substitute count rest
substitute count (char : rest) = char : substitute count rest

prop_generated_general_tail_parity :: Property
prop_generated_general_tail_parity = withTests 200 . property $ do
  count <- forAll (Gen.int (Range.linear 0 80))
  context <- forAll (Gen.element
    [ "even % R?", "odd % R?", "helper % R?",
      "(even % R ; R = fallback)?", "branch % R Choice?",
      "once (even % R)?", "call (helper % R)?",
      "not (helper % R, fail)?",
      "(even % R -> R = done ; R = fallback)?",
      "findall (pair R Alias) (Alias = R, even % R) List?",
      "X in 1..3, Y #= X + 1, even % R, label [X, Y]?",
      "cached Before, helper % R, cached After?",
      "assert (fact seed), even % R, fact Saved?",
      "scoped % Out?", "streamed % Out?", "conditional % Out?", "collected % Out?"
    ])
  program <- load source
  query <- queryText (substitute count context)
  _ <- compareQuery program query
  pure ()

bounded :: Machine.Metrics -> PropertyT IO ()
bounded metrics = do
  assert (Machine.metricTailCalls metrics > 9000)
  assert (Machine.metricCollections metrics > 0)
  assert (Machine.metricMaxTasks metrics <= 64)
  assert (Machine.metricMaxChoices metrics <= 16)
  assert (Machine.metricMaxScopes metrics <= 4)
  assert (Machine.metricMaxCutOwners metrics <= 8)
  assert (Machine.metricMaxHeapCells metrics <= 32768)
  assert (Machine.metricMaxTrailEntries metrics <= 16384)
  assert (Machine.metricMaxBindings metrics <= 8192)
  assert (Machine.metricMaxSubstitutions metrics <= 8192)
  assert (Machine.metricMaxConstants metrics <= 8192)
  assert (Machine.metricMaxFunctors metrics <= 128)

prop_bounded_mutual_and_helper_frames :: Property
prop_bounded_mutual_and_helper_frames = unit $ do
  program <- load source
  forM_ ["even 10000 R?", "odd 10000 R?", "helper 10000 R?"] $ \text -> do
    query <- queryText text
    (items, metrics) <- run program query
    observe query items === [Answer "R = done" []]
    bounded metrics

prop_bounded_live_choice_rollback :: Property
prop_bounded_live_choice_rollback = unit $ do
  program <- load source
  forM_
    [ ("(even 10000 R ; R = fallback)?", [Answer "R = done" [], Answer "R = fallback" []]),
      ("(even 10000 R, fail ; R = fallback)?", [Answer "R = fallback" []]),
      ("branch 10000 R Choice?", [Answer "R = done, Choice = first" [], Answer "R = done, Choice = second" []]),
      ("Data = (box Leaf), (even 10000 R, Leaf = first ; Leaf = second)?",
       [Answer "Data = box first, Leaf = first, R = done" [], Answer "Data = box second, Leaf = second" []])
    ] $ \(text, expected) -> do
      query <- queryText text
      (items, metrics) <- compareQuery program query
      observe query items === expected
      bounded metrics

prop_bounded_opaque_scopes :: Property
prop_bounded_opaque_scopes = unit $ do
  program <- load source
  forM_
    [ ("once (even 10000 R)?", [Answer "R = done" []]),
      ("call (helper 10000 R)?", [Answer "R = done" []]),
      ("not (helper 10000 R, fail)?", [Answer "true." []]),
      ("(even 10000 R -> R = done ; R = fallback)?", [Answer "R = done" []]),
      ("findall (pair R Alias) (Alias = R, even 10000 R) List?", [Answer "List = [pair done done]" []]),
      ("Data = (box Leaf), once (helper 10000 R), Leaf = kept?", [Answer "Data = box kept, Leaf = kept, R = done" []]),
      ("findall R (call (even 10000 R)) List?", [Answer "List = [done]" []]),
      ("scoped 10000 Out?", [Answer "Out = pair before (box done)" []]),
      ("streamed 10000 Out?", [Answer "Out = pair before (box done)" []]),
      ("conditional 10000 Out?", [Answer "Out = pair before (box done)" []]),
      ("collected 10000 Out?", [Answer "Out = pair before [box done]" []]),
      ("minimize Cost (helper 10000 R, (Cost = 2 ; Cost = 1))?", [Answer "Cost = 1, R = done" []]),
      ("emit (render 10000)?", [Answer "true." [Reference.WriteEvent "ok"]])
    ] $ \(text, expected) -> do
      query <- queryText text
      (items, metrics) <- compareQuery program query
      observe query items === expected
      bounded metrics

prop_bounded_live_clp_roots :: Property
prop_bounded_live_clp_roots = unit $ do
  program <- load source
  forM_
    [ "X in 1..3, Y #= X + 1, even 10000 R, label [X, Y]?",
      "X in 1..3, Y #= X + 1, Alias = X, once (helper 10000 R), label [Alias, Y]?",
      "Data = (box X), X in 1..3, Y #= X + 1, (even 10000 R ; R = fallback), label [X, Y]?",
      "X in 1..3, Y #= X + 1, findall R (helper 10000 R) List, label [X, Y]?",
      "X in 1..3, Y #= X + 1, not (helper 10000 R, fail), label [X, Y]?"
    ] $ \text -> do
      query <- queryText text
      (_, metrics) <- compareQuery program query
      bounded metrics

prop_tables_dynamic_output_and_store_roots :: Property
prop_tables_dynamic_output_and_store_roots = unit $ do
  program <- load source
  forM_
    [ "cached Before, even 10000 R, cached After?",
      "assert (fact seed), helper 10000 R, fact Saved?",
      "assert (fact original), (assert (fact branch), even 10000 R, fail ; fact Saved)?",
      "write before, once (helper 10000 R), write after?",
      "cached Before, findall R (helper 10000 R) List, cached After?"
    ] $ \text -> do
      query <- queryText text
      (items, metrics) <- compareQuery program query
      bounded metrics
      let expected = [state | Reference.Found state <- Reference.solveQuery program query]
          actual = [state | Reference.Found state <- items]
      length actual === length expected
      forM_ (zip actual expected) $ \(found, original) -> do
        Reference.ssOutput found === Reference.ssOutput original
        Reference.ssOutLen found === Reference.ssOutLen original
        Reference.ssDynamic found === Reference.ssDynamic original
        show (Reference.ssTables found) === show (Reference.ssTables original)
        -- Logical metadata remains attached to original query IDs. Native
        -- substitutions may compress paths while retaining those semantics.
        (Reference.ssStore found) {stSubst = emptySubst} ===
          (Reference.ssStore original) {stSubst = emptySubst}

prop_declared_parent_contract_survives_collection :: Property
prop_declared_parent_contract_survives_collection = unit $ do
  program <- load $ source ++ unlines
    [ "typed : semidet (int: <=) (int: =>).",
      "typed N X <- even N R, X = bad."
    ]
  query <- queryText "typed 10000 X?"
  (items, metrics) <- compareQuery program query
  observe query items === [Error (show (SortError ("typed", 2) 2 SInt (Atom "bad")))]
  bounded metrics

prop_retained_choice_and_scope_checkpoints :: Property
prop_retained_choice_and_scope_checkpoints = unit $ do
  program <- load source
  forM_
    [ "(even 10000 R ; R = fallback)?",
      "call (even 10000 R), (X = first ; X = second)?",
      "findall R (even 10000 R) List, (X = first ; X = second)?",
      "X in 1..2, once (helper 10000 R), label [X]?"
    ] $ \text -> do
      query <- queryText text
      initial <- evalEither (Machine.startMeasured program query)
      first <- evalEither (Machine.resume initial)
      case first of
        Machine.Finished -> failure
        Machine.Yield retained next -> do
          let before = observe query [retained]
          _ <- evalIO (evaluate (length (show before)))
          assert (Machine.metricCollections (Machine.checkpointMetrics next) > 0)
          (remaining, _) <- evalEither (drain next)
          (repeated, _) <- evalEither (drain next)
          (restarted, final) <- evalEither (drain initial)
          observe query remaining === observe query repeated
          before === observe query [retained]
          before ++ observe query remaining === observe query restarted
          observe query restarted === observe query (Reference.solveQuery program query)
          bounded (Machine.checkpointMetrics final)

prop_unmeasured_general_tail_execution :: Property
prop_unmeasured_general_tail_execution = unit $ do
  program <- load source
  forM_ ["even 10000 R?", "(helper 10000 R ; R = fallback)?", "once (even 10000 R)?"] $ \text -> do
    query <- queryText text
    initial <- evalEither (Machine.start program query)
    (items, final) <- evalEither (drain initial)
    observe query items === observe query (Reference.solveQuery program query)
    let metrics = Machine.checkpointMetrics final
    Machine.metricCalls metrics === 0
    Machine.metricTailCalls metrics === 0
    Machine.metricCollections metrics === 0

machineGeneralTailGroup :: Group
machineGeneralTailGroup = Group "general native tail transfers and live checkpoints"
  [ ("generated mutual helper scoped and stateful parity", prop_generated_general_tail_parity),
    ("bounded mutual and prefix-helper tail frames", prop_bounded_mutual_and_helper_frames),
    ("bounded tail collection preserves live choices", prop_bounded_live_choice_rollback),
    ("bounded tail collection preserves opaque scope handles", prop_bounded_opaque_scopes),
    ("bounded tail collection preserves live CLP roots", prop_bounded_live_clp_roots),
    ("table dynamic output and store roots survive collection", prop_tables_dynamic_output_and_store_roots),
    ("declared parent contracts survive child collection", prop_declared_parent_contract_survives_collection),
    ("retained choice and scope checkpoints resume independently", prop_retained_choice_and_scope_checkpoints),
    ("unmeasured general tail paths remain independent", prop_unmeasured_general_tail_execution)
  ]

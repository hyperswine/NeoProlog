-- | Total recursion verdicts (docs/2026-11-16-TOTAL-RECURSION.md, step 0).
{-# LANGUAGE OverloadedStrings #-}
module TerminationTest (terminationGroup) where

import qualified Data.Map.Strict as Map
import Control.Monad (forM_)
import Hedgehog
import qualified Hedgehog.Gen as Gen
import qualified Hedgehog.Range as Range
import Infera.Diagnostic
import Infera.Syntax (parseLocatedFile)
import Infera.Engine.Reference (loadProgramText)
import Infera.Termination

unit :: PropertyT IO () -> Property
unit = withTests 1 . property

verdictOf :: String -> (String, Int) -> PropertyT IO Verdict
verdictOf source key = do
  annotate source
  program <- evalEither (loadProgramText source)
  evalMaybe (Map.lookup key (verdicts program))

conditions :: Verdict -> Maybe [[Int]]
conditions (Total proof) = Just (proofConditions proof)
conditions _ = Nothing

unproven :: Verdict -> Bool
unproven (Unproven _) = True
unproven _ = False

prop_structural :: Property
prop_structural = unit $ do
  v <- verdictOf "my_app [] L L.\nmy_app [X | Xs] L [X | R] <- my_app Xs L R." ("my_app", 3)
  conditions v === Just [[1], [3]]
  -- A built argument that is still a proper subterm of the head argument.
  w <- verdictOf "my_last [X] X.\nmy_last [_, Y | Ys] X <- my_last [Y | Ys] X." ("my_last", 2)
  conditions w === Just [[1]]
  -- Grammar recursion over input consumed by a terminal in the same rule.
  g <- verdictOf "ds -> [C], { C = 'a' }, ds.\nds -> []." ("ds", 2)
  conditions g === Just [[1]]

-- Shrinking one argument while growing another that a later call shrinks
-- back never ends; the old per-call rule accepted it.
prop_alternating_rejected :: Property
prop_alternating_rejected = unit $ do
  v <- verdictOf "p [X | Xs] Y <- p Xs [X | Y].\np X [Y | Ys] <- p [Y | X] Ys." ("p", 2)
  assert (unproven v)

prop_size_change :: Property
prop_size_change = unit $ do
  -- Each call shrinks one list and keeps the other.
  m <- verdictOf (unlines
    [ "mg [] Ys Ys.", "mg Xs [] Xs.",
      "mg [X | Xs] [Y | Ys] [X | Zs] <- X < Y, mg Xs [Y | Ys] Zs.",
      "mg [X | Xs] [Y | Ys] [Y | Zs] <- X >= Y, mg [X | Xs] Ys Zs." ]) ("mg", 3)
  conditions m === Just [[3], [1, 2]]
  -- Lexicographic descent.
  a <- verdictOf (unlines
    [ "ack zero N (s N).", "ack (s M) zero R <- ack M (s zero) R.",
      "ack (s M) (s N) R <- ack (s M) N R1, ack M R1 R." ]) ("ack", 3)
  conditions a === Just [[1, 2]]
  -- Neither individual list decreases across all calls; their sum does.
  summed <- verdictOf "p [a,b | Xs] Ys <- p Xs [c | Ys]. p Xs [a,b | Ys] <- p [c | Xs] Ys." ("p",2)
  conditions summed === Just [[1,2]]
  -- Mutual recursion, measured across the group.
  e <- verdictOf "ev zero.\nev (s N) <- od N.\nod (s N) <- ev N." ("ev", 1)
  conditions e === Just [[1]]

prop_unproven :: Property
prop_unproven = unit $ do
  -- A unification in one branch of a disjunction proves nothing.
  b <- verdictOf "q [].\nq L <- L != [], (L = [_ | T] ; T = L), q T." ("q", 1)
  assert (unproven b)
  -- Recursion through a verified element-passing closure.
  c <- verdictOf "walk (node Cs) <- maplist walk Cs." ("walk", 1)
  conditions c === Just [[1]]
  -- A goal built at run time could call anything.
  o <- verdictOf "r X <- univ G [r, X], call G." ("r", 1)
  assert (unproven o)
  d <- verdictOf "edge : dynamic.\nedge a b.\nreach X Y <- edge X Y.\nreach X Y <- edge X Z, reach Z Y." ("reach", 2)
  assert (unproven d)

prop_closures_and_io :: Property
prop_closures_and_io = unit $ do
  m <- verdictOf "mp _ [] [].\nmp F [X | Xs] [Y | Ys] <- call F X Y, mp F Xs Ys." ("mp", 3)
  case m of
    Total proof -> do
      proofConditions proof === [[2], [3]]
      assert (proofClosures proof)
    _ -> annotateShow m >> failure
  n <- verdictOf "plain X <- X = 1." ("plain", 1)
  n === NotRecursive
  r <- verdictOf "loop : io.\nloop -> read_line stdin R, ({ R = eof } -> [] ; loop)." ("loop", 2)
  r === Reactive

prop_integer_norms :: Property
prop_integer_norms = unit $ do
  forM_ [
      ("down 0. down N <- N > 0, M is N - 1, down M.", ("down",1), [[1]]),
      ("up I N <- I < N, J is I + 1, up J N.", ("up",2), [[1,2]]),
      ("dn H L <- H > L, J is H - 1, dn J L.", ("dn",2), [[1,2]]),
      ("a N <- N > 0, M is N - 1, b M. b N <- N > 0, M is N - 1, a M.", ("a",1), [[1]])
    ] $ \(source,key,expected) -> do
      v <- verdictOf source key
      case v of
        Total proof -> do
          proofConditions proof === expected
          proofIntegers proof === expected
        _ -> annotateShow v >> failure
  bad <- verdictOf "unbounded N <- M is N - 1, unbounded M." ("unbounded",1)
  assert (unproven bad)

-- The independent integer model reaches a floor in ceiling(N/step) calls.
-- Changing the decrement to zero must never acquire a proof.
prop_generated_counters :: Property
prop_generated_counters = withTests 30 . property $ do
  step <- forAll (Gen.int (Range.linear 1 20))
  start <- forAll (Gen.int (Range.linear 1 200))
  let chain = takeWhile (>0) (iterate (subtract step) start)
  length chain === (start + step - 1) `div` step
  v <- verdictOf ("count N <- N > 0, M is N - " ++ show step ++ ", count M.") ("count",1)
  conditions v === Just [[1]]
  case v of
    Total proof -> proofIntegers proof === [[1]] -- excludes float stagnation
    _ -> failure
  zero <- verdictOf "count N <- N > 0, M is N - 0, count M." ("count",1)
  assert (unproven zero)

prop_callee_relations :: Property
prop_callee_relations = unit $ do
  grammar <- verdictOf "scan -> token1, scan. scan -> []. token1 -> ['a']." ("scan",2)
  conditions grammar === Just [[1]]
  selection <- verdictOf "choose [] []. choose Xs [X | Ys] <- select X Xs Rest, choose Rest Ys." ("choose",2)
  assert (maybe False (elem [1]) (conditions selection))
  widened <- verdictOf "grow X [a | X]. p X <- grow X Y, p Y." ("p",1)
  assert (unproven widened)
  divergent <- verdictOf "bad : notable. bad <- bad. p [_ | T] <- bad, p T." ("p",1)
  assert (unproven divergent)
  -- A user definition must never inherit a library name's trusted summary.
  spoof <- verdictOf "select _ X [a | X]. p X <- select _ X Y, p Y." ("p",1)
  assert (unproven spoof)

prop_finite_tables :: Property
prop_finite_tables = unit $ do
  let source = "edge a b. edge b c. path X Y <- edge X Y. path X Y <- path X Z, edge Z Y."
  v <- verdictOf source ("path",2)
  v === TotalByTable
  untabled <- verdictOf ("path : notable. " ++ source) ("path",2)
  assert (unproven untabled)
  growing <- verdictOf "p a. p (s X) <- p X." ("p",1)
  -- Ground input is a valid structural mode; free generation is not.
  conditions growing === Just [[1]]
  fresh <- verdictOf "p X. p X <- p X." ("p",1)
  assert (unproven fresh)
  fd <- verdictOf "finite X <- X in 1..4, label [X]." ("finite",1)
  fd === NotRecursive
  unbounded <- verdictOf "open X <- label [X]." ("open",1)
  conditions unbounded === Just [[1]]
  bounded <- verdictOf "p X <- std_native_between 1 3 X. p X <- p X." ("p",1)
  bounded === TotalByTable

prop_diagnostics :: Property
prop_diagnostics = unit $ do
  items <- evalEither (parseLocatedFile "recursion.nprolog" "loop : notable. loop X <- loop X. wrapper X <- loop X.")
  let warnings = filter ((== "partial-recursion") . diagnosticCode) (diagnose items)
  length warnings === 2
  assert (all ((== Warning) . diagnosticSeverity) warnings)
  marked <- evalEither (parseLocatedFile "recursion.nprolog" "loop : unsafe notable. loop X <- loop X.")
  assert (null (filter ((== "partial-recursion") . diagnosticCode) (diagnose marked)))
  redundant <- evalEither (parseLocatedFile "recursion.nprolog" "p : unsafe. p a.")
  assert (any ((== "unnecessary-unsafe") . diagnosticCode) (diagnose redundant))
  modes <- evalEither (parseLocatedFile "recursion.nprolog"
    "app [] Y Y. app [X | Xs] Y [X | Zs] <- app Xs Y Zs. free <- app X Y Z. bound R <- app [a,b] [] R.")
  let hints=filter ((== "nonterminating-mode") . diagnosticCode) (diagnose modes)
  length hints === 1
  floats <- evalEither (parseLocatedFile "recursion.nprolog"
    "down 0. down N <- N > 0, M is N - 1, down M. > down 1000000000000000000000000000000.0?")
  let floatHints=filter ((== "nonterminating-mode") . diagnosticCode) (diagnose floats)
  length floatHints === 1
  -- Partiality alone is a warning, never a loading error for a pure caller.
  _ <- evalEither (loadProgramText "loop : unsafe. loop X <- loop X. caller X <- loop X.")
  pure ()

terminationGroup :: Group
terminationGroup = Group "Total recursion verdicts"
  [ ("structural descent, built subterms and grammars", prop_structural),
    ("alternating growth is rejected", prop_alternating_rejected),
    ("size-change: merges, lexicographic, mutual", prop_size_change),
    ("unproven: branches, closures, run-time goals, dynamic", prop_unproven),
    ("closure conditions, non-recursive and io verdicts", prop_closures_and_io),
    ("integer floors, upper bounds and mutual recursion", prop_integer_norms),
    ("generated positive counters and zero-step rejection", prop_generated_counters),
    ("verified grammar and selection summaries", prop_callee_relations),
    ("finite tables and finite-domain labeling", prop_finite_tables),
    ("partial warnings, unsafe and call-site modes", prop_diagnostics)
  ]

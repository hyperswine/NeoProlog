-- | Total recursion verdicts (docs/2026-11-16-TOTAL-RECURSION.md, step 0).
{-# LANGUAGE OverloadedStrings #-}
module TerminationTest (terminationGroup) where

import qualified Data.Map.Strict as Map
import Hedgehog
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
  -- Mutual recursion, measured across the group.
  e <- verdictOf "ev zero.\nev (s N) <- od N.\nod (s N) <- ev N." ("ev", 1)
  conditions e === Just [[1]]

prop_unproven :: Property
prop_unproven = unit $ do
  -- A unification in one branch of a disjunction proves nothing.
  b <- verdictOf "q [].\nq L <- L != [], (L = [_ | T] ; T = L), q T." ("q", 1)
  assert (unproven b)
  -- Recursion through a closure: maplist gives no size relation yet.
  c <- verdictOf "walk (node Cs) <- maplist walk Cs." ("walk", 1)
  assert (unproven c)
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

terminationGroup :: Group
terminationGroup = Group "Total recursion verdicts"
  [ ("structural descent, built subterms and grammars", prop_structural),
    ("alternating growth is rejected", prop_alternating_rejected),
    ("size-change: merges, lexicographic, mutual", prop_size_change),
    ("unproven: branches, closures, run-time goals, dynamic", prop_unproven),
    ("closure conditions, non-recursive and io verdicts", prop_closures_and_io)
  ]

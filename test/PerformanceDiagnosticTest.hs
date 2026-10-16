{-# LANGUAGE OverloadedStrings #-}

-- These oracles describe source patterns and calculate source positions
-- independently; they do not invoke the diagnostic helpers to predict hints.
module PerformanceDiagnosticTest (performanceDiagnosticGroup) where

import Control.Exception (bracket)
import Control.Monad (forM_)
import Data.Char (ord)
import Data.List (isPrefixOf)
import Hedgehog hiding (Var)
import qualified Hedgehog.Gen as Gen
import qualified Hedgehog.Range as Range
import Infera.Diagnostic
import qualified Infera.Engine as Engine
import Infera.Syntax
import Infera.Unify (canonicalize, emptySubst)
import System.Directory
  ( canonicalizePath, createDirectory, getTemporaryDirectory, removeFile,
    removePathForcibly, withCurrentDirectory )
import System.FilePath ((</>))
import System.IO (hClose, openTempFile)

unit :: PropertyT IO () -> Property
unit = withTests 1 . property

generated :: PropertyT IO () -> Property
generated = withTests 200 . property

located :: String -> PropertyT IO [LocatedTopLevel]
located source = annotate source >> evalEither (parseLocatedFile "buffer.nprolog" source)

performance :: String -> PropertyT IO [Diagnostic]
performance source = filter (isPrefixOf "perf-" . diagnosticCode) . diagnose <$> located source

codes :: String -> PropertyT IO [String]
codes source = map diagnosticCode <$> performance source

nonTailCode, unboundedCode, orderCode, indexCode :: String
nonTailCode = "perf-non-tail-recursion"
unboundedCode = "perf-unbounded-labeling"
orderCode = "perf-labeling-before-constraints"
indexCode = "perf-unselective-index"

prop_recursion_model :: Property
prop_recursion_model = generated $ do
  callerArity <- forAll (Gen.int (Range.linear 1 4))
  calleeArity <- forAll (Gen.int (Range.linear 1 4))
  sameName <- forAll Gen.bool
  context <- forAll (Gen.int (Range.linear 0 11))
  let args n = concat [" X" ++ show i | i <- [1 .. n]]
      call = (if sameName then "walk" else "other") ++ args calleeArity
      (body, hasContinuation) =
        [ (call, False), ("true, " ++ call, False), (call ++ ", true", True),
          ("(" ++ call ++ " ; true)", False),
          ("(true -> " ++ call ++ " ; true)", False),
          ("(" ++ call ++ " -> true ; true)", True),
          ("once (" ++ call ++ ")", True), ("not (" ++ call ++ ")", True),
          ("findall 1 (" ++ call ++ ") _", True),
          ("minimize 1 (" ++ call ++ ")", True),
          ("call (" ++ call ++ "), true", True),
          ("call (" ++ call ++ ")", False)
        ] !! context
      source = "walk" ++ args callerArity ++ " <- " ++ body ++ "."
      expected = sameName && callerArity == calleeArity && hasContinuation
  actual <- codes source
  actual === [nonTailCode | expected]

prop_recursion_contexts :: Property
prop_recursion_contexts = unit $ do
  forM_
    [ ("walk X <- (walk X, true ; true).", [nonTailCode]),
      ("walk X <- (true ; walk X).", []),
      ("walk X <- (true -> walk X ; walk X).", []),
      ("walk X <- forall true (walk X).", [nonTailCode]),
      ("walk X Y <- call walk X Y, true.", [nonTailCode]),
      ("walk X Y <- call walk X Y.", []),
      ("walk X <- other X. other X <- walk X.", []),
      ("grammar -> grammar.", []),
      ("grammar -> grammar, \"x\".", []),
      ("grammar -> (grammar ; \"x\").", [])
    ] $ \(source, expected) -> codes source >>= (=== expected)
prop_label_bounds_model :: Property
prop_label_bounds_model = generated $ do
  hasLower <- forAll Gen.bool
  hasUpper <- forAll Gen.bool
  alias <- forAll Gen.bool
  input <- forAll Gen.bool
  helper <- forAll Gen.bool
  let lower = if hasLower then "0" else "inf"
      upper = if hasUpper then "9" else "sup"
      domainVar = if alias then "Y" else "X"
      source = "prepare _.\nentry" ++ (if input then " X" else "") ++ " <- "
        ++ (if alias then "Y = X, " else "")
        ++ "Vs = [X], " ++ domainVar ++ " in " ++ lower ++ ".." ++ upper ++ ", "
        ++ (if helper then "prepare X, " else "") ++ "label Vs."
      expected = not input && not helper && not (hasLower && hasUpper)
  actual <- codes source
  actual === [unboundedCode | expected]

prop_label_false_positives :: Property
prop_label_false_positives = unit $ do
  forM_
    [ ("entry <- label [X].", [unboundedCode]),
      ("entry <- label [1, 2].", []),
      ("entry X <- label [X].", []),
      ("entry X <- X = [Y], label [Y].", []),
      ("prepare _. entry <- prepare X, label [X].", []),
      ("entry <- (true ; true), label [X].", []),
      ("entry <- X #>= 0, label [X].", []),
      ("entry <- X #= Y + 1, label [X].", []),
      ("entry <- X = 3 + 4, label [X].", []),
      ("entry <- X = 3, label [X].", []),
      ("entry <- X in 0..sup, Y in inf..9, X = Y, label [Y].", []),
      ("entry <- label [X | Tail].", []),
      ("entry <- labeling [] [X].", []),
      ("entry Options <- labeling Options [X].", []),
      ("entry <- labeling [min X] [X].", [unboundedCode]),
      ("entry <- Opts = [min X], labeling Opts [X].", [unboundedCode]),
      ("entry <- fail, label [X].", [])
    ] $ \(source, expected) -> codes source >>= (=== expected)

prop_label_constraint_order :: Property
prop_label_constraint_order = unit $ do
  forM_
    [ "X #= Y", "X #!= Y", "X #<= Y", "X #< Y", "X #>= Y", "X #> Y",
      "X != Y", "all_different [X, Y]", "all_distinct [X, Y]",
      "reify (X #= Y) B", "X in 0..2"
    ] $ \constraint -> do
      before <- codes ("entry <- [X, Y] in 0..4, " ++ constraint ++ ", label [X].")
      before === []
      after <- codes ("entry <- [X, Y] in 0..4, label [X], " ++ constraint ++ ".")
      after === [orderCode]
  forM_
    [ ("entry <- X in 0..4, label [X], Y #= 2.", []),
      ("entry <- label [1], X #= 2.", []),
      ("entry <- label [X], X in 0..4.", [orderCode, unboundedCode]),
      ("entry <- Y = X, Vs = [Y], X in 0..4, label Vs, Y #= 2.", [orderCode]),
      ("prepare _. entry <- X in 0..4, prepare X, label [X], X #= 2.", [orderCode])
    ] $ \(source, expected) -> codes source >>= (=== expected)
  -- Moving a filter inside optimization changes its feasible set. The hint
  -- must ask the author to check their intended answers, not promise that
  -- arbitrary constraint reordering is a semantics-preserving rewrite.
  let late = "X in 1..3, labeling [min X] [X], X #>= 2"
      early = "X in 1..3, X #>= 2, labeling [min X] [X]"
  codes ("entry X <- " ++ late ++ ".") >>= (=== [orderCode])
  program <- evalEither (Engine.loadProgramText "")
  lateQuery <- evalEither (parseQuery (late ++ "?"))
  earlyQuery <- evalEither (parseQuery (early ++ "?"))
  let answers query =
        [Engine.showAnswer (Engine.projectAnswer query state) | Engine.Found state <- Engine.solveQuery program query]
  answers lateQuery === []
  answers earlyQuery === ["X = 2"]

prop_index_model :: Property
prop_index_model = generated $ do
  arity <- forAll (Gen.int (Range.linear 0 4))
  count <- forAll (Gen.int (Range.linear 1 6))
  shapes <- forAll (Gen.list (Range.singleton arity) (Gen.int (Range.linear 0 4)))
  flag <- forAll (Gen.element ["", "noindex", "dynamic", "index"])
  let arg row column shape = case shape of
        0 -> "X" ++ show column
        1 -> "same"
        2 -> if even row then "red" else "blue"
        3 -> if even row then "same" else "X" ++ show column
        _ -> "(tag " ++ (if even row then "red" else "blue") ++ ")"
      clause row = "dispatch" ++ concat [" " ++ arg row column shape | (column, shape) <- zip [0 :: Int ..] shapes] ++ "."
      source = (if null flag then "" else "dispatch : " ++ flag ++ ".\n")
        ++ unlines [clause row | row <- [0 .. count - 1]]
      expected = arity > 0 && count > 1 && flag `notElem` ["noindex", "dynamic"]
        && all (`elem` [0, 1, 4]) shapes
  actual <- codes source
  actual === [indexCode | expected]

-- A position is measured from the literal source prefix, treating a tab as
-- one LSP character and a supplementary Unicode code point as two.
position :: String -> (Int, Int)
position prefix =
  (1 + length (filter (== '\n') prefix),
   1 + sum [if ord c > 0xffff then 2 else 1 | c <- takeWhile (/= '\n') (reverse prefix)])

identifierSpan :: FilePath -> String -> String -> SourceSpan
identifierSpan file prefix identifier =
  let (line, column) = position prefix
      (endLine, endColumn) = position (prefix ++ identifier)
   in SourceSpan file line column endLine endColumn

prop_identifier_positions :: Property
prop_identifier_positions = generated $ do
  name <- forAll (Gen.element ["spin", "recur", "δρόμος"])
  newline <- forAll (Gen.element ["\n", "\r\n"])
  indent <- forAll (Gen.string (Range.linear 0 8) (Gen.element (" \t" :: String)))
  comments <- forAll (Gen.list (Range.linear 0 5) (Gen.string (Range.linear 0 12) (Gen.element ("abcλ😀\t" :: String))))
  let prefix = concatMap (\comment -> "# " ++ name ++ " " ++ comment ++ newline) comments ++ indent
      headText = name ++ " X <- X = \"😀\", "
      source = prefix ++ headText ++ name ++ " X, true."
      expected = identifierSpan "buffer.nprolog" (prefix ++ headText) name
  items <- located source
  ds <- performance source
  map diagnosticCode ds === [nonTailCode]
  map diagnosticSpan ds === [expected]
  map diagnosticSeverity ds === [Information]
  map locatedHeadSpan items === [Just (identifierSpan "buffer.nprolog" prefix name)]
  assert ("\"severity\":\"information\"" `contains` diagnosticsJSON ds)
  where contains needle haystack = any (needle `isPrefixOf`) (tails haystack)
        tails [] = [[]]
        tails text@(_ : rest) = text : tails rest

prop_ambiguous_identical_sites :: Property
prop_ambiguous_identical_sites = unit $ do
  let source = "# spin X is only a comment\r\n\tspin X <- spin X, spin X."
  items <- located source
  ds <- performance source
  map diagnosticCode ds === [nonTailCode]
  map diagnosticSpan ds === map locatedSpan items
  -- A head and one equal body term remain distinct roles: the head must not
  -- make a unique recursive call look ambiguous.
  unique <- performance "spin X <- spin X, true."
  map diagnosticSpan unique === [identifierSpan "buffer.nprolog" "spin X <- " "spin"]

sourceAt :: String -> SourceSpan -> Maybe String
sourceAt source span' = do
  start <- lookup (spanLine span', spanColumn span') offsets
  end <- lookup (spanEndLine span', spanEndColumn span') offsets
  pure (take (end - start) (drop start source))
  where offsets = [(position (take i source), i) | i <- [0 .. length source]]

prop_located_parser_equivalence :: Property
prop_located_parser_equivalence = generated $ do
  name <- forAll (Gen.element ["entry", "reader", "λreader"])
  kind <- forAll (Gen.int (Range.linear 0 5))
  newline <- forAll (Gen.element ["\n", "\r\n"])
  comment <- forAll (Gen.string (Range.linear 0 24) (Gen.element (" abcλ😀\t" :: String)))
  let source = "# " ++ comment ++ newline ++ case kind of
        0 -> name ++ " X <- X = \"😀\", call (target X), true."
        1 -> name ++ " X <- (target X -> once (target X) ; not (target X))."
        2 -> name ++ " X <- findall X (target X) Result, Result = [X]."
        3 -> name ++ " X -> \"😀\", {target X}, target X."
        4 -> "> target \"😀\", once (other 1)."
        _ -> name ++ " : notable.\n" ++ name ++ " (tag red)."
  items <- located source
  parsed <- evalEither (parseFile source)
  map locatedItem items === parsed
  forM_ items $ \item -> do
    forM_ (locatedGoalSpans item) $ \(term, span') -> case functorOf term of
      Nothing -> annotateShow term >> failure
      Just (identifier, _) -> do
        spanFile span' === "buffer.nprolog"
        text <- evalMaybe (sourceAt source span')
        if text == identifier
          then pure () -- Named sites retain their exact identifier token.
          else do
            -- Operator expressions retain a full source range. Reparsing
            -- that range must preserve structure and aliasing even when its
            -- variables had different IDs in the containing clause.
            case term of
              Compound operator [_, _] -> assert (operator `elem`
                [ "^", "mul", "div", "mod", "plus", "minus", "range", "access",
                  "fd_ge", "fd_le", "fd_gt", "fd_lt", "gte", "lte", "gt", "lt",
                  "int_eq", "fd_ne", "equiv", "neq", "unify", "is", "in"
                ])
              _ -> annotateShow term >> failure
            reparsed <- evalEither (parseTerm text)
            fst (canonicalize emptySubst reparsed) === fst (canonicalize emptySubst term)
        assert ((spanLine span', spanColumn span') >= (spanLine (locatedSpan item), spanColumn (locatedSpan item)))
        assert ((spanEndLine span', spanEndColumn span') <= (spanEndLine (locatedSpan item), spanEndColumn (locatedSpan item)))
    forM_ (locatedHeadSpan item) $ \span' -> sourceAt source span' === Just name

withTemporaryDirectory :: (FilePath -> IO a) -> IO a
withTemporaryDirectory = bracket create removePathForcibly
  where
    create = do
      temporary <- getTemporaryDirectory
      (path, handle) <- openTempFile temporary "infera-performance-diagnostics"
      hClose handle
      removeFile path
      createDirectory path
      canonicalizePath path

prop_unsaved_import_locations :: Property
prop_unsaved_import_locations = unit $ do
  (ds, dependency, diskContents) <- evalIO $ withTemporaryDirectory $ \directory ->
    withCurrentDirectory directory $ do
      let root = directory </> "main.nprolog"
          dependency = directory </> "library.nprolog"
          saved = "loop X <- true."
          unsaved = "# 😀\r\n\tloop X <- X = \"😀\", loop X, true."
      writeFile root "entry."
      writeFile dependency saved
      writeFile "infera.conf" ("library#test " ++ dependency ++ "\n")
      ds <- checkSource root "<- import \"library#test\".\nentry <- library:loop 1." [(dependency, unsaved)]
      disk <- readFile dependency
      length disk `seq` pure (filter (isPrefixOf "perf-" . diagnosticCode) ds, dependency, disk)
  map diagnosticCode ds === [nonTailCode]
  map diagnosticSpan ds === [identifierSpan dependency "# 😀\r\n\tloop X <- X = \"😀\", " "loop"]
  diskContents === "loop X <- true."

performanceDiagnosticGroup :: Group
performanceDiagnosticGroup = Group "Actionable performance diagnostics"
  [ ("direct recursion context and arity model", prop_recursion_model),
    ("control contexts and DCG conservatism", prop_recursion_contexts),
    ("finite label bounds and alias model", prop_label_bounds_model),
    ("labeling avoids uncertain and invalid cases", prop_label_false_positives),
    ("constraint posting precedes enumeration", prop_label_constraint_order),
    ("all argument index keys independent model", prop_index_model),
    ("exact identifier UTF-16 positions", prop_identifier_positions),
    ("ambiguous equal sites preserve item fallback", prop_ambiguous_identical_sites),
    ("located parser preserves AST and actual identifiers", prop_located_parser_equivalence),
    ("unsaved imported hints retain original qualified locations", prop_unsaved_import_locations)
  ]

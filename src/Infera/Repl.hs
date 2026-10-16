{-# OPTIONS_GHC -Wno-name-shadowing #-}

-- | The interactive read-eval-print loop.
module Infera.Repl
  ( runRepl,
    runTraceFile,
    describePred,
    showSignature,
  )
where

import Control.Monad.IO.Class (liftIO)
import Data.IORef
import qualified Data.IntMap.Strict as IM
import Data.List (dropWhileEnd, isPrefixOf, nub)
import Data.Text (unpack)
import Infera.Engine
import Infera.Error
import Infera.Infer (inferProgram)
import qualified Infera.Machine.Trace as Trace
import Infera.Purity (describeViolation, programViolations)
import Infera.Module
import Infera.Program
import Infera.Syntax
import Prettyprinter
import Prettyprinter.Render.Terminal
import System.Console.Haskeline
import System.Environment (getArgs, lookupEnv)
import System.Exit (exitFailure)
import System.IO (hIsTerminalDevice, hPutStrLn, stderr, stdout)
import System.IO.Unsafe (unsafePerformIO)

-- | Colour output only when stdout is a terminal and NO_COLOR is unset.
useColour :: Bool
useColour = unsafePerformIO $ do
  tty <- hIsTerminalDevice stdout
  noColor <- lookupEnv "NO_COLOR"
  return (tty && maybe True null noColor)
{-# NOINLINE useColour #-}

renderDoc :: Doc AnsiStyle -> String
renderDoc doc
  | useColour = unpack (renderStrict (layoutPretty defaultLayoutOptions doc))
  | otherwise = unpack (renderStrict (layoutPretty defaultLayoutOptions (unAnnotate doc)))

docErr :: String -> Doc AnsiStyle
docErr msg = annotate (bold <> color Red) (pretty "Error: ") <> annotate (color Red) (pretty msg)

docInfo :: String -> Doc AnsiStyle
docInfo = annotate (colorDull Cyan) . pretty

docAnswer :: Answer -> Doc AnsiStyle
docAnswer answer
  | null pieces = annotate (bold <> color Green) (pretty "true.")
  | otherwise = hsep (punctuate comma pieces)
  where
    nameOf v = IM.findWithDefault (showVarDefault v) v (answerNames answer)
    bindingDocs =
      [ annotate (color Yellow) (pretty v)
          <+> annotate (colorDull White) (pretty "=")
          <+> annotate (color Cyan) (pretty (showTermWith nameOf t))
      | (v, t) <- answerBindings answer
      ]
    residualDocs = [annotate (color Magenta) (pretty r) | r <- answerResiduals answer]
    pieces = bindingDocs ++ residualDocs

showSignature :: String -> Signature -> String
showSignature name sig =
  name
    ++ " : "
    ++ unwords (showDet (sigDet sig) : map showArgSpec (sigArgs sig))
    ++ "."

-- | Human-readable description of a predicate's declarations, inferred
-- signature and effective flags.
describePred :: Program -> Pred -> [String]
describePred prog p =
  let (name, _) = predKey p
      declared = ["  declared: " ++ showSignature name s | s <- predDecls p]
      inf = predInferred p
      switch = case sigSwitch inf of
        [] -> ""
        ps -> "   # semidet when argument(s) " ++ unwords (map (show . (+ 1)) ps) ++ " ground"
      inferred = ["  inferred: " ++ showSignature name inf ++ switch]
      flags =
        "  clauses: "
          ++ show (IM.size (predClauses p))
          ++ ", tabled: "
          ++ yesNo (predIsTabled prog p)
          ++ ", indexed: "
          ++ yesNo (predIsIndexed prog p)
          ++ ", recursive: "
          ++ yesNo (predRecursive p)
          ++ ", pure: "
          ++ yesNo (predPure p)
   in (showPredKey (predKey p) : declared) ++ inferred ++ [flags]
  where
    yesNo True = "yes"
    yesNo False = "no"

predNames :: Program -> [String]
predNames prog = nub [fst (predKey p) | p <- programPreds prog]

replComplete :: IORef Program -> CompletionFunc IO
replComplete progRef input@(leftRev, _)
  | ":load " `isPrefixOf` left = completeFilename input
  | otherwise = completeWord Nothing " \t,(.?" completeIdent input
  where
    left = reverse leftRev
    completeIdent word = do
      prog <- readIORef progRef
      let names = nub (predNames prog ++ [":quit", ":q", ":load", ":reload", ":r", ":sig", ":preds", ":trace", ":help"])
      return [simpleCompletion n | n <- names, word `isPrefixOf` n]

runRepl :: IO ()
runRepl = do
  progRef <- newIORef emptyProgram
  fileRef <- newIORef (Nothing :: Maybe FilePath)
  let settings =
        (defaultSettings :: Settings IO)
          { complete = replComplete progRef,
            historyFile = Just ".infera_history"
          }
  runInputT settings $ do
    outputStrLn $
      renderDoc $
        annotate (bold <> color Cyan) (pretty "Infera v2")
          <> annotate (colorDull White) (pretty " — clauses: ")
          <> annotate (colorDull Yellow) (pretty "color red.")
          <+> annotate (colorDull White) (pretty "queries: ")
          <> annotate (colorDull Yellow) (pretty "color X?")
          <+> annotate (colorDull White) (pretty "declarations: ")
          <> annotate (colorDull Yellow) (pretty "color : semidet (atom: =>).")
    outputStrLn $
      renderDoc $
        annotate
          (colorDull White)
          (pretty "Commands: :load <file>   :reload (:r)   :sig [pred]   :preds   :trace <query>   :quit (:q)   Ctrl+D")
    args <- liftIO getArgs
    case args of
      (file : _) -> handleLine progRef fileRef (":load " ++ file)
      [] -> loop progRef fileRef
  where
    prompt = renderDoc (annotate (bold <> color Blue) (pretty "> "))

    loop progRef fileRef = do
      mline <- getInputLine prompt
      case mline of
        Nothing -> outputStrLn (renderDoc (annotate (colorDull Cyan) (pretty "Bye!")))
        Just line -> handleLine progRef fileRef (dropWhileEnd (== ' ') (dropWhile (== ' ') line))

    handleLine progRef fileRef trimmed
      | trimmed `elem` [":quit", ":q"] =
          outputStrLn (renderDoc (annotate (colorDull Cyan) (pretty "Bye!")))
      | trimmed `elem` [":reload", ":r"] = do
          mfile <- liftIO (readIORef fileRef)
          case mfile of
            Nothing -> outputStrLn (renderDoc (docErr "No file loaded yet. Use :load <file> first.")) >> loop progRef fileRef
            Just file -> loadAndReport progRef fileRef file "Reloaded"
      | ":load" `isPrefixOf` trimmed = do
          let raw = dropWhile (== ' ') (drop 5 trimmed)
              file = case raw of
                '"' : rest | not (null rest) && last rest == '"' -> init rest
                _ -> raw
          loadAndReport progRef fileRef file "Loaded"
      | ":preds" == trimmed = do
          prog <- liftIO (readIORef progRef)
          mapM_ (outputStrLn . showPredKey . predKey) (programPreds prog)
          loop progRef fileRef
      | ":sig" `isPrefixOf` trimmed = do
          prog <- liftIO (readIORef progRef)
          let name = dropWhile (== ' ') (drop 4 trimmed)
              selected = [p | p <- programPreds prog, null name || fst (predKey p) == name]
          if null selected
            then outputStrLn (renderDoc (docErr ("no such predicate: " ++ name)))
            else mapM_ (mapM_ (outputStrLn . renderDoc . docInfo) . describePred prog) selected
          loop progRef fileRef
      | ":help" == trimmed = do
          outputStrLn "Clauses end with '.', queries with '?'.  Declarations: name : det (sort: mode) ..."
          outputStrLn ":trace <query?> runs one query with Call/Exit/Redo/Fail/Cut/error events and source positions."
          loop progRef fileRef
      | ":trace " `isPrefixOf` trimmed = do
          case parseQuery (dropWhile (== ' ') (drop 7 trimmed)) of
            Left err -> outputStrLn (renderDoc (docErr err))
            Right query -> do
              prog0 <- liftIO (readIORef progRef)
              prog <- liftIO (preloadFiles prog0 (queryGoals query))
              items <- consumeTrace (outputStrLn . renderDoc . docInfo) (Trace.traceQuery prog query)
              renderQuerySummary (summarizeSearch query items)
          loop progRef fileRef
      | trimmed == ":trace" = do
          outputStrLn "Usage: :trace query?"
          loop progRef fileRef
      | not (null trimmed) && last trimmed == '?' = do
          case parseQuery trimmed of
            Left err -> outputStrLn (renderDoc (docErr err))
            Right q -> do
              prog0 <- liftIO (readIORef progRef)
              prog <- liftIO (preloadFiles prog0 (queryGoals q))
              renderQuerySummary (solveAll prog q)
          loop progRef fileRef
      | null trimmed = loop progRef fileRef
      | otherwise = do
          case parseClauseText trimmed of
            Left err -> outputStrLn (renderDoc (docErr err))
            Right items -> do
              prog <- liftIO (readIORef progRef)
              let located = either (const []) id (parseLocatedFile "<repl>" trimmed)
                  extended = foldl addItem prog items
                  prog' = inferProgram extended
                    {progSources = Trace.appendSourceMap (progSources extended) located}
              case programViolations prog' of
                ((key, g) : _) -> outputStrLn (renderDoc (docErr ("unsafe-call: " ++ describeViolation prog' key g)))
                [] -> do
                  prog'' <- liftIO (preloadFiles prog' (concat [clauseBody c | TLClause c <- items]))
                  liftIO (writeIORef progRef prog'')
                  outputStrLn (renderDoc (docInfo ("Added " ++ show (length items) ++ " item(s).")))
          loop progRef fileRef

    addItem prog (TLClause c) = addClause c prog
    addItem prog (TLDecl d) = addDecl d prog
    addItem prog _ = prog

    loadAndReport progRef fileRef file verb = do
      res <- liftIO (loadFile file)
      case res of
        Left err -> outputStrLn (renderDoc (docErr err))
        Right (prog, queries) -> do
          liftIO (writeIORef progRef prog)
          liftIO (writeIORef fileRef (Just file))
          let n = sum [IM.size (predClauses p) | p <- programPreds prog]
          outputStrLn (renderDoc (docInfo (verb ++ " " ++ show n ++ " clause(s) from " ++ show file ++ ".")))
          mapM_ (runInlineQuery prog) queries
      loop progRef fileRef

    runInlineQuery prog q = do
      let label =
            annotate (colorDull White) (pretty "> ")
              <> hsep (punctuate comma (map (pretty . showTermWith (queryVarName q)) (queryGoals q)))
      outputStrLn (renderDoc label)
      renderQuerySummary (solveAll prog q)

    queryVarName q v = maybe (showVarDefault v) id (lookup v [(vid, n) | (n, vid) <- queryNames q])

    renderQuerySummary summary = do
      let answers = summaryAnswers summary
          errors = summaryErrors summary
          exhausted = summaryExhausted summary
      case answers of
        [] -> case errors of
          err : _ -> outputStrLn (renderDoc (docErr (showSolveError err)))
          []
            | exhausted ->
                outputStrLn (renderDoc (annotate (bold <> color Yellow) (pretty "Search depth limit reached; the query was not proven false.")))
            | otherwise -> outputStrLn (renderDoc (annotate (bold <> color Red) (pretty "false.")))
        _ -> do
          mapM_ renderAnswer answers
          case errors of
            [] -> pure ()
            err : _ ->
              outputStrLn (renderDoc (annotate (color Yellow) (pretty ("Some branches raised an error: " ++ showSolveError err))))
          if exhausted
            then outputStrLn (renderDoc (annotate (color Yellow) (pretty "Search depth limit reached; more solutions may exist.")))
            else pure ()

    renderAnswer answer = do
      let output = concatMap renderOutputEvent (answerOutput answer)
      if null output then pure () else outputStr output
      outputStrLn (renderDoc (docAnswer answer))

-- | Trace a checked file's inline queries, or an explicit query. Events and
-- located errors go to stderr; ordinary answer/output text goes to stdout.
runTraceFile :: FilePath -> Maybe String -> IO ()
runTraceFile file queryText = do
  loaded <- loadFile file
  case loaded of
    Left err -> die err
    Right (program, inline) -> case traverse parseQuery queryText of
      Left err -> die err
      Right explicit -> do
        let queries = maybe inline (: []) explicit
        if null queries then die "No inline query. Usage: infera --trace FILE [\"query?\"]" else pure ()
        summaries <- mapM (run program) queries
        if any (\summary -> not (null (summaryErrors summary)) || summaryExhausted summary) summaries
          then exitFailure else pure ()
  where
    die err = hPutStrLn stderr ("Error: " ++ err) >> exitFailure
    run program query = do
      loaded <- preloadFiles program (queryGoals query)
      items <- consumeTrace (hPutStrLn stderr) (Trace.traceQuery loaded query)
      let summary = summarizeSearch query items
      mapM_ answer (summaryAnswers summary)
      case summaryErrors summary of
        err : _ -> hPutStrLn stderr ("Error: " ++ showSolveError err)
        [] | null (summaryAnswers summary) && not (summaryExhausted summary) -> putStrLn "false."
        [] -> pure ()
      if summaryExhausted summary then hPutStrLn stderr "Search depth limit reached; the query is incomplete." else pure ()
      pure summary
    answer value = do
      putStr (concatMap renderOutputEvent (answerOutput value))
      putStrLn (showAnswer value)

-- Consume the event stream as it is generated, retaining only the ordinary
-- result stream required by the existing query summary renderer.
consumeTrace :: Monad m => (String -> m ()) -> [Trace.TraceItem] -> m Search
consumeTrace display = go []
  where
    go results [] = pure (reverse results)
    go results (Trace.TraceEventItem event : rest) = display (Trace.renderTraceEvent event) >> go results rest
    go results (Trace.TraceSearchItem item : rest) = go (item : results) rest

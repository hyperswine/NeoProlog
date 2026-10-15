-- | The module system: registration in @neoprolog.conf@, @<- import "mod#hash".@
-- directives, and qualification of imported predicates as @mod:name@.
module Infera.Module
  ( ModuleConf,
    findConf,
    loadConf,
    registerModule,
    parseModRef,
    processTopLevels,
    loadSource,
    loadFile,
    loadLocatedFile,
    loadLocatedWithSources,
    buildChecked,
    preloadFiles,
    fileGoals,
  )
where

import qualified Control.Exception as CE
import Control.Monad (foldM)
import qualified Crypto.Hash.SHA1 as SHA1
import qualified Data.ByteString as BS
import qualified Data.ByteString.Char8 as BSC
import Data.List (nub)
import qualified Data.IntMap.Strict as IM
import Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map
import Infera.Infer (inferProgram)
import Infera.Purity (describeViolation, programViolations)
import Infera.Program
import Infera.Syntax
import Numeric (showHex)
import System.Directory (canonicalizePath, doesFileExist, getHomeDirectory)
import System.FilePath (takeBaseName, (</>))

sha1Hex :: String -> String
sha1Hex s = concatMap byte2hex (BS.unpack (SHA1.hash (BSC.pack s)))
  where
    byte2hex b =
      let h = showHex b ""
       in if length h == 1 then '0' : h else h

type ModuleConf = Map String FilePath

confNames :: [FilePath]
confNames = ["neoprolog.conf", "infera.conf"]

findConf :: IO (Maybe FilePath)
findConf = do
  local <- firstExisting confNames
  case local of
    Just p -> return (Just p)
    Nothing -> do
      home <- getHomeDirectory
      firstExisting [home </> "nprolog" </> n | n <- confNames]
  where
    firstExisting [] = return Nothing
    firstExisting (p : ps) = do
      e <- doesFileExist p
      if e then return (Just p) else firstExisting ps

loadConf :: IO ModuleConf
loadConf = do
  mpath <- findConf
  case mpath of
    Nothing -> return Map.empty
    Just path -> do
      contents <- readFile path
      let rows = map words (filter (\l -> take 1 l /= "" && take 1 l /= "#") (lines contents))
      return (Map.fromList [(key, fp) | [key, fp] <- rows])

registerModule :: FilePath -> IO ()
registerModule path = do
  absPath <- canonicalizePath path
  let modName = takeBaseName absPath
      hash = sha1Hex absPath
      key = modName ++ "#" ++ hash
  appendFile "neoprolog.conf" (key ++ " " ++ absPath ++ "\n")
  putStrLn ("Registered " ++ key ++ " -> " ++ absPath)

parseModRef :: String -> Maybe (String, String)
parseModRef s = case break (== '#') s of
  (modName, '#' : hash) | not (null modName), not (null hash) -> Just (modName, hash)
  _ -> Nothing

-- ─── QUALIFICATION ───────────────────────────────────────────────────────────

definedNames :: [TopLevel] -> [String]
definedNames items =
  nub $
    [f | TLClause c <- items, Just (f, _) <- [clauseKey c]]
      ++ [declName d | TLDecl d <- items]

qualifyTerm :: String -> [String] -> Term -> Term
qualifyTerm m known t = case t of
  Atom f | f `elem` known -> Atom (m ++ ":" ++ f)
  Compound f as
    | f `elem` known -> Compound (m ++ ":" ++ f) (map (qualifyTerm m known) as)
    | otherwise -> Compound f (map (qualifyTerm m known) as)
  _ -> t

qualifyItem :: String -> [String] -> TopLevel -> TopLevel
qualifyItem m known item = case item of
  TLClause (Clause h b n) -> TLClause (Clause (qualifyTerm m known h) (map (qualifyTerm m known) b) n)
  TLDecl d
    | declName d `elem` known -> TLDecl d {declName = m ++ ":" ++ declName d}
    | otherwise -> TLDecl d
  other -> other

-- ─── IMPORTS ─────────────────────────────────────────────────────────────────

processImport :: ModuleConf -> [String] -> String -> IO (Either String [TopLevel])
processImport conf visited modRef = case parseModRef modRef of
  Nothing -> return (Left ("Invalid module reference: " ++ modRef))
  Just (modName, _) -> case Map.lookup modRef conf of
    Nothing -> return (Left ("Module '" ++ modRef ++ "' not found in neoprolog.conf"))
    Just fp
      | modRef `elem` visited -> return (Right [])
      | otherwise -> do
          result <- CE.try (readFile fp) :: IO (Either CE.SomeException String)
          case result of
            Left ex -> return (Left (show ex))
            Right contents -> case parseFile contents of
              Left err -> return (Left err)
              Right items -> do
                nested <- expandImports conf (modRef : visited) items
                case nested of
                  Left err -> return (Left err)
                  Right (own, _) ->
                    let known = definedNames own
                     in return (Right (map (qualifyItem modName known) own))

-- Expand imports; returns (program items, inline queries).
expandImports :: ModuleConf -> [String] -> [TopLevel] -> IO (Either String ([TopLevel], [Query]))
expandImports conf visited = foldM step (Right ([], []))
  where
    step (Left e) _ = return (Left e)
    step (Right (items, qs)) item = case item of
      TLQuery q -> return (Right (items, qs ++ [q]))
      TLDirective [Compound "import" [StrLit ref]] -> do
        res <- processImport conf visited ref
        case res of
          Left e -> return (Left e)
          Right imported -> return (Right (items ++ imported, qs))
      TLDirective goals
        | Just _ <- addDirective goals emptyProgram -> return (Right (items ++ [item], qs))
        | otherwise -> return (Left ("Unknown directive: " ++ show goals))
      _ -> return (Right (items ++ [item], qs))

-- | Resolve imports and directives in a parsed file.
processTopLevels :: ModuleConf -> [TopLevel] -> IO (Either String ([TopLevel], [Query]))
processTopLevels conf = expandImports conf []

-- | Build and analyse a program, refusing it when a predicate performs
-- effects without an @unsafe@ declaration.
buildChecked :: [TopLevel] -> Either String Program
buildChecked items =
  let prog = inferProgram (buildProgram items)
   in case programViolations prog of
        [] -> Right prog
        ((key, g) : _) -> Left ("unsafe-call: " ++ describeViolation prog key g)

-- | Literal file paths named by read_file / phrase_from_file goals.
fileGoals :: [Term] -> [String]
fileGoals = nub . concatMap go
  where
    go t = case t of
      Compound "read_file" [StrLit p, _] -> [p]
      Compound "phrase_from_file" [_, StrLit p] -> [p]
      Compound _ as -> concatMap go as
      _ -> []

-- | Read the files a program and its queries refer to, so the pure engine can
-- serve them.  Missing files are reported when the goal runs, not here.
preloadFiles :: Program -> [Term] -> IO Program
preloadFiles prog goals = do
  let wanted = [p | p <- fileGoals goals, not (Map.member p (progFiles prog))]
  loaded <- mapM readOne wanted
  return (addFiles [(p, c) | (p, Just c) <- zip wanted loaded] prog)
  where
    readOne p = do
      r <- CE.try (readFile p >>= \c -> length c `seq` return c) :: IO (Either CE.IOException String)
      return (either (const Nothing) Just r)

programGoals :: Program -> [Term]
programGoals prog = concat [clauseBody cl | p <- programPreds prog, cl <- IM.elems (predClauses p)]

-- | Load program source text (with imports) into an inferred program.
loadSource :: ModuleConf -> String -> IO (Either String (Program, [Query]))
loadSource conf src = case parseFile src of
  Left err -> return (Left err)
  Right items -> do
    res <- processTopLevels conf items
    case res of
      Left err -> return (Left err)
      Right (progItems, qs) -> case buildChecked progItems of
        Left err -> return (Left err)
        Right prog -> do
          prog' <- preloadFiles prog (programGoals prog ++ concatMap queryGoals qs)
          return (Right (prog', qs))

loadFile :: FilePath -> IO (Either String (Program, [Query]))
loadFile path = do
  result <- CE.try (readFile path) :: IO (Either CE.SomeException String)
  case result of
    Left ex -> return (Left (show ex))
    Right contents -> do
      conf <- loadConf
      loadSource conf contents

-- | Resolve imports while retaining the owning file and item range. Import
-- queries are ignored, just as they are by 'loadSource'.
loadLocatedFile :: FilePath -> IO (Either (SourceSpan, String) [LocatedTopLevel])
loadLocatedFile = loadLocatedWithSources []

-- | Source overrides use the original file's identity and import context.
-- This lets editors check unsaved roots and dependencies without replacing
-- their files on disk. Paths are canonicalised before lookup.
loadLocatedWithSources :: [(FilePath, String)] -> FilePath -> IO (Either (SourceSpan, String) [LocatedTopLevel])
loadLocatedWithSources sources path = do
  result <- CE.try $ do
    conf <- loadConf
    overrides <- Map.fromList <$> mapM (\(file, src) -> do
      absolute <- canonicalizePath file
      pure (absolute, src)) sources
    absolute <- canonicalizePath path
    expand overrides conf [] absolute
  pure $ case result of
    Left ex -> Left (SourceSpan path 1 1 1 2, show (ex :: CE.IOException))
    Right value -> value
  where
    expand overrides conf visited file = do
      input <- case Map.lookup file overrides of
        Just src -> pure (Right src)
        Nothing -> CE.try (readFile file >>= \s -> length s `seq` pure s)
      case input of
        Left ex -> pure (Left (SourceSpan file 1 1 1 2, show (ex :: CE.IOException)))
        Right src -> case parseLocatedFile file src of
          Left err -> pure (Left err)
          Right items -> foldM (step overrides conf visited) (Right []) items
    step _ _ _ (Left err) _ = pure (Left err)
    step overrides conf visited (Right acc) item = case locatedItem item of
      TLDirective [Compound "import" [StrLit ref]] ->
        case parseModRef ref of
          Nothing -> pure (Left (locatedSpan item, "Invalid module reference: " ++ ref))
          Just (name, _) -> case Map.lookup ref conf of
            Nothing -> pure (Left (locatedSpan item, "Module '" ++ ref ++ "' not found in neoprolog.conf"))
            Just file
              | ref `elem` visited -> pure (Right acc)
              | otherwise -> do
                  absolute <- canonicalizePath file
                  nested <- expand overrides conf (ref : visited) absolute
                  pure $ do
                    imported <- nested
                    let own = [i | i <- imported, case locatedItem i of TLQuery _ -> False; _ -> True]
                        known = definedNames (map locatedItem own)
                    pure (acc ++ [i {locatedItem = qualifyItem name known (locatedItem i)} | i <- own])
      TLDirective goals
        | Nothing <- addDirective goals emptyProgram ->
            pure (Left (locatedSpan item, "Unknown directive: " ++ show goals))
      _ -> pure (Right (acc ++ [item]))

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
  )
where

import qualified Control.Exception as CE
import Control.Monad (foldM)
import qualified Crypto.Hash.SHA1 as SHA1
import qualified Data.ByteString as BS
import qualified Data.ByteString.Char8 as BSC
import Data.List (nub)
import Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map
import Infera.Infer (inferProgram)
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

-- | Load program source text (with imports) into an inferred program.
loadSource :: ModuleConf -> String -> IO (Either String (Program, [Query]))
loadSource conf src = case parseFile src of
  Left err -> return (Left err)
  Right items -> do
    res <- processTopLevels conf items
    case res of
      Left err -> return (Left err)
      Right (progItems, qs) -> return (Right (inferProgram (buildProgram progItems), qs))

loadFile :: FilePath -> IO (Either String (Program, [Query]))
loadFile path = do
  result <- CE.try (readFile path) :: IO (Either CE.SomeException String)
  case result of
    Left ex -> return (Left (show ex))
    Right contents -> do
      conf <- loadConf
      loadSource conf contents

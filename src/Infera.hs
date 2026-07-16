{-# OPTIONS_GHC -Wno-missing-export-lists #-}
{-# OPTIONS_GHC -Wno-name-shadowing #-}
{-# OPTIONS_GHC -Wno-type-defaults #-}
{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}
{-# OPTIONS_GHC -Wno-unused-do-bind #-}

{-# HLINT ignore "Replace case with fromMaybe" #-}

module Infera where

import qualified Control.Exception as CE
import Control.Monad (foldM, void)
import Control.Monad.Combinators.Expr
import Control.Monad.IO.Class (liftIO)
import qualified Crypto.Hash.SHA1 as SHA1
import qualified Data.ByteString as BS
import qualified Data.ByteString.Char8 as BSC
import Data.IORef (modifyIORef, newIORef, readIORef, writeIORef, IORef)
import Data.List (dropWhileEnd, intercalate, isPrefixOf, nub)
import Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map
import Data.Maybe (fromMaybe)
import Data.Text (unpack)
import Data.Void
import Numeric (showHex)
import Prettyprinter
import Prettyprinter.Render.Terminal
import System.Console.Haskeline
import System.Directory (canonicalizePath, doesFileExist, getHomeDirectory)
import System.Environment (getArgs)
import System.FilePath (takeBaseName, (</>))
import Text.Megaparsec
import Text.Megaparsec.Char
import qualified Text.Megaparsec.Char.Lexer as L

-- ─── SURFACE SYNTAX ──────────────────────────────────────────────────────────

data Term
  = Atom String
  | Var String
  | IntLit Integer
  | FloatLit Double
  | CharLit Char
  | StrLit String
  | Compound String [Term]
  | TList [Term] (Maybe Term)
  deriving (Ord, Eq)

data Clause = Clause
  { clauseHead :: Term,
    clauseBody :: [Term]
  }
  deriving (Show, Eq)

data TopLevel
  = TLClause Clause
  | TLQuery [Term]
  | TLDirective [Term]
  deriving (Show, Eq)

type Program = [Clause]

-- Unfold a cons chain (produced by :: or expandList) into its elements and
-- optional tail.
unfoldCons :: Term -> ([Term], Maybe Term)
unfoldCons (Compound "cons" [h, t]) =
  let (xs, rest) = unfoldCons t
   in (h : xs, rest)
unfoldCons (Atom "nil") = ([], Nothing)
unfoldCons (TList xs Nothing) = (xs, Nothing)
unfoldCons (TList xs (Just r)) =
  let (ys, rest) = unfoldCons r
   in (xs ++ ys, rest)
unfoldCons t = ([], Just t)

instance Show Term where
  show (Atom s) = s
  show (Var s) = s
  show (IntLit n) = show n
  show (FloatLit d) = show d
  show (CharLit c) = ['\'', c, '\'']
  show (StrLit s) = show s
  show t@(Compound "cons" _) =
    let (xs, rest) = unfoldCons t
     in "["
          ++ intercalate ", " (map show xs)
          ++ maybe "" (\r -> " | " ++ show r) rest
          ++ "]"
  show (Compound f as) = f ++ " " ++ unwords (map showArg as)
    where
      showArg t@(Compound _ (_ : _)) = "(" ++ show t ++ ")"
      showArg t = show t
  show t@(TList _ _) =
    let (xs, rest) = unfoldCons t
     in "["
          ++ intercalate ", " (map show xs)
          ++ maybe "" (\r -> " | " ++ show r) rest
          ++ "]"

type Parser = Parsec Void String

-- ─── LEXING ──────────────────────────────────────────────────────────────────

-- Preserve the original # comment syntax while reserving #= as an operator.
hashLineComment :: Parser ()
hashLineComment = try $ do
  char '#'
  notFollowedBy (char '=')
  void $ manyTill anySingle (void eol <|> eof)

sc :: Parser ()
sc = L.space space1 hashLineComment empty

lexeme :: Parser a -> Parser a
lexeme = L.lexeme sc

symbol :: String -> Parser String
symbol = L.symbol sc

-- ─── PARSER ──────────────────────────────────────────────────────────────────

pAtomIdent :: Parser String
pAtomIdent = lexeme $ do
  c <- lowerChar <|> char '_'
  cs <- many $ alphaNumChar <|> char '_'

  let name = c : cs
  if name == "_"
    then fail "underscore is a variable"
    else do
      -- Optionally parse :qualifier for module-qualified names, but not ::.
      qual <- optional $ try $ do
        char ':'
        notFollowedBy $ char ':'
        c' <- lowerChar <|> char '_'
        cs' <- many $ alphaNumChar <|> char '_'
        return $ c' : cs'
      return $ case qual of
        Nothing -> name
        Just q -> name ++ ":" ++ q

pVarIdent :: Parser String
pVarIdent = lexeme $ do
  c <- upperChar
  cs <- many $ alphaNumChar <|> char '_'
  return $ c : cs

pAnon :: Parser String
pAnon = lexeme $ do
  char '_'
  notFollowedBy alphaNumChar
  return "_"

pNumber :: Parser Term
pNumber = lexeme $ do
  neg <- option False $ True <$ char '-'

  choice
    [ try $ do
        whole <- some digitChar
        char '.'
        frac <- some digitChar
        let d = read $ whole ++ "." ++ frac :: Double
        return $ FloatLit $ if neg then negate d else d,
      do
        digits <- some digitChar
        let n = read digits :: Integer
        return $ IntLit $ if neg then negate n else n
    ]

pCharLit :: Parser Term
pCharLit = lexeme $ do
  char '\''
  c <- L.charLiteral
  char '\''
  return $ CharLit c

pStrLit :: Parser Term
pStrLit = lexeme $ do
  char '"'
  cs <- manyTill L.charLiteral $ char '"'
  return $ StrLit cs

pList :: Parser Term
pList = do
  symbol "["
  choice
    [ symbol "]" >> return (TList [] Nothing),
      do
        first <- pExpr
        rest <- many $ symbol "," *> pExpr
        let elems = first : rest
        tail' <- optional $ symbol "|" *> pExpr
        symbol "]"
        return $ TList elems tail'
    ]

pAtomicTerm :: Parser Term
pAtomicTerm =
  choice
    [ try pNumber,
      pCharLit,
      pStrLit,
      pList,
      between (symbol "(") (symbol ")") pExpr,
      try pCompound,
      Var <$> (pAnon <|> pVarIdent),
      Atom <$> pAtomIdent
    ]

pCompound :: Parser Term
pCompound = do
  f <- pAtomIdent
  args <- some pArgTerm
  return $ Compound f args

pArgTerm :: Parser Term
pArgTerm =
  choice
    [ try pNumber,
      pCharLit,
      pStrLit,
      pList,
      between (symbol "(") (symbol ")") pExpr,
      Var <$> (pAnon <|> pVarIdent),
      Atom <$> pAtomIdent
    ]

pExpr :: Parser Term
pExpr = makeExprParser pAtomicTerm operatorTable

operatorTable :: [[Operator Parser Term]]
operatorTable =
  [ [InfixL $ binOp "^" <$ try (symbol "^")],
    [ InfixL $ binOp "mul" <$ try (symbol "*"),
      InfixL $ binOp "div" <$ try (symbol "/"),
      InfixL $ binOp "mod" <$ try (symbol "%")
    ],
    [ InfixL $ binOp "plus" <$ try (symbol "+"),
      InfixL $ binOp "minus" <$ try (symbol "-" <* notFollowedBy (char '>'))
    ],
    [InfixR $ binOp "cons" <$ try (symbol "::")],
    [InfixN $ binOp "access" <$ try (char '.' *> lookAhead (letterChar <|> char '_'))],
    [ InfixN $ binOp "gte" <$ try (symbol ">="),
      InfixN $ binOp "lte" <$ try (symbol "<="),
      InfixN $ binOp "gt" <$ try (symbol ">" <* notFollowedBy (char '=' <|> char '-')),
      InfixN $ binOp "lt" <$ try (symbol "<" <* notFollowedBy (char '=' <|> char '-'))
    ],
    [ InfixN $ binOp "int_eq" <$ try (symbol "#="),
      InfixN $ binOp "equiv" <$ try (symbol "=="),
      InfixN $ binOp "neq" <$ try (symbol "!="),
      InfixN $ binOp "unify" <$ try (symbol "=" <* notFollowedBy (char '=')),
      InfixN $ binOp "is" <$ try (string "is" <* notFollowedBy alphaNumChar <* sc)
    ]
  ]
  where
    binOp name l r = Compound name [l, r]

pGoal :: Parser Term
pGoal = pExpr

pGoals :: Parser [Term]
pGoals = pGoal `sepBy1` symbol ","

pClause :: Parser Clause
pClause = do
  hd <- pExpr
  choice
    [ do
        symbol "->"
        body <- pGoals
        symbol "."
        return $ desugarDCG hd body,
      do
        symbol "<-"
        body <- pGoals
        symbol "."
        return $ Clause hd body,
      do
        symbol "."
        return $ Clause hd []
    ]

desugarDCG :: Term -> [Term] -> Clause
desugarDCG hd body = Clause hd' body'
  where
    n = length body
    sVars = [Var $ "S" ++ show i | i <- [0 .. n]]

    addArgs t sa sb = case t of
      TList [] Nothing -> Compound "unify" [sa, sb]
      TList xs Nothing -> Compound "unify" [sa, TList xs (Just sb)]
      TList xs (Just r) -> Compound "unify" [sa, TList xs (Just r)]
      Atom f -> Compound f [sa, sb]
      Compound f args -> Compound f $ args ++ [sa, sb]
      _ -> Compound "call" [t, sa, sb]

    s0 = head sVars
    sN = last sVars

    hd' = case hd of
      Atom f -> Compound f [s0, sN]
      Compound f args -> Compound f $ args ++ [s0, sN]
      _ -> hd

    body' = zipWith3 addArgs body sVars (drop 1 sVars)

pProgram :: Parser Program
pProgram = sc *> many pClause <* eof

pInlineQuery :: Parser [Term]
pInlineQuery = do
  symbol ">"
  goals <- pGoals
  symbol "." <|> symbol "?"
  return goals

pTopLevel :: Parser TopLevel
pTopLevel =
  try (TLQuery <$> pInlineQuery)
    <|> try (TLDirective <$> pDirective)
    <|> (TLClause <$> pClause)

pDirective :: Parser [Term]
pDirective = do
  symbol "<-"
  goals <- pGoals
  symbol "."
  return goals

pFile :: Parser [TopLevel]
pFile = sc *> many pTopLevel <* eof

parseProgram :: String -> Either String Program
parseProgram input = case parse pProgram "<input>" input of
  Left err -> Left $ errorBundlePretty err
  Right p -> Right p

parseFile :: String -> Either String [TopLevel]
parseFile input = case parse pFile "<input>" input of
  Left err -> Left $ errorBundlePretty err
  Right items -> Right items

parseTerm :: String -> Either String Term
parseTerm input = case parse (sc *> pExpr <* eof) "<input>" input of
  Left err -> Left $ errorBundlePretty err
  Right t -> Right t

parseGoals :: String -> Either String [Term]
parseGoals input = case parse (sc *> pGoals <* eof) "<input>" input of
  Left err -> Left $ errorBundlePretty err
  Right gs -> Right gs

-- ─── SUBSTITUTION AND UNIFICATION ────────────────────────────────────────────

type Subst = Map String Term

type FreshCounter = Int

emptySubst :: Subst
emptySubst = Map.empty

walk :: Subst -> Term -> Term
walk s (Var v) = case Map.lookup v s of
  Just t -> walk s t
  Nothing -> Var v
walk _ t = t

deepWalk :: Subst -> Term -> Term
deepWalk s t = case walk s t of
  Var v -> Var v
  Atom a -> Atom a
  IntLit n -> IntLit n
  FloatLit d -> FloatLit d
  CharLit c -> CharLit c
  StrLit str -> StrLit str
  Compound f as -> Compound f $ map (deepWalk s) as
  TList xs rest -> TList (map (deepWalk s) xs) (fmap (deepWalk s) rest)

occurs :: Subst -> String -> Term -> Bool
occurs s v t = case walk s t of
  Var v' -> v == v'
  Compound _ as -> any (occurs s v) as
  TList xs rest -> any (occurs s v) xs || maybe False (occurs s v) rest
  _ -> False

expandList :: [Term] -> Maybe Term -> Term
expandList [] (Just t) = t
expandList [] Nothing = Atom "nil"
expandList (h : hs) r = Compound "cons" [h, expandList hs r]

unifySubst :: Subst -> Term -> Term -> Maybe Subst
unifySubst s t1 t2 = unify' s (walk s t1) (walk s t2)

unify' :: Subst -> Term -> Term -> Maybe Subst
unify' s (Var v) t | Var v == t = Just s
unify' s (Var v) t | occurs s v t = Nothing
unify' s (Var v) t = Just $ Map.insert v t s
unify' s t (Var v) | occurs s v t = Nothing
unify' s t (Var v) = Just $ Map.insert v t s
unify' s (Atom a) (Atom b) | a == b = Just s
unify' s (IntLit a) (IntLit b) | a == b = Just s
unify' s (FloatLit a) (FloatLit b) | a == b = Just s
unify' s (CharLit a) (CharLit b) | a == b = Just s
unify' s (StrLit a) (StrLit b) | a == b = Just s
unify' s (Compound "cons" [h, t]) u = unify' s (TList [h] (Just t)) u
unify' s u (Compound "cons" [h, t]) = unify' s u (TList [h] (Just t))
unify' s (Compound f1 as1) (Compound f2 as2)
  | f1 == f2 && length as1 == length as2 =
      foldM (\s' (a, b) -> unifySubst s' a b) s (zip as1 as2)
unify' s (Atom "nil") (TList [] Nothing) = Just s
unify' s (TList [] Nothing) (Atom "nil") = Just s
unify' s (TList [] Nothing) (TList [] Nothing) = Just s
unify' s (TList [] Nothing) (TList [] (Just t)) = unifySubst s t (TList [] Nothing)
unify' s (TList [] (Just r)) (TList [] Nothing) = unifySubst s r (TList [] Nothing)
unify' s (TList [] (Just r)) (TList [] (Just t)) = unifySubst s r t
unify' _ (TList [] Nothing) (TList (_ : _) _) = Nothing
unify' _ (TList (_ : _) _) (TList [] Nothing) = Nothing
unify' s (TList [] (Just r)) (TList ys s2) = unifySubst s r (TList ys s2)
unify' s (TList xs r) (TList [] (Just t)) = unifySubst s (TList xs r) t
unify' s (TList (x : xs) r) (TList (y : ys) s2) = do
  s' <- unifySubst s x y
  unifySubst s' (TList xs r) (TList ys s2)
unify' _ (TList _ _) _ = Nothing
unify' _ _ (TList _ _) = Nothing
unify' _ _ _ = Nothing

termVars :: Term -> [String]
termVars (Var "_") = []
termVars (Var v) = [v]
termVars (Compound _ as) = concatMap termVars as
termVars (TList xs rest) = concatMap termVars xs ++ maybe [] termVars rest
termVars _ = []

renameVars :: Map String Term -> Term -> Term
renameVars m (Var v) = fromMaybe (Var v) (Map.lookup v m)
renameVars m (Compound f as) = Compound f $ map (renameVars m) as
renameVars m (TList xs rest) = TList (map (renameVars m) xs) (fmap (renameVars m) rest)
renameVars _ t = t

-- Every anonymous variable occurrence gets a distinct inaccessible identity.
freshenAnonTerm :: FreshCounter -> Term -> (Term, FreshCounter)
freshenAnonTerm n (Var "_") = (Var ("_$anon" ++ show n), n + 1)
freshenAnonTerm n (Compound f args) =
  let (args', n') = freshenAnonTerms n args
   in (Compound f args', n')
freshenAnonTerm n (TList xs rest) =
  let (xs', n1) = freshenAnonTerms n xs
      (rest', n2) = case rest of
        Nothing -> (Nothing, n1)
        Just r ->
          let (r', n') = freshenAnonTerm n1 r
           in (Just r', n')
   in (TList xs' rest', n2)
freshenAnonTerm n t = (t, n)

freshenAnonTerms :: FreshCounter -> [Term] -> ([Term], FreshCounter)
freshenAnonTerms n [] = ([], n)
freshenAnonTerms n (x : xs) =
  let (x', n1) = freshenAnonTerm n x
      (xs', n2) = freshenAnonTerms n1 xs
   in (x' : xs', n2)

freshenClause :: FreshCounter -> Clause -> (Clause, FreshCounter)
freshenClause counter (Clause hd body) =
  let namedVars = nub $ concatMap termVars (hd : body)
      mapping =
        Map.fromList
          [ (v, Var ("_$var" ++ show i))
          | (v, i) <- zip namedVars [counter ..]
          ]
      counter1 = counter + length namedVars
      renameNamed = renameVars mapping
      hd1 = renameNamed hd
      body1 = map renameNamed body
      (hd2, counter2) = freshenAnonTerm counter1 hd1
      (body2, counter3) = freshenAnonTerms counter2 body1
   in (Clause hd2 body2, counter3)

prepareQuery :: [Term] -> ([String], [Term], FreshCounter)
prepareQuery goals =
  let visibleVars = nub $ concatMap termVars goals
      (goals', counter) = freshenAnonTerms 0 goals
   in (visibleVars, goals', counter)

-- ─── SOLVER STATE, CONSTRAINTS, AND OUTCOMES ─────────────────────────────────

data Constraint
  = Diseq Term Term
  | IntEq Term Term
  deriving (Show, Eq)

data OutputEvent
  = WriteEvent String
  | NewlineEvent
  deriving (Show, Eq)

data SolverState = SolverState
  { solverSubst :: !Subst,
    solverConstraints :: ![Constraint],
    solverOutput :: ![OutputEvent]
  }
  deriving (Show, Eq)

emptySolverState :: SolverState
emptySolverState =
  SolverState
    { solverSubst = Map.empty,
      solverConstraints = [],
      solverOutput = []
    }

data SolveError
  = InstantiationError Term
  | ExpectedInteger Term
  | ExpectedNumber Term
  | DivisionByZero
  | NegativeIntegerExponent Integer
  deriving (Show, Eq)

data SearchItem
  = Found SolverState
  | BranchExhausted
  | BranchError SolveError
  deriving (Show, Eq)

type Search = [SearchItem]

type Checked a = Either SolveError (Maybe a)

maxResolutionDepth :: Int
maxResolutionDepth = 100000

-- ─── SAFE ARITHMETIC ─────────────────────────────────────────────────────────

data NumericValue
  = NVInt Integer
  | NVFloat Double
  deriving (Show, Eq)

numericTerm :: NumericValue -> Term
numericTerm (NVInt n) = IntLit n
numericTerm (NVFloat d) = FloatLit d

numericDouble :: NumericValue -> Double
numericDouble (NVInt n) = fromIntegral n
numericDouble (NVFloat d) = d

evalArithSafe :: Subst -> Term -> Either SolveError (Maybe Term)
evalArithSafe s t = fmap (fmap numericTerm) (evalNumeric s t)

evalNumeric :: Subst -> Term -> Either SolveError (Maybe NumericValue)
evalNumeric s term = case deepWalk s term of
  Var _ -> Right Nothing
  IntLit n -> Right $ Just (NVInt n)
  FloatLit d -> Right $ Just (NVFloat d)
  Compound "plus" [a, b] -> numericBinOp (+) (+) s a b
  Compound "minus" [a, b] -> numericBinOp (-) (-) s a b
  Compound "mul" [a, b] -> numericBinOp (*) (*) s a b
  Compound "div" [a, b] -> do
    ma <- evalNumeric s a
    mb <- evalNumeric s b
    case (ma, mb) of
      (_, Just (NVInt 0)) -> Left DivisionByZero
      (_, Just (NVFloat 0)) -> Left DivisionByZero
      (Just (NVInt x), Just (NVInt y)) -> Right $ Just $ NVInt (x `div` y)
      (Just x, Just y) -> Right $ Just $ NVFloat (numericDouble x / numericDouble y)
      _ -> Right Nothing
  Compound "mod" [a, b] -> do
    ma <- evalNumeric s a
    mb <- evalNumeric s b
    case (ma, mb) of
      (_, Just (NVInt 0)) -> Left DivisionByZero
      (Just (NVInt x), Just (NVInt y)) -> Right $ Just $ NVInt (x `mod` y)
      (Just _, Just bad) -> Left $ ExpectedInteger (numericTerm bad)
      _ -> Right Nothing
  Compound "^" [a, b] -> do
    ma <- evalNumeric s a
    mb <- evalNumeric s b
    case (ma, mb) of
      (_, Just (NVInt exponent)) | exponent < 0 ->
        Left $ NegativeIntegerExponent exponent
      (Just (NVInt base), Just (NVInt exponent)) ->
        Right $ Just $ NVInt (base ^ exponent)
      (Just base, Just exponent) ->
        Right $ Just $ NVFloat (numericDouble base ** numericDouble exponent)
      _ -> Right Nothing
  bad -> Left $ ExpectedNumber bad

numericBinOp
  :: (Integer -> Integer -> Integer)
  -> (Double -> Double -> Double)
  -> Subst
  -> Term
  -> Term
  -> Either SolveError (Maybe NumericValue)
numericBinOp iop fop s a b = do
  ma <- evalNumeric s a
  mb <- evalNumeric s b
  pure $ case (ma, mb) of
    (Just (NVInt x), Just (NVInt y)) -> Just $ NVInt (iop x y)
    (Just x, Just y) -> Just $ NVFloat (fop (numericDouble x) (numericDouble y))
    _ -> Nothing

-- Integer-only evaluator for #= constraints. Nothing means blocked on variables;
-- malformed expressions and invalid arithmetic are explicit errors.
evalIntExpr :: Subst -> Term -> Either SolveError (Maybe Integer)
evalIntExpr s term = case deepWalk s term of
  Var _ -> Right Nothing
  IntLit n -> Right $ Just n
  bad@(FloatLit _) -> Left $ ExpectedInteger bad
  Compound "plus" [a, b] -> intBinOp (+) s a b
  Compound "minus" [a, b] -> intBinOp (-) s a b
  Compound "mul" [a, b] -> intBinOp (*) s a b
  Compound "div" [a, b] -> do
    ma <- evalIntExpr s a
    mb <- evalIntExpr s b
    case (ma, mb) of
      (_, Just 0) -> Left DivisionByZero
      (Just x, Just y) -> Right $ Just (x `div` y)
      _ -> Right Nothing
  Compound "mod" [a, b] -> do
    ma <- evalIntExpr s a
    mb <- evalIntExpr s b
    case (ma, mb) of
      (_, Just 0) -> Left DivisionByZero
      (Just x, Just y) -> Right $ Just (x `mod` y)
      _ -> Right Nothing
  Compound "^" [a, b] -> do
    ma <- evalIntExpr s a
    mb <- evalIntExpr s b
    case (ma, mb) of
      (_, Just exponent) | exponent < 0 -> Left $ NegativeIntegerExponent exponent
      (Just base, Just exponent) -> Right $ Just (base ^ exponent)
      _ -> Right Nothing
  bad -> Left $ ExpectedInteger bad

intBinOp
  :: (Integer -> Integer -> Integer)
  -> Subst
  -> Term
  -> Term
  -> Either SolveError (Maybe Integer)
intBinOp op s a b = do
  ma <- evalIntExpr s a
  mb <- evalIntExpr s b
  pure $ op <$> ma <*> mb

arithOps :: [String]
arithOps = ["plus", "minus", "mul", "div", "mod", "^"]

arithFreeVars :: Term -> [String]
arithFreeVars (Var v) = [v]
arithFreeVars (Compound f [a, b])
  | f `elem` arithOps = arithFreeVars a ++ arithFreeVars b
arithFreeVars _ = []

data LinearForm = LinearForm
  { linearCoefficient :: Integer,
    linearConstant :: Integer
  }
  deriving (Show, Eq)

scaleLinear :: Integer -> LinearForm -> LinearForm
scaleLinear k (LinearForm coefficient constant) =
  LinearForm (k * coefficient) (k * constant)

-- Convert an expression to coefficient*v + constant. Only exact linear integer
-- operations are accepted; div, mod, exponentiation, and products of unknowns
-- deliberately remain residual constraints.
linearize :: Subst -> String -> Term -> Maybe LinearForm
linearize s wanted term = case deepWalk s term of
  Var v
    | v == wanted -> Just $ LinearForm 1 0
    | otherwise -> Nothing
  IntLit n -> Just $ LinearForm 0 n
  Compound "plus" [a, b] -> do
    LinearForm ca ka <- linearize s wanted a
    LinearForm cb kb <- linearize s wanted b
    pure $ LinearForm (ca + cb) (ka + kb)
  Compound "minus" [a, b] -> do
    LinearForm ca ka <- linearize s wanted a
    LinearForm cb kb <- linearize s wanted b
    pure $ LinearForm (ca - cb) (ka - kb)
  Compound "mul" [a, b] -> do
    la@(LinearForm ca ka) <- linearize s wanted a
    lb@(LinearForm cb kb) <- linearize s wanted b
    case (ca == 0, cb == 0) of
      (True, _) -> pure $ scaleLinear ka lb
      (_, True) -> pure $ scaleLinear kb la
      _ -> Nothing
  _ -> Nothing

data LinearResult
  = LinearBinding String Integer
  | LinearSatisfied
  | LinearContradiction
  | NotLinear
  deriving (Show, Eq)

solveLinearEquation :: Subst -> Term -> Integer -> LinearResult
solveLinearEquation s expr target =
  case nub $ arithFreeVars $ deepWalk s expr of
    [v] -> case linearize s v expr of
      Nothing -> NotLinear
      Just (LinearForm coefficient constant)
        | coefficient == 0 ->
            if constant == target then LinearSatisfied else LinearContradiction
        | (target - constant) `mod` coefficient /= 0 -> LinearContradiction
        | otherwise ->
            LinearBinding v ((target - constant) `div` coefficient)
    [] -> case evalIntExpr s expr of
      Right (Just n) -> if n == target then LinearSatisfied else LinearContradiction
      _ -> NotLinear
    _ -> NotLinear

-- Eagerly reduce fully-ground arithmetic subexpressions before predicate-head
-- matching. Errors are left in symbolic form and are handled by arithmetic goals.
normArithTerm :: Subst -> Term -> Term
normArithTerm s t = case deepWalk s t of
  Compound f as | f `elem` arithOps ->
    let as' = map (normArithTerm s) as
        t' = Compound f as'
     in case evalArithSafe emptySubst t' of
          Right (Just v) -> v
          _ -> t'
  Compound f as -> Compound f $ map (normArithTerm s) as
  TList xs rest -> TList (map (normArithTerm s) xs) (fmap (normArithTerm s) rest)
  t' -> t'

-- ─── CONSTRAINT NORMALIZATION ────────────────────────────────────────────────

reduceDisequality
  :: Subst
  -> [Constraint]
  -> Term
  -> Term
  -> Checked (Subst, [Constraint])
reduceDisequality s kept a b =
  let a' = deepWalk s a
      b' = deepWalk s b
   in if a' == b'
        then Right Nothing
        else case unifySubst s a' b' of
          Nothing -> Right $ Just (s, kept)
          Just _ -> Right $ Just (s, Diseq a' b' : kept)

propagateInteger
  :: Subst
  -> [Constraint]
  -> Term
  -> Integer
  -> Checked (Subst, [Constraint])
propagateInteger s kept expression target =
  case deepWalk s expression of
    Var v -> Right $ Just (Map.insert v (IntLit target) s, kept)
    expression' -> case solveLinearEquation s expression' target of
      LinearBinding v value ->
        Right $ Just (Map.insert v (IntLit value) s, kept)
      LinearSatisfied -> Right $ Just (s, kept)
      LinearContradiction -> Right Nothing
      NotLinear ->
        Right $ Just (s, IntEq expression' (IntLit target) : kept)

reduceConstraint
  :: (Subst, [Constraint])
  -> Constraint
  -> Checked (Subst, [Constraint])
reduceConstraint (s, kept) constraint = case constraint of
  Diseq a b -> reduceDisequality s kept a b
  IntEq a b -> do
    let a' = deepWalk s a
        b' = deepWalk s b
    ma <- evalIntExpr s a'
    mb <- evalIntExpr s b'
    case (ma, mb) of
      (Just x, Just y)
        | x == y -> Right $ Just (s, kept)
        | otherwise -> Right Nothing
      (Nothing, Just target) -> propagateInteger s kept a' target
      (Just target, Nothing) -> propagateInteger s kept b' target
      (Nothing, Nothing) -> Right $ Just (s, IntEq a' b' : kept)

normalizeState :: SolverState -> Checked SolverState
normalizeState initial = loop initial
  where
    loop st = do
      result <- reduceAll (solverSubst st, []) (solverConstraints st)
      case result of
        Nothing -> Right Nothing
        Just (s', reversedConstraints) ->
          let constraints' = reverse reversedConstraints
              st' =
                st
                  { solverSubst = s',
                    solverConstraints = constraints'
                  }
           in if s' == solverSubst st
                && constraints' == solverConstraints st
                then Right $ Just st'
                else loop st'

    reduceAll
      :: (Subst, [Constraint])
      -> [Constraint]
      -> Checked (Subst, [Constraint])
    reduceAll acc [] = Right $ Just acc
    reduceAll acc (constraint : rest) = do
      next <- reduceConstraint acc constraint
      case next of
        Nothing -> Right Nothing
        Just acc' -> reduceAll acc' rest

addConstraint :: Constraint -> SolverState -> Checked SolverState
addConstraint constraint st =
  normalizeState
    st
      { solverConstraints = constraint : solverConstraints st
      }

unifyState :: SolverState -> Term -> Term -> Checked SolverState
unifyState st a b = case unifySubst (solverSubst st) a b of
  Nothing -> Right Nothing
  Just s' -> normalizeState st {solverSubst = s'}

appendOutput :: OutputEvent -> SolverState -> SolverState
appendOutput event st =
  st
    { solverOutput = solverOutput st ++ [event]
    }

-- ─── SEARCH ──────────────────────────────────────────────────────────────────

continueChecked :: Checked SolverState -> (SolverState -> Search) -> Search
continueChecked result continue = case result of
  Left err -> [BranchError err]
  Right Nothing -> []
  Right (Just st) -> continue st

solve :: Program -> [Term] -> ([String], Search)
solve prog goals =
  let (visibleVars, preparedGoals, counter) = prepareQuery goals
   in (visibleVars, solveGoals prog emptySolverState preparedGoals counter maxResolutionDepth)

solveGoals
  :: Program
  -> SolverState
  -> [Term]
  -> FreshCounter
  -> Int
  -> Search
solveGoals _ st [] _ _ = [Found st]
solveGoals _ _ _ _ 0 = [BranchExhausted]
solveGoals prog st (g : gs) counter fuel =
  let s = solverSubst st
   in case walk s g of
        Compound "unify" [a, b] ->
          continueChecked
            (unifyState st a b)
            (\st' -> solveGoals prog st' gs counter fuel)
        Compound "equiv" [a, b] ->
          if deepWalk s a == deepWalk s b
            then solveGoals prog st gs counter fuel
            else []
        Compound "neq" [a, b] ->
          continueChecked
            (addConstraint (Diseq a b) st)
            (\st' -> solveGoals prog st' gs counter fuel)
        Compound "int_eq" [a, b] ->
          continueChecked
            (addConstraint (IntEq a b) st)
            (\st' -> solveGoals prog st' gs counter fuel)
        Compound "gt" [a, b] ->
          solveComparison (>) prog st a b gs counter fuel
        Compound "lt" [a, b] ->
          solveComparison (<) prog st a b gs counter fuel
        Compound "gte" [a, b] ->
          solveComparison (>=) prog st a b gs counter fuel
        Compound "lte" [a, b] ->
          solveComparison (<=) prog st a b gs counter fuel
        Compound "is" [lhs, rhs] ->
          case evalArithSafe s rhs of
            Left err -> [BranchError err]
            Right Nothing -> [BranchError $ InstantiationError rhs]
            Right (Just value) ->
              continueChecked
                (unifyState st lhs value)
                (\st' -> solveGoals prog st' gs counter fuel)
        Compound "call" (pred' : args) ->
          let pred'' = walk s pred'
              goal = case pred'' of
                Atom f -> Compound f args
                Compound f as' -> Compound f (as' ++ args)
                _ -> Compound "call" (pred'' : args)
           in solveGoals prog st (goal : gs) counter fuel
        Compound "phrase" [nt, lst] ->
          let nt' = walk s nt
              goal = case nt' of
                Atom f -> Compound f [lst, TList [] Nothing]
                Compound f as -> Compound f (as ++ [lst, TList [] Nothing])
                _ -> Compound "call" [nt', lst, TList [] Nothing]
           in solveGoals prog st (goal : gs) counter fuel
        Compound "not" [goal] ->
          solveNegated prog st goal gs counter fuel
        Compound "once" [goal] ->
          solveOnce prog st goal gs counter fuel
        Compound "write" [value] ->
          let rendered = show $ deepWalk s value
              st' = appendOutput (WriteEvent rendered) st
           in solveGoals prog st' gs counter fuel
        Atom "nl" ->
          solveGoals prog (appendOutput NewlineEvent st) gs counter fuel
        Atom "true" -> solveGoals prog st gs counter fuel
        Atom "fail" -> []
        goal ->
          concatMap
            (tryClause prog st goal gs counter fuel)
            prog

solveComparison
  :: (Double -> Double -> Bool)
  -> Program
  -> SolverState
  -> Term
  -> Term
  -> [Term]
  -> FreshCounter
  -> Int
  -> Search
solveComparison cmp prog st a b rest counter fuel =
  case (evalNumeric (solverSubst st) a, evalNumeric (solverSubst st) b) of
    (Left err, _) -> [BranchError err]
    (_, Left err) -> [BranchError err]
    (Right Nothing, _) -> [BranchError $ InstantiationError a]
    (_, Right Nothing) -> [BranchError $ InstantiationError b]
    (Right (Just va), Right (Just vb))
      | cmp (numericDouble va) (numericDouble vb) ->
          solveGoals prog st rest counter fuel
      | otherwise -> []

solveNegated
  :: Program
  -> SolverState
  -> Term
  -> [Term]
  -> FreshCounter
  -> Int
  -> Search
solveNegated prog st negated rest counter fuel =
  let subsearch = solveGoals prog st [negated] counter fuel
      hasAnswer = any isAnswer subsearch
      errors = [err | BranchError err <- subsearch]
      exhausted = any isExhausted subsearch
   in if hasAnswer
        then []
        else case errors of
          err : _ -> [BranchError err]
          []
            | exhausted -> [BranchExhausted]
            | otherwise -> solveGoals prog st rest counter fuel
  where
    isAnswer (Found _) = True
    isAnswer _ = False
    isExhausted BranchExhausted = True
    isExhausted _ = False

solveOnce
  :: Program
  -> SolverState
  -> Term
  -> [Term]
  -> FreshCounter
  -> Int
  -> Search
solveOnce prog st goal rest counter fuel =
  let subsearch = solveGoals prog st [goal] counter fuel
   in case [answer | Found answer <- subsearch] of
        answer : _ -> solveGoals prog answer rest counter fuel
        [] -> case [err | BranchError err <- subsearch] of
          err : _ -> [BranchError err]
          []
            | any isExhausted subsearch -> [BranchExhausted]
            | otherwise -> []
  where
    isExhausted BranchExhausted = True
    isExhausted _ = False

tryClause
  :: Program
  -> SolverState
  -> Term
  -> [Term]
  -> FreshCounter
  -> Int
  -> Clause
  -> Search
tryClause prog st goal restGoals counter fuel clause
  | fuel <= 0 = [BranchExhausted]
  | otherwise =
      let (Clause hd body, counter') = freshenClause counter clause
          normalizedGoal = normArithTerm (solverSubst st) goal
       in continueChecked
            (unifyState st normalizedGoal hd)
            ( \st' ->
                solveGoals
                  prog
                  st'
                  (body ++ restGoals)
                  counter'
                  (fuel - 1)
            )

-- ─── ANSWER PROJECTION AND RENDERING ─────────────────────────────────────────

deepEval :: Subst -> Term -> Term
deepEval s t = tryEval (deepWalk s t)
  where
    tryEval t' = case evalArithSafe emptySubst t' of
      Right (Just v) -> v
      _ -> case t' of
        Compound f as -> Compound f $ map tryEval as
        TList xs r -> TList (map tryEval xs) $ fmap tryEval r
        _ -> t'

data Answer = Answer
  { answerBindings :: Map String Term,
    answerConstraints :: [Constraint],
    answerOutput :: [OutputEvent]
  }
  deriving (Show, Eq)

walkConstraint :: Subst -> Constraint -> Constraint
walkConstraint s (Diseq a b) = Diseq (deepEval s a) (deepEval s b)
walkConstraint s (IntEq a b) = IntEq (deepEval s a) (deepEval s b)

constraintVars :: Constraint -> [String]
constraintVars (Diseq a b) = termVars a ++ termVars b
constraintVars (IntEq a b) = termVars a ++ termVars b

-- Keep only residual constraints connected to a visible query variable. This
-- prevents constraints on anonymous or purely clause-local variables from
-- leaking into otherwise ground answers.
relevantConstraints :: [String] -> [Constraint] -> [Constraint]
relevantConstraints seed constraints = go (nub seed) [] constraints
  where
    go known selected remaining =
      let (newlyRelevant, stillRemaining) = splitRelevant known remaining
          known' = nub $ known ++ concatMap constraintVars newlyRelevant
       in if null newlyRelevant
            then reverse selected
            else go known' (reverse newlyRelevant ++ selected) stillRemaining

    splitRelevant _ [] = ([], [])
    splitRelevant known (constraint : rest) =
      let (yes, no) = splitRelevant known rest
       in if any (`elem` known) (constraintVars constraint)
            then (constraint : yes, no)
            else (yes, constraint : no)

isInternalVar :: String -> Bool
isInternalVar = isPrefixOf "_$"

reifyConstraint :: Map String Term -> Constraint -> Constraint
reifyConstraint names (Diseq a b) = Diseq (renameVars names a) (renameVars names b)
reifyConstraint names (IntEq a b) = IntEq (renameVars names a) (renameVars names b)

-- Give internal variables stable, readable names in projected answers.
reifyAnswer :: Answer -> Answer
reifyAnswer answer =
  let allTerms =
        Map.elems (answerBindings answer)
          ++ concatMap constraintTerms (answerConstraints answer)
      internalVars = nub [v | term <- allTerms, v <- termVars term, isInternalVar v]
      names =
        Map.fromList
          [ (v, Var ("_" ++ show i))
          | (v, i) <- zip internalVars [(0 :: Int) ..]
          ]
   in answer
        { answerBindings = fmap (renameVars names) (answerBindings answer),
          answerConstraints = map (reifyConstraint names) (answerConstraints answer)
        }
  where
    constraintTerms (Diseq a b) = [a, b]
    constraintTerms (IntEq a b) = [a, b]

projectAnswer :: [String] -> SolverState -> Answer
projectAnswer visible st =
  let s = solverSubst st
      bindings =
        Map.fromList
          [ (v, deepEval s (Var v))
          | v <- visible
          , deepEval s (Var v) /= Var v
          ]
      constraints = map (walkConstraint s) (solverConstraints st)
   in reifyAnswer $
        Answer
          { answerBindings = bindings,
            answerConstraints = constraints,
            answerOutput = solverOutput st
          }

showConstraint :: Constraint -> String
showConstraint (Diseq a b) = show a ++ " != " ++ show b
showConstraint (IntEq a b) = show a ++ " #= " ++ show b

showAnswer :: Answer -> String
showAnswer answer
  | null pieces = "true."
  | otherwise = intercalate ", " pieces
  where
    bindings =
      [ v ++ " = " ++ show t
      | (v, t) <- Map.toList (answerBindings answer)
      ]
    constraints = map showConstraint (answerConstraints answer)
    pieces = bindings ++ constraints

showSolveError :: SolveError -> String
showSolveError (InstantiationError t) =
  "arithmetic expression is not sufficiently instantiated: " ++ show t
showSolveError (ExpectedInteger t) =
  "expected an integer expression, but got: " ++ show t
showSolveError (ExpectedNumber t) =
  "expected a numeric expression, but got: " ++ show t
showSolveError DivisionByZero = "division by zero"
showSolveError (NegativeIntegerExponent n) =
  "negative exponent in integer exponentiation: " ++ show n

renderOutputEvent :: OutputEvent -> String
renderOutputEvent (WriteEvent text) = text
renderOutputEvent NewlineEvent = "\n"

data QuerySummary = QuerySummary
  { summaryAnswers :: [Answer],
    summaryErrors :: [SolveError],
    summaryExhausted :: Bool
  }
  deriving (Show, Eq)

summarizeSearch :: [String] -> Search -> QuerySummary
summarizeSearch visible items =
  QuerySummary
    { summaryAnswers = [projectAnswer visible st | Found st <- items],
      summaryErrors = nub [err | BranchError err <- items],
      summaryExhausted = any isExhausted items
    }
  where
    isExhausted BranchExhausted = True
    isExhausted _ = False

solveAll :: Program -> [Term] -> QuerySummary
solveAll prog goals =
  let (visible, search) = solve prog goals
   in summarizeSearch visible search

runProlog :: String -> String -> Either String [String]
runProlog programSrc querySrc = do
  prog <- parseProgram programSrc
  goals <- parseGoals querySrc
  let summary = solveAll prog goals
      answers = summaryAnswers summary
      errors = summaryErrors summary
      exhausted = summaryExhausted summary
      renderedAnswers = concatMap renderAnswerWithOutput answers
  pure $ case renderedAnswers of
    _ : _ ->
      renderedAnswers
        ++ ["Search depth limit reached; more solutions may exist." | exhausted]
    [] -> case errors of
      err : _ -> ["Error: " ++ showSolveError err]
      []
        | exhausted -> ["Search depth limit reached; the query was not proven false."]
        | otherwise -> ["false."]
  where
    renderAnswerWithOutput answer =
      let output = concatMap renderOutputEvent (answerOutput answer)
       in [output | not (null output)] ++ [showAnswer answer]

-- ─── MODULE SYSTEM ───────────────────────────────────────────────────────────

sha1Hex :: String -> String
sha1Hex s = concatMap byte2hex $ BS.unpack $ SHA1.hash $ BSC.pack s
  where
    byte2hex b =
      let h = showHex b ""
       in if length h == 1 then '0' : h else h

type ModuleConf = Map String FilePath

findNPrologConf :: IO (Maybe FilePath)
findNPrologConf = do
  let local = "neoprolog.conf"
  localExists <- doesFileExist local
  if localExists
    then return (Just local)
    else do
      home <- getHomeDirectory
      let homeConf = home </> "nprolog" </> "neoprolog.conf"
      homeExists <- doesFileExist homeConf
      return $ if homeExists then Just homeConf else Nothing

loadNPrologConf :: IO ModuleConf
loadNPrologConf = do
  mpath <- findNPrologConf
  case mpath of
    Nothing -> return Map.empty
    Just path -> do
      contents <- readFile path
      let lineWords =
            map words $
              filter (\line -> not (null line) && head line /= '#') (lines contents)
      return $ Map.fromList [(key, fp) | [key, fp] <- lineWords]

registerModule :: FilePath -> IO ()
registerModule path = do
  absPath <- canonicalizePath path
  let modName = takeBaseName absPath
      hash = sha1Hex absPath
      key = modName ++ "#" ++ hash
      entry = key ++ " " ++ absPath ++ "\n"
  appendFile "neoprolog.conf" entry
  putStrLn $ "Registered " ++ key ++ " -> " ++ absPath

parseModRef :: String -> Maybe (String, String)
parseModRef s = case break (== '#') s of
  (modName, '#' : hash)
    | not (null modName), not (null hash) -> Just (modName, hash)
  _ -> Nothing

moduleFunctors :: [Clause] -> [String]
moduleFunctors cs = nub [f | Clause hd _ <- cs, f <- headFunctor hd]
  where
    headFunctor (Atom f) = [f]
    headFunctor (Compound f _) = [f]
    headFunctor _ = []

qualifyFunctor :: String -> [String] -> Term -> Term
qualifyFunctor m known (Atom f)
  | f `elem` known = Atom (m ++ ":" ++ f)
qualifyFunctor m known (Compound f as)
  | f `elem` known = Compound (m ++ ":" ++ f) (map (qualifyTerm m known) as)
qualifyFunctor m known (Compound f as) =
  Compound f (map (qualifyTerm m known) as)
qualifyFunctor m known (TList xs rest) =
  TList (map (qualifyTerm m known) xs) (fmap (qualifyTerm m known) rest)
qualifyFunctor _ _ t = t

qualifyTerm :: String -> [String] -> Term -> Term
qualifyTerm = qualifyFunctor

qualifyClause :: String -> [String] -> Clause -> Clause
qualifyClause modName known (Clause hd body) =
  Clause
    (qualifyFunctor modName known hd)
    (map (qualifyFunctor modName known) body)

processImport :: ModuleConf -> String -> IO (Either String [Clause])
processImport conf modRef = case parseModRef modRef of
  Nothing -> return $ Left $ "Invalid module reference: " ++ modRef
  Just (modName, _) -> case Map.lookup modRef conf of
    Nothing -> return $ Left $ "Module '" ++ modRef ++ "' not found in neoprolog.conf"
    Just fp -> do
      result <- CE.try (readFile fp) :: IO (Either CE.SomeException String)
      case result of
        Left ex -> return $ Left (show ex)
        Right contents -> case parseFile contents of
          Left err -> return $ Left err
          Right items -> do
            let rawClauses = [c | TLClause c <- items]
                known = moduleFunctors rawClauses
            return $ Right (map (qualifyClause modName known) rawClauses)

processTopLevels
  :: ModuleConf
  -> [TopLevel]
  -> IO (Either String ([Clause], [[Term]]))
processTopLevels conf = foldM step (Right ([], []))
  where
    step (Left e) _ = return (Left e)
    step (Right (cs, qs)) (TLClause c) = return $ Right (cs ++ [c], qs)
    step (Right (cs, qs)) (TLQuery gs) = return $ Right (cs, qs ++ [gs])
    step (Right (cs, qs)) (TLDirective [Compound "import" [StrLit ref]]) = do
      res <- processImport conf ref
      case res of
        Left e -> return $ Left e
        Right newCs -> return $ Right (cs ++ newCs, qs)
    step (Right _) (TLDirective goals) =
      return $ Left $ "Unknown directive: " ++ show goals

-- ─── REPL, COMPLETION, AND PRETTY PRINTING ───────────────────────────────────

renderDoc :: Doc AnsiStyle -> String
renderDoc = unpack . renderStrict . layoutPretty defaultLayoutOptions

docErr :: String -> Doc AnsiStyle
docErr msg =
  annotate (bold <> color Red) (pretty "Error: ")
    <> annotate (color Red) (pretty msg)

docInfo :: String -> Doc AnsiStyle
docInfo = annotate (colorDull Cyan) . pretty

docAnswer :: Answer -> Doc AnsiStyle
docAnswer answer
  | null pieces = annotate (bold <> color Green) (pretty "true.")
  | otherwise = hsep $ punctuate comma pieces
  where
    bindingDocs =
      [ annotate (color Yellow) (pretty v)
          <+> annotate (colorDull White) (pretty "=")
          <+> annotate (color Cyan) (pretty (show t))
      | (v, t) <- Map.toList (answerBindings answer)
      ]
    constraintDocs =
      [ annotate (color Magenta) (pretty (showConstraint constraint))
      | constraint <- answerConstraints answer
      ]
    pieces = bindingDocs ++ constraintDocs

progPreds :: Program -> [String]
progPreds prog =
  nub
    [ name
    | c <- prog,
      let name = case clauseHead c of
            Atom f -> f
            Compound f _ -> f
            _ -> "",
      not $ null name
    ]

prologComplete
  :: IORef Program
  -> CompletionFunc IO
prologComplete progRef input@(leftRev, _)
  | ":load " `isPrefixOf` left = completeFilename input
  | otherwise = completeWord Nothing " \t,(.?" completeIdent input
  where
    left = reverse leftRev
    completeIdent word = do
      prog <- readIORef progRef
      let preds =
            nub
              ( progPreds prog
                  ++ [":quit", ":q", ":load", ":reload", ":r"]
              )
      return [simpleCompletion p | p <- preds, word `isPrefixOf` p]

runPrologRepl :: IO ()
runPrologRepl = do
  progRef <- newIORef ([] :: Program)
  fileRef <- newIORef (Nothing :: Maybe FilePath)

  let settings =
        (defaultSettings :: Settings IO)
          { complete = prologComplete progRef,
            historyFile = Just ".infera_history"
          }

  runInputT settings $ do
    outputStrLn $
      renderDoc $
        annotate (bold <> color Cyan) (pretty "Infera")
          <> annotate (colorDull White) (pretty " — clauses: ")
          <> annotate (colorDull Yellow) (pretty "color red.")
          <+> annotate (colorDull White) (pretty "queries: ")
          <> annotate (colorDull Yellow) (pretty "color X?")
    outputStrLn $
      renderDoc $
        annotate
          (colorDull White)
          (pretty "Commands: :load <file>   :reload (:r)   :quit (:q)   Ctrl+D")
    args <- liftIO getArgs
    case args of
      (file : _) -> handleLine progRef fileRef (":load " ++ file)
      [] -> loop progRef fileRef
  where
    prompt = renderDoc $ annotate (bold <> color Blue) (pretty "> ")

    loop progRef fileRef = do
      mline <- getInputLine prompt
      case mline of
        Nothing -> outputStrLn $ renderDoc $ annotate (colorDull Cyan) (pretty "Bye!")
        Just line -> handleLine progRef fileRef $ dropWhileEnd (== ' ') line

    handleLine progRef fileRef trimmed = case trimmed of
      t
        | t == ":quit" || t == ":q" ->
            outputStrLn $ renderDoc $ annotate (colorDull Cyan) (pretty "Bye!")
      t
        | t == ":reload" || t == ":r" -> do
            mfile <- liftIO $ readIORef fileRef
            case mfile of
              Nothing ->
                outputStrLn (renderDoc $ docErr "No file loaded yet. Use :load <file> first.")
                  >> loop progRef fileRef
              Just file -> do
                res <- parseAndLoad progRef file
                case res of
                  Left err -> outputStrLn (renderDoc $ docErr err) >> loop progRef fileRef
                  Right (n, queries) -> do
                    outputStrLn $
                      renderDoc $
                        docInfo
                          ("Reloaded " ++ show n ++ " clause(s) from " ++ show file ++ ".")
                    prog' <- liftIO $ readIORef progRef
                    mapM_ (runInlineQuery prog') queries
                    loop progRef fileRef
      _
        | take 5 trimmed == ":load" -> do
            let raw = dropWhile (== ' ') (drop 5 trimmed)
                file =
                  if length raw >= 2 && head raw == '"' && last raw == '"'
                    then init (tail raw)
                    else raw
            res <- parseAndLoad progRef file
            case res of
              Left err -> outputStrLn (renderDoc $ docErr err) >> loop progRef fileRef
              Right (n, queries) -> do
                liftIO $ writeIORef fileRef (Just file)
                outputStrLn $
                  renderDoc $
                    docInfo
                      ("Loaded " ++ show n ++ " clause(s) from " ++ show file ++ ".")
                prog' <- liftIO $ readIORef progRef
                mapM_ (runInlineQuery prog') queries
                loop progRef fileRef
        | not (null trimmed) && last trimmed == '?' -> do
            let queryStr = init trimmed
            case parseGoals queryStr of
              Left err -> outputStrLn (renderDoc $ docErr err) >> loop progRef fileRef
              Right goals -> do
                prog <- liftIO $ readIORef progRef
                renderQuerySummary $ solveAll prog goals
                loop progRef fileRef
        | null trimmed -> loop progRef fileRef
        | otherwise -> do
            case parseProgram trimmed of
              Left err -> outputStrLn (renderDoc $ docErr err) >> loop progRef fileRef
              Right clauses -> do
                liftIO $ modifyIORef progRef (++ clauses)
                outputStrLn $
                  renderDoc $
                    docInfo ("Added " ++ show (length clauses) ++ " clause(s).")
                loop progRef fileRef

    parseAndLoad progRef file = do
      result <- liftIO (CE.try (readFile file) :: IO (Either CE.SomeException String))
      case result of
        Left ex -> return $ Left (show ex)
        Right contents -> case parseFile contents of
          Left err -> return $ Left err
          Right items -> do
            conf <- liftIO loadNPrologConf
            procResult <- liftIO $ processTopLevels conf items
            case procResult of
              Left err -> return $ Left err
              Right (clauses, queries) -> do
                liftIO $ writeIORef progRef clauses
                return $ Right (length clauses, queries)

    runInlineQuery prog goals = do
      let queryLabel =
            annotate (colorDull White) (pretty "> ")
              <> hsep (punctuate comma (map (pretty . show) goals))
      outputStrLn $ renderDoc queryLabel
      renderQuerySummary $ solveAll prog goals

    renderQuerySummary summary = do
      let answers = summaryAnswers summary
          errors = summaryErrors summary
          exhausted = summaryExhausted summary
      case answers of
        [] -> case errors of
          err : _ -> outputStrLn $ renderDoc $ docErr (showSolveError err)
          []
            | exhausted ->
                outputStrLn $
                  renderDoc $
                    annotate
                      (bold <> color Yellow)
                      (pretty "Search depth limit reached; the query was not proven false.")
            | otherwise ->
                outputStrLn $
                  renderDoc $
                    annotate (bold <> color Red) (pretty "false.")
        _ -> do
          mapM_ renderAnswer answers
          case errors of
            [] -> pure ()
            err : _ ->
              outputStrLn $
                renderDoc $
                  annotate
                    (color Yellow)
                    (pretty ("Some branches raised an error: " ++ showSolveError err))
          if exhausted
            then
              outputStrLn $
                renderDoc $
                  annotate
                    (color Yellow)
                    (pretty "Search depth limit reached; more solutions may exist.")
            else pure ()

    renderAnswer answer = do
      let output = concatMap renderOutputEvent (answerOutput answer)
      if null output then pure () else outputStr output
      outputStrLn $ renderDoc $ docAnswer answer

main :: IO ()
main = do
  args <- getArgs
  case args of
    ("reg" : paths) -> mapM_ registerModule paths
    _ -> runPrologRepl

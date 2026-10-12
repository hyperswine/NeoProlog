{-# OPTIONS_GHC -Wno-name-shadowing #-}
{-# OPTIONS_GHC -Wno-unused-do-bind #-}

-- | Surface syntax for Infera v2: terms, clauses, declarations, the parser and
-- the term printer.
--
-- Variables are represented by integer identifiers.  Every top-level item is
-- parsed in a fresh variable environment, so a clause's variables are numbered
-- @0 .. n-1@ and can be renamed apart by adding an offset.
module Infera.Syntax
  ( -- * Terms
    Term (..),
    VarId,
    nil,
    cons,
    mkList,
    unfoldCons,
    isCallable,
    functorOf,
    showTermWith,
    showVarDefault,
    termVarIds,

    -- * Declarations
    Mode (..),
    Sort (..),
    Det (..),
    ArgSpec (..),
    Flag (..),
    Decl (..),
    showMode,
    showSort,
    showDet,
    showArgSpec,
    showDecl,

    -- * Clauses and files
    Clause (..),
    Query (..),
    TopLevel (..),
    SourceSpan (..),
    LocatedTopLevel (..),
    parseLocatedFile,
    clauseKey,

    -- * Parsing
    parseFile,
    parseProgram,
    parseQuery,
    parseTerm,
    parseClauseText,

    -- * Body helpers
    flattenConj,
    desugarDCG,
  )
where

import Control.Monad (void)
import Control.Monad.Combinators.Expr
import qualified Control.Monad.State.Strict as St
import Data.List (intercalate)
import Data.Char (ord)
import qualified Data.List.NonEmpty as NE
import Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map
import Data.Void
import Text.Megaparsec
import Text.Megaparsec.Char
import qualified Text.Megaparsec.Char.Lexer as L

-- ─── TERMS ───────────────────────────────────────────────────────────────────

type VarId = Int

data Term
  = Atom !String
  | Var !VarId
  | IntLit !Integer
  | FloatLit !Double
  | CharLit !Char
  | StrLit !String
  | Compound !String [Term]
  deriving (Eq, Ord)

nil :: Term
nil = Atom "nil"

cons :: Term -> Term -> Term
cons h t = Compound "cons" [h, t]

mkList :: [Term] -> Maybe Term -> Term
mkList [] Nothing = nil
mkList [] (Just t) = t
mkList (x : xs) r = cons x (mkList xs r)

-- | Unfold a cons chain into its elements and an optional non-nil tail.
unfoldCons :: Term -> ([Term], Maybe Term)
unfoldCons (Compound "cons" [h, t]) =
  let (xs, rest) = unfoldCons t
   in (h : xs, rest)
unfoldCons (Atom "nil") = ([], Nothing)
unfoldCons t = ([], Just t)

isCallable :: Term -> Bool
isCallable (Atom _) = True
isCallable (Compound _ _) = True
isCallable _ = False

-- | Name and arity of a callable term.
functorOf :: Term -> Maybe (String, Int)
functorOf (Atom f) = Just (f, 0)
functorOf (Compound f as) = Just (f, length as)
functorOf _ = Nothing

termVarIds :: Term -> [VarId]
termVarIds (Var v) = [v]
termVarIds (Compound _ as) = concatMap termVarIds as
termVarIds _ = []

showVarDefault :: VarId -> String
showVarDefault v = "_G" ++ show v

instance Show Term where
  show = showTermWith showVarDefault

-- Operator table for printing: (internal name, symbol, precedence, assoc).
-- Higher precedence binds tighter.
data Assoc = AL | AR | AN deriving (Eq)

infixTable :: Map String (String, Int, Assoc)
infixTable =
  Map.fromList
    [ ("^", ("^", 9, AR)),
      ("mul", ("*", 8, AL)),
      ("div", ("/", 8, AL)),
      ("mod", ("%", 8, AL)),
      ("plus", ("+", 7, AL)),
      ("minus", ("-", 7, AL)),
      ("range", ("..", 6, AN)),
      ("gte", (">=", 5, AN)),
      ("lte", ("<=", 5, AN)),
      ("gt", (">", 5, AN)),
      ("lt", ("<", 5, AN)),
      ("fd_ge", ("#>=", 5, AN)),
      ("fd_le", ("#<=", 5, AN)),
      ("fd_gt", ("#>", 5, AN)),
      ("fd_lt", ("#<", 5, AN)),
      ("int_eq", ("#=", 4, AN)),
      ("fd_ne", ("#!=", 4, AN)),
      ("equiv", ("==", 4, AN)),
      ("neq", ("!=", 4, AN)),
      ("unify", ("=", 4, AN)),
      ("is", ("is", 4, AN)),
      ("in", ("in", 4, AN)),
      (",", (",", 3, AR)),
      ("->", ("->", 2, AR)),
      (";", (";", 1, AR))
    ]

-- | Render a term, naming variables with the supplied function.
showTermWith :: (VarId -> String) -> Term -> String
showTermWith name = go 0
  where
    go :: Int -> Term -> String
    go _ (Atom "nil") = "[]"
    go _ (Atom s) = s
    go _ (Var v) = name v
    go _ (IntLit n) = show n
    go _ (FloatLit d) = show d
    go _ (CharLit c) = show c
    go _ (StrLit s) = show s
    go _ t@(Compound "cons" [_, _]) = showList' t
    go ctx (Compound f [a, b])
      | Just (sym, prec, assoc) <- Map.lookup f infixTable =
          let l = go (if assoc == AL then prec else prec + 1) a
              r = go (if assoc == AR then prec else prec + 1) b
              body = l ++ " " ++ sym ++ " " ++ r
           in if prec < ctx then "(" ++ body ++ ")" else body
    go _ (Compound f []) = f
    go _ (Compound f as) = f ++ " " ++ unwords (map arg as)

    arg t@(Compound "cons" [_, _]) = showList' t
    arg t@(Compound _ (_ : _)) = "(" ++ go 0 t ++ ")"
    arg t = go 0 t

    showList' t =
      let (xs, rest) = unfoldCons t
       in "["
            ++ intercalate ", " (map (go 0) xs)
            ++ maybe "" (\r -> " | " ++ go 0 r) rest
            ++ "]"

-- ─── DECLARATION TYPES ───────────────────────────────────────────────────────

-- | Argument modes.  @<=@ is input (must be ground at call), @=>@ is output
-- (ground after the call), @<=>@ places no requirement.
data Mode = ModeIn | ModeOut | ModeInOut
  deriving (Show, Eq, Ord)

-- | Sorts (types).  'SNone' is the bottom element used only during inference
-- (no evidence yet); it is never written by users.
data Sort
  = SAny
  | SNum
  | SInt
  | SFloat
  | SStr
  | SChar
  | SAtom
  | SList Sort
  | SNone
  deriving (Show, Eq, Ord)

-- | Determinism categories (Mercury-style).
data Det
  = Det -- exactly one solution
  | Semidet -- at most one
  | Multi -- at least one
  | Nondet -- any number
  deriving (Show, Eq, Ord)

data ArgSpec = ArgSpec
  { argSort :: Sort,
    argMode :: Mode
  }
  deriving (Show, Eq, Ord)

data Flag = FlagTable | FlagNoTable | FlagIndex | FlagNoIndex
  deriving (Show, Eq, Ord)

-- | A predicate declaration: @name : det flags (sort: mode) ...@
data Decl = Decl
  { declName :: String,
    declDet :: Maybe Det,
    declFlags :: [Flag],
    declArgs :: [ArgSpec]
  }
  deriving (Show, Eq)

showMode :: Mode -> String
showMode ModeIn = "<="
showMode ModeOut = "=>"
showMode ModeInOut = "<=>"

showSort :: Sort -> String
showSort SAny = "any"
showSort SNum = "num"
showSort SInt = "int"
showSort SFloat = "float"
showSort SStr = "str"
showSort SChar = "char"
showSort SAtom = "atom"
showSort (SList s@(SList _)) = "list (" ++ showSort s ++ ")"
showSort (SList s) = "list " ++ showSort s
showSort SNone = "none"

showDet :: Det -> String
showDet Det = "det"
showDet Semidet = "semidet"
showDet Multi = "multi"
showDet Nondet = "nondet"

showArgSpec :: ArgSpec -> String
showArgSpec (ArgSpec s m) = "(" ++ showSort s ++ ": " ++ showMode m ++ ")"

showFlag :: Flag -> String
showFlag FlagTable = "table"
showFlag FlagNoTable = "notable"
showFlag FlagIndex = "index"
showFlag FlagNoIndex = "noindex"

showDecl :: Decl -> String
showDecl (Decl n d fs as) =
  n
    ++ " : "
    ++ unwords (maybe [] (\x -> [showDet x]) d ++ map showFlag fs ++ map showArgSpec as)
    ++ "."

-- ─── CLAUSES, QUERIES, FILES ─────────────────────────────────────────────────

data Clause = Clause
  { clauseHead :: Term,
    clauseBody :: [Term],
    -- | Number of distinct variables in the clause (ids are @0 .. n-1@).
    clauseNVars :: Int
  }
  deriving (Show, Eq)

data Query = Query
  { queryGoals :: [Term],
    -- | Named (non-anonymous) query variables in order of appearance.
    queryNames :: [(String, VarId)],
    queryNVars :: Int
  }
  deriving (Show, Eq)

data TopLevel
  = TLClause Clause
  | TLQuery Query
  | TLDirective [Term]
  | TLDecl Decl
  deriving (Show, Eq)

-- | One-based lines and UTF-16 columns. Semantic diagnostics refer to the containing
-- item; parser errors point at the offending character.
data SourceSpan = SourceSpan
  { spanFile :: FilePath,
    spanLine :: Int,
    spanColumn :: Int,
    spanEndLine :: Int,
    spanEndColumn :: Int
  }
  deriving (Show, Eq)

data LocatedTopLevel = LocatedTopLevel
  { locatedSpan :: SourceSpan,
    locatedItem :: TopLevel,
    locatedNames :: [(String, VarId)]
  }
  deriving (Show, Eq)

clauseKey :: Clause -> Maybe (String, Int)
clauseKey = functorOf . clauseHead

-- ─── PARSER STATE ────────────────────────────────────────────────────────────

data ParseEnv = ParseEnv
  { peVars :: Map String VarId,
    peOrder :: [(String, VarId)],
    peTokenEnd :: !Int,
    peNext :: !Int
  }

emptyEnv :: ParseEnv
emptyEnv = ParseEnv Map.empty [] 0 0

type Parser = ParsecT Void String (St.State ParseEnv)

resetEnv :: Parser ()
resetEnv = St.put emptyEnv

freshVar :: Parser Term
freshVar = do
  env <- St.get
  let n = peNext env
  St.put env {peNext = n + 1}
  return (Var n)

namedVar :: String -> Parser Term
namedVar name = do
  env <- St.get
  case Map.lookup name (peVars env) of
    Just v -> return (Var v)
    Nothing -> do
      let n = peNext env
      St.put
        env
          { peVars = Map.insert name n (peVars env),
            peOrder = peOrder env ++ [(name, n)],
            peNext = n + 1
          }
      return (Var n)

-- ─── LEXING ──────────────────────────────────────────────────────────────────

-- @#@ starts a line comment unless it is immediately followed by one of the
-- CLP(Z) operator characters (@#=@, @#!=@, @#<@, @#>@, @#<=@, @#>=@).
hashLineComment :: Parser ()
hashLineComment = try $ do
  char '#'
  notFollowedBy (oneOf "=!<>")
  void $ manyTill anySingle (void eol <|> eof)

sc :: Parser ()
sc = L.space space1 hashLineComment empty

lexeme :: Parser a -> Parser a
lexeme p = do
  value <- p
  end <- getOffset
  St.modify (\env -> env {peTokenEnd = end})
  sc
  pure value

symbol :: String -> Parser String
symbol = lexeme . string

keyword :: String -> Parser ()
keyword s = void $ lexeme $ try $ string s <* notFollowedBy (alphaNumChar <|> char '_')

identChars :: Parser String
identChars = many (alphaNumChar <|> char '_')

-- ─── TERM PARSER ─────────────────────────────────────────────────────────────

-- Lower-case identifier, optionally module-qualified (@mod:name@, no spaces).
pAtomIdent :: Parser String
pAtomIdent = lexeme $ do
  c <- lowerChar
  cs <- identChars
  let name = c : cs
  qual <- optional $ try $ do
    char ':'
    notFollowedBy (char ':')
    c' <- lowerChar
    cs' <- identChars
    return (c' : cs')
  return $ maybe name (\q -> name ++ ":" ++ q) qual

-- Plain identifier without module qualification (used in declarations).
pPlainIdent :: Parser String
pPlainIdent = lexeme $ do
  c <- lowerChar
  cs <- identChars
  return (c : cs)

-- Variables start with an upper-case letter or an underscore.  A lone @_@ is
-- anonymous (fresh on every occurrence).
pVar :: Parser Term
pVar = do
  name <- lexeme $ do
    c <- upperChar <|> char '_'
    cs <- identChars
    return (c : cs)
  if name == "_" then freshVar else namedVar name

pNumber :: Parser Term
pNumber = lexeme $ do
  neg <- option False (True <$ char '-')
  choice
    [ try $ do
        whole <- some digitChar
        char '.'
        frac <- some digitChar
        let d = read (whole ++ "." ++ frac) :: Double
        return $ FloatLit (if neg then negate d else d),
      do
        digits <- some digitChar
        let n = read digits :: Integer
        return $ IntLit (if neg then negate n else n)
    ]

pCharLit :: Parser Term
pCharLit = lexeme $ do
  char '\''
  c <- L.charLiteral
  char '\''
  return (CharLit c)

pStrLit :: Parser Term
pStrLit = lexeme $ do
  char '"'
  cs <- manyTill L.charLiteral (char '"')
  return (StrLit cs)

pList :: Parser Term
pList = do
  symbol "["
  choice
    [ symbol "]" >> return nil,
      do
        first <- pExpr
        rest <- many (symbol "," *> pExpr)
        tl <- optional (symbol "|" *> pExpr)
        symbol "]"
        return (mkList (first : rest) tl)
    ]

pParens :: Parser Term
pParens = between (symbol "(") (symbol ")") pControl

-- | @{ Goal }@: an embedded goal inside a DCG body.
pBraces :: Parser Term
pBraces = do
  g <- between (symbol "{") (symbol "}") pControl
  return (Compound "{}" [g])

pCut :: Parser Term
pCut = Atom "!" <$ try (symbol "!" <* notFollowedBy (char '='))

pAtomicTerm :: Parser Term
pAtomicTerm =
  choice
    [ try pNumber,
      pCharLit,
      pStrLit,
      pList,
      pParens,
      pBraces,
      pCut,
      try pCompound,
      pVar,
      Atom <$> pAtomIdent
    ]

pCompound :: Parser Term
pCompound = do
  f <- pAtomIdent
  args <- some pArgTerm
  return (Compound f args)

pArgTerm :: Parser Term
pArgTerm =
  choice
    [ try pNumber,
      pCharLit,
      pStrLit,
      pList,
      pParens,
      pBraces,
      pVar,
      Atom <$> pAtomIdent
    ]

-- | Term-level expression (no control operators).
pExpr :: Parser Term
pExpr = makeExprParser pAtomicTerm operatorTable

-- | Control-level expression: adds @,@ @->@ and @;@ (used inside parentheses
-- and in clause bodies).
pControl :: Parser Term
pControl = makeExprParser pExpr controlTable

binOp :: String -> Term -> Term -> Term
binOp name l r = Compound name [l, r]

operatorTable :: [[Operator Parser Term]]
operatorTable =
  [ [InfixR $ binOp "^" <$ try (symbol "^")],
    [ InfixL $ binOp "mul" <$ try (symbol "*"),
      InfixL $ binOp "div" <$ try (symbol "/"),
      InfixL $ binOp "mod" <$ try (symbol "%")
    ],
    [ InfixL $ binOp "plus" <$ try (symbol "+"),
      InfixL $ binOp "minus" <$ try (symbol "-" <* notFollowedBy (char '>'))
    ],
    [InfixR $ binOp "cons" <$ try (symbol "::")],
    [InfixN $ binOp "range" <$ try (symbol "..")],
    [InfixN $ binOp "access" <$ try (char '.' *> lookAhead (letterChar <|> char '_'))],
    [ InfixN $ binOp "fd_ge" <$ try (symbol "#>="),
      InfixN $ binOp "fd_le" <$ try (symbol "#<="),
      InfixN $ binOp "fd_gt" <$ try (symbol "#>"),
      InfixN $ binOp "fd_lt" <$ try (symbol "#<"),
      InfixN $ binOp "gte" <$ try (symbol ">="),
      InfixN $ binOp "lte" <$ try (symbol "<=" <* notFollowedBy (char '>')),
      InfixN $ binOp "gt" <$ try (symbol ">" <* notFollowedBy (oneOf "=-")),
      InfixN $ binOp "lt" <$ try (symbol "<" <* notFollowedBy (oneOf "=-"))
    ],
    [ InfixN $ binOp "int_eq" <$ try (symbol "#="),
      InfixN $ binOp "fd_ne" <$ try (symbol "#!="),
      InfixN $ binOp "equiv" <$ try (symbol "=="),
      InfixN $ binOp "neq" <$ try (symbol "!="),
      InfixN $ binOp "unify" <$ try (symbol "=" <* notFollowedBy (oneOf "=>")),
      InfixN $ binOp "is" <$ keyword "is",
      InfixN $ binOp "in" <$ keyword "in"
    ]
  ]

controlTable :: [[Operator Parser Term]]
controlTable =
  [ [InfixR $ binOp "," <$ try (symbol ",")],
    [InfixR $ binOp "->" <$ try (symbol "->")],
    [InfixR $ binOp ";" <$ try (symbol ";")]
  ]

-- | Flatten a top-level conjunction into a goal list.
flattenConj :: Term -> [Term]
flattenConj (Compound "," [a, b]) = flattenConj a ++ flattenConj b
flattenConj t = [t]

pGoals :: Parser [Term]
pGoals = flattenConj <$> pControl

-- ─── CLAUSES ─────────────────────────────────────────────────────────────────

pClause :: Parser Clause
pClause = do
  hd <- pExpr
  choice
    [ do
        symbol "->"
        body <- pControl
        symbol "."
        env <- St.get
        let (hd', goals, n') = desugarDCG (peNext env) hd body
        return (Clause hd' goals n'),
      do
        symbol "<-"
        body <- pGoals
        symbol "."
        finish (hd, body),
      do
        symbol "."
        finish (hd, [])
    ]
  where
    finish :: (Term, [Term]) -> Parser Clause
    finish (h, b) = do
      env <- St.get
      return (Clause h b (peNext env))

-- | DCG translation.  @desugarDCG n head body@ translates a grammar rule,
-- allocating fresh variables from @n@ upwards; returns the translated head,
-- the body goals and the next free variable id.
desugarDCG :: Int -> Term -> Term -> (Term, [Term], Int)
desugarDCG n0 hd body = (hd', flattenConj bodyT, nEnd)
  where
    s0 = Var n0
    (bodyT, sOut, nEnd) = translate body s0 (n0 + 1)
    hd' = addArgs hd s0 sOut

    addArgs t sa sb = case t of
      Atom f -> Compound f [sa, sb]
      Compound f args -> Compound f (args ++ [sa, sb])
      _ -> Compound "call" [t, sa, sb]

    -- translate G S0 n = (G', S, n') where G' relates S0 to S.
    translate :: Term -> Term -> Int -> (Term, Term, Int)
    translate g sIn n = case g of
      Compound "," [a, b] ->
        let (a', s1, n1) = translate a sIn n
            (b', s2, n2) = translate b s1 n1
         in (Compound "," [a', b'], s2, n2)
      Compound ";" [a, b] ->
        let (a', sa, n1) = translate a sIn n
            (b', sb, n2) = translate b sIn n1
            s = Var n2
            wrap x sx = Compound "," [x, Compound "unify" [sx, s]]
         in (Compound ";" [wrap a' sa, wrap b' sb], s, n2 + 1)
      Compound "->" [c, t] ->
        let (c', s1, n1) = translate c sIn n
            (t', s2, n2) = translate t s1 n1
         in (Compound "->" [c', t'], s2, n2)
      Atom "!" -> (Atom "!", sIn, n)
      Compound "{}" [inner] -> (inner, sIn, n)
      Atom "nil" -> (Atom "true", sIn, n)
      Compound "cons" _ ->
        let (xs, _) = unfoldCons g
            s = Var n
         in (Compound "unify" [sIn, mkList xs (Just s)], s, n + 1)
      StrLit str ->
        let s = Var n
         in (Compound "unify" [sIn, mkList (map CharLit str) (Just s)], s, n + 1)
      _ ->
        let s = Var n
         in (addArgs g sIn s, s, n + 1)

-- ─── DECLARATION PARSER ──────────────────────────────────────────────────────

pDecl :: Parser Decl
pDecl = do
  name <- pPlainIdent
  void $ lexeme (char ':' <* notFollowedBy (oneOf ":-="))
  items <- many pDeclItem
  symbol "."
  let dets = [d | DIDet d <- items]
      flags = [f | DIFlag f <- items]
      args = [a | DIArg a <- items]
  case dets of
    (_ : _ : _) -> fail "multiple determinism categories in one declaration"
    _ ->
      return
        Decl
          { declName = name,
            declDet = case dets of [d] -> Just d; _ -> Nothing,
            declFlags = flags,
            declArgs = args
          }

data DeclItem = DIDet Det | DIFlag Flag | DIArg ArgSpec

pDeclItem :: Parser DeclItem
pDeclItem =
  choice
    [ DIDet Det <$ keyword "det",
      DIDet Semidet <$ keyword "semidet",
      DIDet Multi <$ keyword "multi",
      DIDet Nondet <$ keyword "nondet",
      DIFlag FlagTable <$ keyword "table",
      DIFlag FlagNoTable <$ keyword "notable",
      DIFlag FlagIndex <$ keyword "index",
      DIFlag FlagNoIndex <$ keyword "noindex",
      DIArg <$> pArgSpec
    ]

pMode :: Parser Mode
pMode =
  choice
    [ ModeInOut <$ try (symbol "<=>"),
      ModeIn <$ try (symbol "<="),
      ModeOut <$ try (symbol "=>")
    ]

pSort :: Parser Sort
pSort =
  choice
    [ keyword "list" *> (SList <$> pSort),
      pSortAtom
    ]

pSortAtom :: Parser Sort
pSortAtom =
  choice
    [ SInt <$ keyword "int",
      SFloat <$ keyword "float",
      SNum <$ keyword "num",
      SStr <$ keyword "str",
      SChar <$ keyword "char",
      SAtom <$ keyword "atom",
      SAny <$ keyword "any",
      SAny <$ try (lexeme (char '_' <* notFollowedBy (alphaNumChar <|> char '_'))),
      between (symbol "(") (symbol ")") pSort
    ]

pArgSpec :: Parser ArgSpec
pArgSpec =
  choice
    [ ArgSpec SAny <$> pMode,
      between (symbol "(") (symbol ")") inner
    ]
  where
    inner =
      choice
        [ try $ do
            s <- pSort
            void $ lexeme (char ':')
            m <- pMode
            return (ArgSpec s m),
          (`ArgSpec` ModeInOut) <$> pSort,
          ArgSpec SAny <$> pMode
        ]

-- ─── FILES ───────────────────────────────────────────────────────────────────

pInlineQuery :: Parser Query
pInlineQuery = do
  symbol ">"
  goals <- pGoals
  symbol "." <|> symbol "?"
  finishQuery goals

finishQuery :: [Term] -> Parser Query
finishQuery goals = do
  env <- St.get
  return Query {queryGoals = goals, queryNames = peOrder env, queryNVars = peNext env}

pDirective :: Parser [Term]
pDirective = do
  symbol "<-"
  goals <- pGoals
  symbol "."
  return goals

pTopLevel :: Parser TopLevel
pTopLevel = do
  resetEnv
  choice
    [ try (TLQuery <$> pInlineQuery),
      try (TLDirective <$> pDirective),
      try (TLDecl <$> pDecl),
      TLClause <$> pClause
    ]

pFile :: Parser [TopLevel]
pFile = sc *> many pTopLevel <* eof

runP :: Parser a -> String -> Either String a
runP p input = case St.evalState (runParserT p "<input>" input) emptyEnv of
  Left err -> Left (errorBundlePretty err)
  Right x -> Right x

-- | Parse a whole file: clauses, declarations, directives and inline queries.
parseFile :: String -> Either String [TopLevel]
parseFile = runP pFile

parseLocatedFile :: FilePath -> String -> Either (SourceSpan, String) [LocatedTopLevel]
parseLocatedFile path input =
  case St.evalState (runParserT parser path input) emptyEnv of
    Right items -> Right items
    Left bundle ->
      let (l, c) = position (errorOffset (NE.head (bundleErrors bundle)))
       in Left (SourceSpan path l c l (c + 1), errorBundlePretty bundle)
  where
    parser = sc *> many located <* eof
    located = do
      start <- getOffset
      item <- pTopLevel
      env <- St.get
      let (l, c) = position start
          (el, ec) = position (peTokenEnd env)
          loc = SourceSpan path l c el ec
      pure (LocatedTopLevel loc item (peOrder env))
    -- UTF-16 columns match the LSP protocol, including supplementary Unicode
    -- characters and literal tabs (which occupy one character).
    -- Index once so locating many items does not repeatedly scan the source.
    positions = Map.fromDistinctAscList (zip [0 ..] (scanl advance (1, 1) input))
    position offset = Map.findWithDefault (1, 1) offset positions
    advance (l, _) '\n' = (l + 1, 1)
    advance (l, c) ch = (l, c + if ord ch > 0xffff then 2 else 1)

-- | Parse a program consisting only of clauses and declarations (no queries).
parseProgram :: String -> Either String [TopLevel]
parseProgram src = do
  items <- parseFile src
  case [q | TLQuery q <- items] of
    [] -> Right items
    _ -> Left "unexpected inline query in program text"

-- | Parse a query (comma-separated goals, optional trailing @?@ or @.@).
parseQuery :: String -> Either String Query
parseQuery = runP $ do
  sc
  resetEnv
  goals <- pGoals
  optional (symbol "?" <|> symbol ".")
  eof
  finishQuery goals

-- | Parse a single term (control operators allowed inside parentheses).
parseTerm :: String -> Either String Term
parseTerm = runP (sc *> resetEnv *> pExpr <* eof)

-- | Parse clause text (one or more clauses / declarations) as typed at the REPL.
parseClauseText :: String -> Either String [TopLevel]
parseClauseText =
  runP (sc *> many (resetEnv *> (try (TLDecl <$> pDecl) <|> (TLClause <$> pClause))) <* eof)

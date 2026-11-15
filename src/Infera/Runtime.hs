{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE ForeignFunctionInterface #-}
{-# LANGUAGE ScopedTypeVariables #-}
-- | Explicit, resource-scoped execution of effect grammars. The pure Search
-- API never performs external effects and cannot resume a consumed world.
module Infera.Runtime (runProgram, runEffectQuery) where

import qualified Control.Exception as E
import Control.Monad (unless, when, foldM, void)
import Control.Concurrent (threadDelay)
import Data.Data (Typeable)
import Data.IORef
import qualified Data.IntMap.Strict as IM
import qualified Data.Map.Strict as Map
import Data.List (intercalate, nub)
import Data.Unique (newUnique, hashUnique)
import Foreign.C.Types
import qualified Data.ByteString as BS
import GHC.Clock (getMonotonicTimeNSec)
import qualified Network.Socket as N
import qualified Network.Socket.ByteString as NB
import qualified System.Directory as D
import System.Environment (lookupEnv)
import System.Exit (exitWith, ExitCode(..))
import qualified System.IO as H
import System.IO.Error
import qualified System.Posix.IO as PIO
import System.Posix.Types (Fd(..))
import Data.Time.Clock.POSIX (getPOSIXTime)
import Infera.Syntax
import Infera.Program
import Infera.Module (loadRunnable)
import Infera.Error
import qualified Infera.Engine.Reference as R
import qualified Infera.Core as Core
import Infera.AttributeSupport (usesAttributes)
import Infera.CLP
import Infera.Unify
import Infera.Effects
import Infera.Machine.Trace.Types

foreign import ccall unsafe "infera_poll_read" pollRead :: CInt -> IO CInt

data Failure = Fault SolveError Term [String] | Halt Int | InputFailure deriving (Show,Typeable)
instance E.Exception Failure

data Object = Stream H.Handle | SocketStream N.Socket H.Handle | Listener N.Socket | Datagram N.Socket
  | Memory (IORef String) (IORef Int) (Maybe Term)
data Resource = Resource Object Bool
data Runner = Runner { program :: Program, resources :: IORef (IM.IntMap Resource),
  serial :: Int, world :: IORef Int, nextHandle :: IORef Int,
  parseCaches :: IORef (IM.IntMap (IORef (IM.IntMap Char, Bool, Int))),
  positions :: IORef (IM.IntMap Int), parseBudget :: IORef Int,
  -- | No attributes and no dynamic predicates: pure goals can run on the
  -- Core engine ('pureSearch') and no attribute hooks are ever pending.
  coreEligible :: Bool }

type State = R.SolverState

runProgram :: FilePath -> [String] -> IO ()
runProgram file args = do
  loaded <- loadRunnable file
  case loaded of
    Left err -> H.hPutStrLn H.stderr ("Fault: load-error\n" ++ err) >> exitWith (ExitFailure 2)
    Right p -> do
      result <- E.bracket (newRunner p) cleanup $ \r -> E.try $ (do
        let w = worldTerm r 0
            goal = Compound "main" [mkList (map StrLit args) Nothing,w,Var 0]
        unless (nameHasFlag p "main" FlagIo) (fault goal [] (UserError "main must be declared io"))
        outcome <- execGoals r [] (R.initialState 1) [goal]
        pure (case outcome of Nothing -> 1; Just _ -> 0)) `E.catch` \(e::E.IOException) -> fault (Atom "main") [] (UserError (show (reason e)))
      code <- case result of
        Right n -> pure n
        Left (Halt n) -> pure n
        Left InputFailure -> pure 1
        Left (Fault err goal frames) -> do
          H.hPutStrLn H.stderr ("Fault: " ++ showSolveError err ++ "\nGoal: " ++ show goal ++ "\n" ++ intercalate "\n" frames)
          pure 2
      exitWith (if code == 0 then ExitSuccess else ExitFailure code)

-- Inline entry points accept the surface effect grammar syntax directly.
-- Ordinary logic goals are lifted into pure braces before DCG translation.
runEffectQuery :: Program -> Query -> IO (Maybe R.QuerySummary)
runEffectQuery p q
  | not(any surfaceEffect(queryGoals q)) = pure Nothing
  | otherwise = do
      result<-E.bracket(newRunner p) cleanup $ \r->E.try $ do
        let combine []=Atom "nil"
            combine [x]=x
            combine(x:xs)=Compound ","[x,combine xs]
            liftGoal t=case t of
              Compound name xs | name `elem` [",",";","->"] ->Compound name(map liftGoal xs)
              _ | surfaceEffect t -> t
                | otherwise ->Compound "{}"[t]
            n=queryNVars q
            (head',body,next)=desugarDCG n (Atom "$inline") (combine(map liftGoal(queryGoals q)))
            input=case head' of Compound _ (w:_)->w; _->Var n
            state=R.initialState next
        start<-requireBind (Atom "$inline") [] state input(worldTerm r 0)
        execGoals r [] start body
      case result of
        Right answer->pure(Just(R.summarizeSearch q (maybe [] (\s->[R.Found s]) answer)))
        Left InputFailure->pure(Just(R.summarizeSearch q []))
        Left(Halt n)->exitWith(if n==0 then ExitSuccess else ExitFailure n)
        Left(Fault err goal frames)->do
          H.hPutStrLn H.stderr("Fault: "++showSolveError err++"\nGoal: "++show goal++"\n"++intercalate "\n" frames)
          exitWith(ExitFailure 2)
  where
    surfaceEffect t=case t of
      Compound name xs | (name,length xs+2) `elem` effectKeys -> True
      Compound name xs | name `elem` [",",";","->"] ->any surfaceEffect xs
      _->case functorOf t of
        Just(name,n)->nameHasFlag p name FlagIo && maybe False(const True)(lookupPred(name,n+2)p)
        _->False

newRunner :: Program -> IO Runner
newRunner p = Runner p <$> newIORef (IM.fromList [(0,Resource (Stream H.stdin) False),(1,Resource (Stream H.stdout) False),(2,Resource (Stream H.stderr) False)])
  <*> (hashUnique <$> newUnique) <*> newIORef 0 <*> newIORef 3 <*> newIORef IM.empty <*> newIORef IM.empty <*> newIORef 0
  <*> pure (not (usesAttributes p []) && null (dynamicNames p))

-- | Solve pure goals from the runner's state. Programs without attributes or
-- dynamic predicates run on the Core engine (and its JIT): the walked goals
-- become a query over their free variables, and each answer's bindings are
-- unified back into the runner's state, with the answer's own fresh
-- variables renamed above 'R.ssFresh'. A state or answer carrying
-- constraints, attributes or residual goals cannot cross that boundary, so
-- those searches use the reference resolver from the same state; answers
-- already delivered are skipped, since both produce answers in the same order.
pureSearch :: Runner -> State -> [Term] -> R.Search
pureSearch r s goals
  | not (coreEligible r) || carriesStore s = reference
  | otherwise = answers (0 :: Int) (Core.solveQueryOrFallback (program r) query)
  where
    reference = R.solveGoals (R.mkEnv (program r)) R.maxResolutionDepth s goals
    walked = map (walkS s) goals
    vars = nub (concatMap termVarIds walked)
    n = length vars
    index = IM.fromList (zip vars [0 ..])
    query = Query (map (renameWith (\v -> Var (index IM.! v))) walked)
      [("V" ++ show i, i) | i <- [0 .. n - 1]] n
    base = R.ssFresh s
    original = IM.fromList (zip [0 ..] vars)
    back j = Var (IM.findWithDefault (base + j) j original)
    answers _ [] = []
    answers k (R.Found st : rest)
      | carriesStore st = dropFound k reference
      | otherwise = case restore st of
          Just s' -> R.Found s' : answers (k + 1) rest
          Nothing -> dropFound k reference
    answers k (item : rest) = item : answers k rest
    restore st =
      let sub = stSubst (R.ssStore st)
          values = [(Var v, renameWith back (deepWalk sub (Var i))) | (i, v) <- zip [0 ..] vars]
          fresh = maximum (base : [v + 1 | (_, t) <- values, v <- termVarIds t])
          step store (a, b) = store >>= \st' -> case storeUnify st' a b of
            Right (Just st'') -> Just st''
            _ -> Nothing
       in (\store -> s {R.ssStore = store, R.ssFresh = fresh}) <$> foldl step (Just (R.ssStore s)) values
    dropFound _ [] = []
    dropFound 0 items = items
    dropFound k (R.Found _ : rest) = dropFound (k - 1) rest
    dropFound k (_ : rest) = dropFound k rest

carriesStore :: State -> Bool
carriesStore st =
  let store = R.ssStore st
   in not (IM.null (stDomains store)) || not (null (stConstraints store))
        || not (null (R.ssResidualGoals st)) || not (Map.null (R.ssAttributes st))
        || not (Map.null (R.ssDynamic st))

renameWith :: (VarId -> Term) -> Term -> Term
renameWith f t = case t of
  Var v -> f v
  Compound name xs -> Compound name (map (renameWith f) xs)
  _ -> t

cleanup :: Runner -> IO ()
cleanup r = readIORef (resources r) >>= mapM_ (\(Resource o owned) -> when owned (ignore (closeObject o))) . IM.elems
  where ignore a = a `E.catch` \(_ :: E.IOException) -> pure ()
closeObject :: Object -> IO ()
closeObject (Stream h) = H.hClose h
closeObject (SocketStream s h) = H.hClose h `E.finally` N.close s
closeObject (Listener s) = N.close s
closeObject (Datagram s) = N.close s
closeObject (Memory _ _ _) = pure ()

fault :: Term -> [String] -> SolveError -> IO a
fault g frames e = E.throwIO (Fault e g frames)
worldTerm :: Runner -> Int -> Term
worldTerm r n = Compound "$world" [IntLit (fromIntegral (serial r)),IntLit (fromIntegral n)]
walkS :: State -> Term -> Term
walkS s = deepWalk (stSubst (R.ssStore s))
bind :: Term -> [String] -> State -> Term -> Term -> IO (Maybe State)
bind g frames s a b = case storeUnify (R.ssStore s) a b of
  Left e -> fault g frames e
  Right Nothing -> pure Nothing
  Right (Just store) -> pure (Just s {R.ssStore=store})
requireBind :: Term -> [String] -> State -> Term -> Term -> IO State
requireBind g frames s a b = bind g frames s a b >>= maybe (fault g frames (UserError "effect output does not unify")) pure

-- A maximal pure prefix is searched before the next irreversible operation.
-- Any remaining alternatives at the effect boundary violate linearity.
execGoals :: Runner -> [String] -> State -> [Term] -> IO (Maybe State)
execGoals r frames state goals = do
  ready<-if coreEligible r then pure (Just (state,False))
    else selectPure frames (Atom "$attribute_boundary") (R.solveGoals (R.mkEnv(program r)) R.maxResolutionDepth state [])
  case ready of
    Nothing->pure Nothing
    Just(_,True)->fault (Atom "$attribute_boundary") frames (UserError "attribute hook left an effect choice point")
    Just(s,False)->execReady r frames s goals

execReady :: Runner -> [String] -> State -> [Term] -> IO (Maybe State)
execReady _ _ s [] = pure (Just s)
execReady r frames s goals = do
  let (prefix,rest) = span (not . effectful r s) goals
  if not (null prefix) then do
    let answers = pureSearch r s prefix
    selected <- selectPure frames (head prefix) answers
    case selected of
      Nothing -> pure Nothing
      Just (s',more) -> do
        when more (fault (if null rest then head prefix else head rest) frames (UserError "backtracking across an effect or io return"))
        execGoals r frames s' rest
  else case goals of
    [] -> pure (Just s)
    g:gs -> do
      before <- readIORef (world r)
      result <- execOne r frames s (walkS s g)
      after <- readIORef (world r)
      case result of
        Nothing | after /= before -> fault g frames (UserError "io grammar failed after an effect")
        Nothing -> pure Nothing
        Just s' -> do
          end <- execGoals r frames s' gs
          case end of
            Nothing | after /= before -> fault g frames (UserError "io grammar failed after an effect")
            _ -> pure end

effectful :: Runner -> State -> Term -> Bool
effectful r s term = let t=walkS s term in isEffect t || case t of
  Compound "call" (callee:extra) -> case callee of
    Atom f -> effectful r s (Compound f extra)
    Compound f xs -> effectful r s (Compound f (xs++extra))
    _ -> True
  Compound f xs | f `elem` [",",";","->","once","not","findall","bagof","setof","forall"] -> any (effectful r s) xs
  _ -> case functorOf t of Just (n,_) -> nameHasFlag (program r) n FlagIo; _ -> False

selectPure :: [String] -> Term -> R.Search -> IO (Maybe (State,Bool))
selectPure frames goal items = case items of
  [] -> pure Nothing
  R.Found s:rest -> do
    -- Force at most the next answer; errors are never hidden by commitment.
    more <- hasMore rest
    pure (Just (s,more))
  R.BranchError err:_ -> fault goal frames err
  R.BranchExhausted:_ -> fault goal frames (UserError "search depth limit")
  _:rest -> selectPure frames goal rest
  where
    hasMore [] = pure False
    hasMore (R.Found _:_) = pure True
    hasMore (R.BranchError err:_) = fault goal frames err
    hasMore (R.BranchExhausted:_) = fault goal frames (UserError "search depth limit")
    hasMore (_:rest) = hasMore rest

execOne :: Runner -> [String] -> State -> Term -> IO (Maybe State)
execOne r frames s goal = case goal of
  Compound "," [a,b] -> execGoals r frames s [a,b]
  Compound ";" [Compound "->" [c,t],e] -> do
    when (effectful r s c) (fault c frames (UserError "effect in condition"))
    found <- firstPure frames c (pureSearch r s [c])
    maybe (execGoals r frames s [e]) (\s' -> execGoals r frames s' [t]) found
  Compound "->" [c,t] -> execOne r frames s (Compound ";" [Compound "->" [c,t],Atom "fail"])
  Compound ";" [a,b] -> do
    n <- readIORef (world r)
    x <- execGoals r frames s [a]
    m <- readIORef (world r)
    case x of
      Just _ -> fault goal frames (UserError "an io disjunction can leave a choice point; use if-then-else")
      Nothing | n /= m -> fault goal frames (UserError "backtracking across an effect")
      Nothing -> execGoals r frames s [b]
  Compound f xs | (f,length xs) `elem` effectKeys -> perform r frames s f xs
  Compound "call" (callee:extra) -> case callee of
    Atom f -> execOne r frames s (Compound f extra)
    Compound f as -> execOne r frames s (Compound f (as++extra))
    _ -> fault goal frames (InstantiationError goal)
  _ -> case functorOf goal >>= (`lookupPred` program r) of
    Nothing -> fault goal frames (maybe (TypeError "callable" goal) UnknownPredicate (functorOf goal))
    Just p -> tryClauses (zip [0..] (IM.elems (predClauses p)))
      where
        tryClauses [] = pure Nothing
        tryClauses ((ordinal,cl):rest) = do
          let base=R.ssFresh s
              renamed=renameTerm base (clauseHead cl)
              source=lookupClauseSource (progSources (program r)) (predKey p) ordinal
              frame=showPredKey (predKey p) ++ maybe "" ((" at "++) . renderSourceSpan . sourceClauseSpan) source
          matched <- bind goal frames s {R.ssFresh=base+clauseNVars cl} goal renamed
          case matched of
            Nothing -> tryClauses rest
            Just s' -> do
              n <- readIORef (world r)
              result <- execGoals r (frame:frames) s' (map (renameBody base) (clauseBody cl))
              m <- readIORef (world r)
              case result of
                Just _ -> pure result
                Nothing | n /= m -> fault goal (frame:frames) (UserError "io grammar failed after an effect")
                Nothing -> tryClauses rest

firstPure :: [String] -> Term -> R.Search -> IO (Maybe State)
firstPure frames g xs = case xs of
  [] -> pure Nothing
  R.Found s:_ -> pure (Just s)
  R.BranchError e:_ -> fault g frames e
  R.BranchExhausted:_ -> fault g frames (UserError "search depth limit")
  _:rest -> firstPure frames g rest

-- Every effect consumes precisely the current world and produces its successor.
perform :: Runner -> [String] -> State -> String -> [Term] -> IO (Maybe State)
perform r frames s name args = do
  let (inputs,tokens)=splitAt (length args-2) args
      goal=Compound name args
  case tokens of
    [w0,w1] -> do
      n <- readIORef (world r)
      unless (walkS s w0 == worldTerm r n) (fault goal frames (UserError "world was reused or is not current"))
      case walk (stSubst (R.ssStore s)) w1 of
        Var _ -> pure ()
        _ -> fault goal frames (UserError "effect output world must be fresh")
      s' <- requireBind goal frames s w1 (worldTerm r (n+1))
      writeIORef (world r) (n+1)
      outcome <- action r frames s' goal name (map (walkS s') inputs)
      pure (Just outcome)
    _ -> fault goal frames (UserError "invalid effect arity")

atom :: Term -> [String] -> Term -> IO String
atom g f (Atom x) = pure x
atom g f x = fault g f (TypeError "atom" x)
text :: Term -> [String] -> Term -> IO String
text _ _ (StrLit x) = pure x
text g f x = fault g f (TypeError "string" x)
integer :: Term -> [String] -> Term -> IO Int
integer _ _ (IntLit n) | n >= 0, n <= fromIntegral (maxBound::Int) = pure (fromInteger n)
integer g f x = fault g f (TypeError "nonnegative bounded integer" x)

handleTerm :: Runner -> Int -> Term
handleTerm r n = Compound "$handle" [IntLit (fromIntegral (serial r)),IntLit (fromIntegral n)]
handleId :: Runner -> Term -> [String] -> Term -> IO Int
handleId _ _ _ (Atom "stdin") = pure 0
handleId _ _ _ (Atom "stdout") = pure 1
handleId _ _ _ (Atom "stderr") = pure 2
handleId r g f (Compound "$handle" [IntLit session,IntLit n]) | session == fromIntegral (serial r), n>=0, n<=fromIntegral(maxBound::Int) = pure (fromInteger n)
handleId _ g f x = fault g f (TypeError "live handle" x)
object :: Runner -> Term -> [String] -> Term -> IO (Int,Resource)
object r g f h = do
  k <- handleId r g f h
  rs <- readIORef (resources r)
  maybe (fault g f (UserError "closed or invalid handle")) (pure . (,) k) (IM.lookup k rs)
register :: Runner -> Object -> IO Term
register r obj = do
  k <- atomicModifyIORef' (nextHandle r) (\n -> (n+1,n))
  modifyIORef' (resources r) (IM.insert k (Resource obj True))
  pure (handleTerm r k)

reason :: E.IOException -> Term
reason e = Atom $ if isDoesNotExistError e then "enoent" else if isPermissionError e then "eacces"
  else if isAlreadyExistsError e then "eexist" else if isEOFError e then "eof"
  else if "Connection refused" `contains` show e then "econnrefused"
  else if "Address already in use" `contains` show e then "eaddrinuse"
  else if "timed out" `contains` show e then "etimedout" else "eio"
  where contains needle hay = any (\xs -> take (length needle) xs == needle) (tails hay)
        tails []=[[]]; tails xs@(_:ys)=xs:tails ys
attempt :: IO Term -> IO Term
attempt a = (Compound "ok" . (:[]) <$> a) `E.catch` \(e::E.IOException) -> pure (Compound "err" [reason e])
unitAttempt :: IO () -> IO Term
unitAttempt a = (a >> pure (Atom "ok")) `E.catch` \(e::E.IOException) -> pure (Compound "err" [reason e])

modeOf :: Term -> [String] -> Term -> IO (H.IOMode,Bool)
modeOf g f (Compound "binary" [m]) = do (mode,_) <- modeOf g f m; pure (mode,True)
modeOf _ _ (Atom "read") = pure (H.ReadMode,False)
modeOf _ _ (Atom "write") = pure (H.WriteMode,False)
modeOf _ _ (Atom "append") = pure (H.AppendMode,False)
modeOf _ _ (Atom "update") = pure (H.ReadWriteMode,False)
modeOf g f t = fault g f (TypeError "read/write/append/update mode" t)

openObject :: Runner -> Term -> [String] -> Term -> Term -> IO Term
openObject r g f address mode = do
  (m,binary) <- modeOf g f mode
  let setup h = H.hSetBinaryMode h binary >> unless binary (H.hSetEncoding h H.utf8) >> pure h
      connectAddr addr = do
        s <- N.socket (family addr) (kind addr) N.defaultProtocol
        (N.connect s addr >> socketStream s) `E.onException` N.close s
      family (N.SockAddrUnix _) = N.AF_UNIX
      family (N.SockAddrInet _ _) = N.AF_INET
      family _ = N.AF_INET6
      kind _ = N.Stream
      socketStream sock = do
        -- Duplicate the descriptor, retaining the Socket for readiness and
        -- ownership. Never operate on a Socket consumed by socketToHandle.
        fd <- N.withFdSocket sock (PIO.dup . Fd)
        h <- PIO.fdToHandle fd >>= setup
        register r (SocketStream sock h)
      hostPort host port passive = do
        h <- text g f host
        n <- integer g f port
        when (n>65535) (fault g f (TypeError "port 0..65535" port))
        as <- N.getAddrInfo (Just N.defaultHints {N.addrSocketType=N.Stream,N.addrFlags=[N.AI_PASSIVE | passive]}) (if null h then Nothing else Just h) (Just (show n))
        case as of a:_ -> pure (N.addrAddress a); [] -> E.ioError (userError "address resolution failed")
      listenAddr addr = do
        sock <- N.socket (family addr) N.Stream N.defaultProtocol
        (N.setSocketOption sock N.ReuseAddr 1 >> N.bind sock addr >> N.listen sock 128 >> register r (Listener sock)) `E.onException` N.close sock
  case address of
    Atom n | n `elem` ["stdin","stdout","stderr"] -> pure (Atom n)
    Compound "file" [path] -> text g f path >>= \p -> E.bracketOnError (H.openFile p m) H.hClose (\h -> setup h >>= register r . Stream)
    Compound "string" [initial] -> do
      value <- case initial of Var _ | m==H.WriteMode -> pure ""; _ -> text g f initial
      buf <- newIORef (if m==H.WriteMode then "" else value)
      pos <- newIORef (if m==H.AppendMode then length value else 0)
      register r (Memory buf pos (case initial of Var _ -> Just initial; _ -> Nothing))
    Compound "tcp" [host,port] -> hostPort host port False >>= connectAddr
    Compound "unix" [path] -> text g f path >>= connectAddr . N.SockAddrUnix
    Compound "listen" [port] -> hostPort (StrLit "") port True >>= listenAddr
    Compound "listen" [host,port] -> hostPort host port True >>= listenAddr
    Compound "listen" [Compound "unix" [path]] -> text g f path >>= listenAddr . N.SockAddrUnix
    Compound "udp" [port] -> do
      n <- integer g f port
      when (n>65535) (fault g f (TypeError "port 0..65535" port))
      sock <- N.socket N.AF_INET N.Datagram N.defaultProtocol
      (N.bind sock (N.SockAddrInet (fromIntegral n) (N.tupleToHostAddress (0,0,0,0))) >> register r (Datagram sock)) `E.onException` N.close sock
    _ -> fault g f (TypeError "handle address" address)

readChar :: Term -> [String] -> Object -> IO (Maybe Char)
readChar g f (Memory buf pos _) = do
  n<-readIORef pos; xs<-readIORef buf
  case drop n xs of []->pure Nothing; c:_->writeIORef pos (n+1)>>pure(Just c)
readChar g f obj = do
  h <- streamHandle g f obj
  (Just <$> H.hGetChar h) `E.catch` \(e::E.IOException) -> if isEOFError e then pure Nothing else E.throwIO e
streamHandle :: Term -> [String] -> Object -> IO H.Handle
streamHandle _ _ (Stream h)=pure h
streamHandle _ _ (SocketStream _ h)=pure h
streamHandle g f _=fault g f (TypeError "text/byte stream" g)
readChars :: Term -> [String] -> Object -> Int -> IO String
readChars _ _ _ 0 = pure ""
readChars g f o n = readChar g f o >>= maybe (pure "") (\c -> (c:) <$> readChars g f o (n-1))
-- Direct reads share the parser's cached read-ahead and committed cursor.
logicalChar :: Runner -> Term -> [String] -> Int -> Object -> IO (Maybe Char)
logicalChar r g f key obj = do
  caches<-readIORef(parseCaches r)
  case IM.lookup key caches of
    Nothing->readChar g f obj
    Just cache->do
      pos<-IM.findWithDefault 0 key <$> readIORef(positions r)
      (known,eof,count)<-readIORef cache
      let advance c=modifyIORef'(positions r)(IM.insert key(pos+1))>>pure(Just c)
      case IM.lookup pos known of
        Just c->advance c
        Nothing | eof->pure Nothing
        Nothing->do
          c<-readChar g f obj
          case c of
            Nothing->writeIORef cache(known,True,count)>>pure Nothing
            Just ch->writeIORef cache(IM.insert pos ch known,False,pos+1)>>advance ch

charsUsing :: IO (Maybe Char) -> Int -> IO String
charsUsing _ 0=pure ""
charsUsing reader n=reader >>= maybe(pure "")(\c->(c:) <$> charsUsing reader(n-1))
lineUsing :: IO (Maybe Char) -> IO (Maybe String)
lineUsing reader=reader >>= maybe(pure Nothing)(\c->if c=='\n' then pure(Just "") else Just . (c:) . maybe "" id <$> lineUsing reader)

writeText :: Term -> [String] -> Object -> String -> IO ()
writeText _ _ (Memory buf pos _) xs = do
  n<-readIORef pos; old<-readIORef buf
  writeIORef buf (take n old ++ xs ++ drop (n+length xs) old)
  writeIORef pos (n+length xs)
writeText g f obj xs = streamHandle g f obj >>= \h -> H.hPutStr h xs >> H.hFlush h
bytes :: Term -> [String] -> Term -> IO BS.ByteString
bytes g f t = case unfoldCons t of
  (xs,Nothing) -> BS.pack <$> mapM one xs
  _ -> fault g f (TypeError "byte list" t)
  where one (IntLit n) | n>=0,n<=255 = pure(fromInteger n)
        one x = fault g f (TypeError "byte 0..255" x)
byteTerm :: BS.ByteString -> Term
byteTerm = flip mkList Nothing . map (IntLit . fromIntegral) . BS.unpack

renderGrammar :: Runner -> Term -> [String] -> State -> Term -> IO (String,State)
renderGrammar _ _ _ s (StrLit xs)=pure(xs,s)
renderGrammar r g f s nt = do
  let v=R.ssFresh s; target=Var v
      goal=case nt of Atom n->Compound n [target,nil]; Compound n as->Compound n (as++[target,nil]); _->Compound "call" [nt,target,nil]
  found<-firstPure f g (pureSearch r s {R.ssFresh=v+1} [goal])
  case found of
    Nothing->fault g f (UserError "text grammar failed")
    Just s'->case unfoldCons(walkS s' target) of
      (xs,Nothing) | all isChar xs -> pure([c | CharLit c<-xs],s')
      _ ->fault g f (TypeError "character-list grammar" nt)
  where isChar(CharLit _)=True; isChar _=False

ready :: Term -> [String] -> Object -> IO Bool
ready _ _ (Memory _ _ _)=pure True
ready _ _ (Listener sock)=N.withFdSocket sock (fmap (/=0) . pollRead)
ready _ _ (Datagram sock)=N.withFdSocket sock (fmap (/=0) . pollRead)
ready g f obj=streamHandle g f obj >>= \h -> H.hWaitForInput h 0 `E.catch` \(e::E.IOException) -> if isEOFError e then pure True else E.throwIO e

-- Result-bearing operations return expected environmental failures as values.
action :: Runner -> [String] -> State -> Term -> String -> [Term] -> IO State
action r f s g name args = case (name,args) of
  ("open",[address,mode,out]) -> attempt (openObject r g f address mode) >>= outBind out
  ("close",[h]) -> do
    (k,Resource obj owned)<-object r g f h
    unless owned (fault g f (UserError "process streams remain open"))
    closeObject obj
    modifyIORef' (resources r) (IM.delete k)
    modifyIORef' (parseCaches r) (IM.delete k)
    modifyIORef' (positions r) (IM.delete k)
    case obj of
      Memory buf _ (Just target) -> readIORef buf >>= outBind target . StrLit
      _ -> pure s
  ("read_line",[h,out]) -> do
    (key,Resource obj _)<-object r g f h
    value <- (lineUsing (logicalChar r g f key obj) >>= pure . maybe (Atom "eof") (Compound "ok" . (:[]) . StrLit)) `E.catch` \(e::E.IOException)->pure(Compound "err"[reason e])
    outBind out value
  ("read_chars",[h,count,out]) -> do
    n<-integer g f count; (key,Resource obj _)<-object r g f h
    value<-attempt (StrLit <$> charsUsing (logicalChar r g f key obj) n)
    outBind out (if n>0 && value==Compound "ok"[StrLit ""] then Atom "eof" else value)
  ("read_bytes",[h,count,out]) -> do
    n<-integer g f count; (_,Resource obj _)<-object r g f h
    value<-attempt $ case obj of
      Memory{} -> byteTerm . BS.pack . map (fromIntegral . fromEnum) <$> readChars g f obj n
      _ -> streamHandle g f obj >>= fmap byteTerm . flip BS.hGet n
    outBind out (if n>0 && value==Compound "ok"[nil] then Atom "eof" else value)
  ("write",[h,t,out]) -> do
    xs<-text g f t; (_,Resource obj _)<-object r g f h
    unitAttempt (writeText g f obj xs) >>= outBind out
  ("write_bytes",[h,t,out]) -> do
    bs<-bytes g f t; (_,Resource obj _)<-object r g f h
    result<-unitAttempt $ case obj of
      Memory{} -> writeText g f obj (map (toEnum . fromIntegral) (BS.unpack bs))
      _ -> streamHandle g f obj >>= \h' -> BS.hPut h' bs >> H.hFlush h'
    outBind out result
  ("say",[nt]) -> say (Atom "stdout") nt Nothing
  ("say",[nt,out]) -> say (Atom "stdout") nt (Just out)
  ("say_to",[h,nt]) -> say h nt Nothing
  ("say_to",[h,nt,out]) -> say h nt (Just out)
  ("phrase_from",[h,nt]) -> parseHandle r f s g h nt
  ("phrase_from_file",[nt,path]) -> do
    result<-attempt(openObject r g f (Compound "file"[path]) (Atom "read"))
    case result of
      Compound "ok"[h]->do
        (key,Resource obj _)<-object r g f h
        parseHandleWith True r f s g h nt `E.finally` (closeObject obj >> modifyIORef'(resources r)(IM.delete key))
      _->fault g f(UserError("unchecked input failure: "++show result++"; use open to handle environmental errors"))
  ("accept",[h,out]) -> do
    (_,Resource obj _)<-object r g f h
    case obj of
      Listener sock -> attempt (do
        (peer,_)<-N.accept sock
        (do fd<-N.withFdSocket peer (PIO.dup . Fd); handle<-PIO.fdToHandle fd
            H.hSetEncoding handle H.utf8
            register r (SocketStream peer handle)) `E.onException` N.close peer) >>= outBind out
      _ -> fault g f (TypeError "listening handle" h)
  ("handle_address",[h,out]) -> do
    (_,Resource obj _)<-object r g f h
    let socket = case obj of SocketStream sk _->Just sk; Listener sk->Just sk; Datagram sk->Just sk; _->Nothing
    case socket of
      Nothing->fault g f (TypeError "socket handle" h)
      Just sk->do
        addr<-N.getSocketName sk
        let value=case (obj,addressTerm addr) of
              (Datagram _,x)->x
              (_,Compound "udp" xs)->Compound "tcp" xs
              (_,x)->x
        outBind out value
  ("wait",[hs,t,out]) -> do
    timeout<-integer g f t
    handles<-case unfoldCons hs of (xs,Nothing)->pure xs; _->fault g f(TypeError "handle list" hs)
    objects<-mapM (object r g f) handles
    start<-getMonotonicTimeNSec
    let loop=do
          flags<-mapM (\(key,Resource o _)->do
            caches<-readIORef(parseCaches r)
            pos<-IM.findWithDefault 0 key <$> readIORef(positions r)
            buffered<-case IM.lookup key caches of Nothing->pure False; Just c->do (_,eof,count)<-readIORef c; pure(eof || pos<count)
            if buffered then pure True else ready g f o) objects
          now<-getMonotonicTimeNSec
          let available=[h | (h,True)<-zip handles flags]
          if not(null available) || now-start >= fromIntegral timeout*1000000 then pure available else threadDelay 1000>>loop
    loop >>= outBind out . flip mkList Nothing
  ("send_to",[h,address,payload,out]) -> do
    (_,Resource obj _)<-object r g f h; bs<-bytes g f payload
    case obj of
      Datagram sock -> do
        addr<-udpAddress g f address
        unitAttempt (void(NB.sendTo sock bs addr)) >>= outBind out
      _->fault g f(TypeError "datagram handle" h)
  ("recv_from",[h,count,out]) -> do
    n<-integer g f count; (_,Resource obj _)<-object r g f h
    case obj of
      Datagram sock -> attempt (do (bs,addr)<-NB.recvFrom sock n; pure(Compound "packet"[addressTerm addr,byteTerm bs])) >>= outBind out
      _->fault g f(TypeError "datagram handle" h)
  ("getenv",[key,out]) -> do
    k<-text g f key; v<-lookupEnv k
    outBind out (maybe (Compound "err"[Atom "enoent"]) (Compound "ok" . (:[]) . StrLit) v)
  ("now",[out]) -> getPOSIXTime >>= outBind out . FloatLit . realToFrac
  ("monotonic",[out]) -> getMonotonicTimeNSec >>= outBind out . IntLit . fromIntegral
  ("sleep",[ms]) -> integer g f ms >>= \n -> threadDelay (min (maxBound `div` 1000) n*1000) >> pure s
  ("random_seed",[out]) -> getMonotonicTimeNSec >>= outBind out . IntLit . fromIntegral
  ("list_dir",[path,out]) -> text g f path >>= \p -> attempt (flip mkList Nothing . map StrLit <$> D.listDirectory p) >>= outBind out
  ("stat",[path,out]) -> do
    p<-text g f path
    attempt (do directory<-D.doesDirectoryExist p; exists<-D.doesPathExist p
                unless exists (E.ioError (mkIOError doesNotExistErrorType "stat" Nothing (Just p)))
                size<-if directory then pure 0 else D.getFileSize p
                pure(Compound "stat"[Atom(if directory then "directory" else "file"),IntLit size])) >>= outBind out
  ("remove",[path,out]) -> text g f path >>= \p -> unitAttempt (D.removeFile p) >>= outBind out
  ("rename",[a,b,out]) -> do x<-text g f a; y<-text g f b; unitAttempt(D.renamePath x y)>>=outBind out
  ("make_dir",[path,out]) -> text g f path >>= \p -> unitAttempt (D.createDirectory p) >>= outBind out
  ("halt",[n]) -> integer g f n >>= E.throwIO . Halt
  _ -> fault g f (UnknownPredicate(name,length args))
  where
    outBind= requireBind g f s
    say h nt out=do
      (xs,s')<-renderGrammar r g f s nt
      (_,Resource obj _)<-object r g f h
      result<-unitAttempt(writeText g f obj xs)
      case out of
        Just target->requireBind g f s' target result
        Nothing->if result==Atom "ok" then pure s' else fault g f (UserError("unchecked output failure: "++show result++"; use the result-bearing say form"))

addressTerm :: N.SockAddr -> Term
addressTerm (N.SockAddrInet port host)=let(a,b,c,d)=N.hostAddressToTuple host in Compound "udp"[StrLit(intercalate "."(map show[a,b,c,d])),IntLit(fromIntegral port)]
addressTerm (N.SockAddrUnix path)=Compound "unix"[StrLit path]
addressTerm other=StrLit(show other)
udpAddress :: Term -> [String] -> Term -> IO N.SockAddr
udpAddress g f (Compound "udp"[host,port])=do
  h<-text g f host; n<-integer g f port
  when(n>65535)(fault g f(TypeError "port 0..65535" port))
  as<-N.getAddrInfo (Just N.defaultHints{N.addrSocketType=N.Datagram,N.addrFamily=N.AF_INET}) (Just h)(Just(show n))
  case as of a:_->pure(N.addrAddress a); _->E.ioError(userError "address resolution failed")
udpAddress g f t=fault g f(TypeError "udp host port" t)

-- Implemented below: the parser keeps read-ahead in a handle-owned cache so
-- grammar alternatives can rewind without repeating external reads.
parseHandle :: Runner -> [String] -> State -> Term -> Term -> Term -> IO State
parseHandle = parseHandleWith False

parseHandleWith :: Bool -> Runner -> [String] -> State -> Term -> Term -> Term -> IO State
parseHandleWith complete r f s g h nt = do
  writeIORef (parseBudget r) 0
  (key,Resource obj _)<-object r g f h
  caches<-readIORef(parseCaches r)
  cache<-case IM.lookup key caches of
    Just c->pure c
    Nothing->do c<-newIORef(IM.empty,False,0); modifyIORef'(parseCaches r)(IM.insert key c); pure c
  pos<-IM.findWithDefault 0 key <$> readIORef(positions r)
  let input=Compound "$input"[IntLit(fromIntegral key),IntLit(fromIntegral pos)]
      out=if complete then nil else Var(R.ssFresh s)
      target=case nt of Atom n->Compound n[input,out]; Compound n as->Compound n(as++[input,out]); _->Compound "call"[nt,input,out]
      state=s{R.ssFresh=R.ssFresh s+1}
  result<-parseGoals r f key obj cache state [target] (pure . Just)
  case result of
    Nothing->E.throwIO InputFailure
    Just found->do
      let force n=do
            (known,eof,count)<-readIORef cache
            case IM.lookup n known of
              Just c->(c:) <$> force(n+1)
              Nothing | eof->pure []
              Nothing->do
                c<-readChar g f obj
                case c of
                  Nothing->writeIORef cache(known,True,count)>>pure []
                  Just ch->writeIORef cache(IM.insert n ch known,False,count+1)>>force n
          materialize term=case term of
            Compound "$input"[IntLit k,IntLit n] | k==fromIntegral key -> mkList . map CharLit <$> force(fromInteger n) <*> pure Nothing
            Compound name xs->Compound name <$> mapM materialize xs
            _->pure term
      values<-mapM (\v->do t<-materialize(walkS found(Var v)); pure(v,t)) (termVarIds nt)
      let done=found{R.ssStore=(R.ssStore found){stSubst=foldr (uncurry IM.insert) (stSubst(R.ssStore found)) values}}
      end<-case walkS done out of
        Compound "$input"[IntLit k,IntLit n] | k==fromIntegral key ->pure(fromInteger n)
        Atom "nil" -> do _<-force pos; (_,_,n)<-readIORef cache; pure n
        _->fault g f(TypeError "grammar stream remainder" (walkS done out))
      modifyIORef'(positions r)(IM.insert key end)
      modifyIORef' cache (\(known,eof,n)->(IM.filterWithKey (\k _->k>=end) known,eof,n))
      pure done

-- CPS depth-first parsing, with an immutable substitution per alternative.
-- Only head/list unification asks the stream for another character.
parseGoals :: Runner -> [String] -> Int -> Object -> IORef(IM.IntMap Char,Bool,Int) -> State -> [Term] -> (State -> IO(Maybe State)) -> IO(Maybe State)
parseGoals _ _ _ _ _ s [] done=done s
parseGoals r f key obj cache s (goal:goals) done = do
  used<-atomicModifyIORef' (parseBudget r) (\n->(n+1,n+1))
  when (used>R.maxResolutionDepth) (fault goal f (UserError "input grammar resolution budget exhausted"))
  let next st=parseGoals r f key obj cache st goals done
      one t cont=parseGoals r f key obj cache s [t] cont
      g=walkS s goal
      tryStates []=pure Nothing
      tryStates(R.Found st:rest)=next st >>= maybe (tryStates rest)(pure . Just)
      tryStates(R.BranchError e:_)=fault g f e
      tryStates(R.BranchExhausted:_)=fault g f(UserError "parser depth limit")
      tryStates(_:rest)=tryStates rest
  case g of
    Atom "true"->next s
    Atom "fail"->pure Nothing
    Compound ","[a,b]->parseGoals r f key obj cache s (a:b:goals) done
    Compound ";"[Compound "->"[c,t],e]->do
      found<-one c (pure . Just)
      maybe (one e next)(\st->parseGoals r f key obj cache st [t] next) found
    Compound ";"[a,b]->one a next >>= maybe (one b next)(pure . Just)
    Compound "->"[c,t]->one(Compound ";"[Compound "->"[c,t],Atom "fail"]) next
    Compound "once"[a]->one a (pure . Just) >>= maybe (pure Nothing) next
    Compound "not"[a]->one a (pure . Just) >>= maybe (next s)(const(pure Nothing))
    Compound "unify"[a,b]->streamUnify r f key obj cache s a b >>= maybe(pure Nothing) next
    Compound "seq"[xs,a,b] ->case xs of
      Var _->prefixes s [] a b xs next
      _->case unfoldCons xs of (cs,Nothing)->streamUnify r f key obj cache s a (mkList cs(Just b)) >>= maybe(pure Nothing) next; _->fault g f(TypeError "terminal list" xs)
    Compound "call"(callee:extra)->case callee of
      Atom n->one(Compound n extra) next
      Compound n as->one(Compound n(as++extra)) next
      _->fault g f(InstantiationError g)
    _ | isEffect g->fault g f(UserError "effect in text grammar")
      | Just p<-functorOf g >>= (`lookupPred` program r) ->
          let clauses []=pure Nothing
              clauses(cl:rest)=do
                let base=R.ssFresh s; st=s{R.ssFresh=base+clauseNVars cl}
                matched<-streamUnify r f key obj cache st g (renameTerm base(clauseHead cl))
                found<-maybe(pure Nothing)(\st'->parseGoals r f key obj cache st' (map(renameBody base)(clauseBody cl)) next) matched
                maybe(clauses rest)(pure . Just) found
          in clauses(IM.elems(predClauses p))
      | otherwise->tryStates(R.solveGoal(R.mkEnv(program r)) R.maxResolutionDepth s g)
  where
    prefixes st rev input output target next=do
      candidate<-streamUnify r f key obj cache st input output
      result<-case candidate of Nothing->pure Nothing; Just st'->bind goal f st' target(mkList(reverse rev)Nothing)>>=maybe(pure Nothing) next
      case result of
        Just _->pure result
        Nothing->do
          let v=R.ssFresh st; c=Var v; tail'=Var(v+1)
          matched<-streamUnify r f key obj cache st{R.ssFresh=v+2} input(cons c tail')
          maybe(pure Nothing)(\st'->prefixes st' (walkS st' c:rev) (walkS st' tail') output target next) matched

streamUnify :: Runner -> [String] -> Int -> Object -> IORef(IM.IntMap Char,Bool,Int) -> State -> Term -> Term -> IO(Maybe State)
streamUnify r f key obj cache s a0 b0 =
  let a=walk(stSubst(R.ssStore s)) a0; b=walk(stSubst(R.ssStore s)) b0
      input t=case t of Compound "$input"[IntLit k,IntLit n] | k==fromIntegral key->Just(fromInteger n); _->Nothing
      materialize n=do
        (known,eof,count)<-readIORef cache
        case IM.lookup n known of
          Just c->pure(cons(CharLit c)(Compound "$input"[IntLit(fromIntegral key),IntLit(fromIntegral(n+1))]))
          Nothing | eof->pure nil
          Nothing | n==count->do
            c<-readChar a0 f obj
            case c of
              Nothing->writeIORef cache(known,True,count)>>pure nil
              Just ch->writeIORef cache(IM.insert n ch known,False,count+1)>>materialize n
          _->fault a0 f(UserError "invalid stream offset")
  in case (a,b) of
    (Var _,_)->bind a0 f s a b
    (_,Var _)->bind a0 f s a b
    _ | a==b->pure(Just s)
      | Just n<-input a -> materialize n >>= \x->streamUnify r f key obj cache s x b
      | Just n<-input b -> materialize n >>= \x->streamUnify r f key obj cache s a x
    (Compound x xs,Compound y ys) | x==y,length xs==length ys ->foldM (\state pair->case state of Nothing->pure Nothing; Just st->uncurry(streamUnify r f key obj cache st) pair)(Just s)(zip xs ys)
    _->bind a0 f s a b

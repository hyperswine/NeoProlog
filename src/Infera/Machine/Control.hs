-- | Experimental explicit control and backtracking over the machine heap.
-- Ordinary clauses, conjunction, disjunction, cuts, opaque sub-searches and
-- unconstrained unification run here. Other builtins, tabled calls and
-- constrained calls use the reference resolver through complete immutable
-- state adapters. The production 'Infera.Engine.solveQuery' is unchanged.
--
-- Each externally visible step owns an immutable heap snapshot. Resuming a
-- checkpoint twice starts independent branches; neither a returned solver
-- state nor an earlier checkpoint contains a mutable heap view. Frames are
-- explicit tasks, but there is no last-call reuse or collector yet.
module Infera.Machine.Control
  ( Checkpoint,
    Step (..),
    start,
    startGoals,
    resume,
    solveQuery,
    solveGoals,
  )
where

import Control.Monad (when)
import Control.Monad.Except (ExceptT, runExceptT, throwError)
import Control.Monad.ST (ST, runST)
import Control.Monad.Trans.Class (lift)
import qualified Data.IntMap.Strict as IM
import Infera.Arith (normArithTerm)
import Infera.CLP (Store (..))
import Infera.Engine (Env (..), OutputEvent, Search, SearchItem (..), SolverState (..))
import qualified Infera.Engine as Reference
import qualified Infera.Engine.Contracts as Contracts
import Infera.Error
import Infera.Infer (builtinDet)
import qualified Infera.Machine.Bridge as Bridge
import qualified Infera.Machine.Heap as Heap
import Infera.Program
import Infera.Syntax
import Infera.Unify (deepWalk, renameBody, renameTerm, replaceCuts, walk)

-- Source cut owners are the same fresh-variable bases used by the reference
-- resolver. The second component is the current choice-stack barrier.
type Scopes = [(Int, Int)]

data Task
  = Run !Heap.Address !Int Scopes
  | Return !Call
  | Emit SearchItem
  | Fail

data Call = Call
  { callId :: !Int,
    callOwner :: !Int,
    callEntryDepth :: !Int,
    callKey :: !PredKey,
    callSignature :: Maybe Signature,
    callArguments :: [Heap.Address],
    callCommits :: !Bool
  }

data Branch = Branch
  { branchBindings :: !Bridge.Bindings,
    -- Native bindings live on the heap; stSubst is a cache until an adapter,
    -- callable expansion or public Found boundary exports it through Bridge.
    branchState :: !SolverState,
    branchTasks :: [Task],
    branchMarker :: Maybe Int
  }

-- A choice owns all branch state and the heap/trail checkpoint together.
-- Guards remember successful predicate returns across its clause retries;
-- success is decided before the caller's continuation is executed.
data Choice = Choice !Heap.Checkpoint !Branch Alternative

data Alternative
  = Tasks
  | ClauseRetry !Heap.Address !Int Scopes !Call [Clause]
  | ReferenceRetry Scopes Search
  | Guard !Int !PredKey (Maybe Det) !Bool
  | DeferredCut !Int Scopes
  | NativeRetry !Running

-- An opaque sub-search parks its caller's entire control state, then runs an
-- isolated choice stack on the same heap prefix. No caller cut barrier is
-- imported. Issues that may be suppressed are buffered inside this frame.
data ScopeKind
  = CallScope
  | OnceScope
  | NotScope
  | IfScope !Heap.Address (Maybe Heap.Address) !Int Scopes
  | FindScope !Heap.Address !Heap.Address !Int Scopes [Term] [OutputEvent]

data Scope = Scope
  { scopeParent :: !Running,
    scopeEntry :: !Heap.Checkpoint,
    scopeKind :: !ScopeKind,
    scopeIssues :: [SearchItem]
  }

data Phase = Seeking | Backtracking | Complete

data Running = Running
  { runningBranch :: !Branch,
    runningChoices :: [Choice],
    runningDepth :: !Int,
    runningNextId :: !Int,
    runningPhase :: !Phase,
    runningScope :: Maybe Scope
  }

data Checkpoint = Checkpoint !Env !Heap.FrozenHeap !Running

data Step = Finished | Yield SearchItem Checkpoint

type MachineM s = ExceptT Heap.HeapError (ST s)

checked :: ST s (Either Heap.HeapError a) -> MachineM s a
checked action = lift action >>= either throwError pure

-- | Start a query with the same root cut barrier and depth budget as the
-- reference query entry point.
start :: Program -> Query -> Either Heap.HeapError Checkpoint
start program query = startWith [(-1, 0)] (Reference.mkEnv program)
  Reference.maxResolutionDepth (Reference.initialState (queryNVars query))
  (map (replaceCuts (-1)) (queryGoals query))

-- | Adapter-compatible entry point for existing solver states. Bare cuts
-- keep the reference solveGoals behavior; unowned internal cut markers are
-- propagated. Resolution fuel counts predicate nesting, not machine steps.
startGoals :: Env -> Int -> SolverState -> [Term] -> Either Heap.HeapError Checkpoint
startGoals = startWith []

startWith :: Scopes -> Env -> Int -> SolverState -> [Term] -> Either Heap.HeapError Checkpoint
startWith scopes environment fuel state goals = runST $ runExceptT $ do
  heap <- lift Heap.newHeap
  bindings <- checked (Bridge.newBindings heap [0 .. ssFresh state - 1])
  synchronized <- checked (Bridge.syncState heap bindings state)
  (imported, addresses) <- checked (Bridge.importTerms heap synchronized goals)
  frozen <- lift (Heap.freezeHeap heap)
  let branch = Branch imported state [Run address fuel scopes | address <- addresses] Nothing
  pure (Checkpoint environment frozen (Running branch [] 0 0 Seeking Nothing))

-- | Run until the next search item or completion. Every mutable operation is
-- contained in this fresh ST scope; only immutable pages and control remain.
resume :: Checkpoint -> Either Heap.HeapError Step
resume (Checkpoint environment frozen running) = runST $ runExceptT $ do
  heap <- lift (Heap.thawHeap frozen)
  drive environment heap running

solveQuery :: Program -> Query -> Search
solveQuery program query = unfold (start program query)

solveGoals :: Env -> Int -> SolverState -> [Term] -> Search
solveGoals environment fuel state goals = unfold (startGoals environment fuel state goals)

unfold :: Either Heap.HeapError Checkpoint -> Search
unfold (Left err) = [BranchError (UserError ("machine heap: " ++ show err))]
unfold (Right checkpoint) = case resume checkpoint of
  Left err -> [BranchError (UserError ("machine heap: " ++ show err))]
  Right Finished -> []
  Right (Yield item next) -> item : unfold (Right next)

yield :: Env -> Heap.Heap s -> Running -> SearchItem -> MachineM s Step
yield environment heap running item = do
  frozen <- lift (Heap.freezeHeap heap)
  pure (Yield item (Checkpoint environment frozen running))

-- Scope events stay internal until their construct decides what escapes.
-- Public suspension still happens only through yield's immutable snapshot.
emit :: Env -> Heap.Heap s -> Running -> SearchItem -> MachineM s Step
emit environment heap running item = case runningScope running of
  Nothing -> yield environment heap running item
  Just scope -> scopeEvent environment heap running scope item

drive :: Env -> Heap.Heap s -> Running -> MachineM s Step
drive environment heap running = case runningPhase running of
  Complete -> finish environment heap running
  Backtracking -> backtrack environment heap running
  Seeking -> case branchTasks (runningBranch running) of
    [] -> do
      let branch = runningBranch running
      state <- case runningScope running of
        Nothing -> checked (Bridge.exportState heap (branchBindings branch) (branchState branch))
        -- Child scopes share the heap and bindings. Avoid rebuilding the
        -- whole substitution for each internal success only to reimport it.
        Just _ -> pure (branchState branch)
      emit environment heap running {runningPhase = Backtracking} (Found state)
    task : rest ->
      let branch = (runningBranch running) {branchTasks = rest}
          next = running {runningBranch = branch}
       in case task of
            Run address fuel scopes -> runGoal environment heap next address fuel scopes
            Return call -> returnCall environment heap next call
            Emit item -> emit environment heap next item
            Fail -> drive environment heap next {runningPhase = Backtracking}

push :: Choice -> Running -> MachineM s Running
push choice running = do
  when (runningDepth running == maxBound) (throwError Heap.HeapCapacityExceeded)
  pure running
    { runningChoices = choice : runningChoices running,
      runningDepth = runningDepth running + 1
    }

-- Clamp still-active continuation barriers after a cut that crosses several
-- frames. A descendant may continue executing and create new alternatives
-- even though an ancestor cut has removed its old guard.
prune :: Int -> Running -> Running
prune requested running = running
  { runningChoices = drop (runningDepth running - depth) (runningChoices running),
    runningDepth = depth,
    runningBranch = (runningBranch running)
      {branchTasks = map clampTask (branchTasks (runningBranch running))}
  }
  where
    depth = max 0 (min requested (runningDepth running))
    clampTask (Run address fuel scopes) =
      Run address fuel [(owner, min barrier depth) | (owner, barrier) <- scopes]
    clampTask (Return call) = Return call {callEntryDepth = min (callEntryDepth call) depth}
    clampTask task = task

cut :: Int -> Scopes -> Running -> Running
cut owner scopes running = case committingBoundary (branchTasks (runningBranch running)) of
  -- commitFirst removes foreign markers. They still stop alternatives inside
  -- that call, but cannot prune its caller. Keep the guard: if the body never
  -- returns a valid result, a declared det must still report its failure.
  Just barrier -> prune barrier running
  Nothing -> case lookup owner scopes of
    Just barrier -> prune barrier running
    Nothing ->
      let pruned = prune 0 running
       in pruned {runningBranch = (runningBranch pruned) {branchMarker = Just owner}}
  where
    committingBoundary [] = Nothing
    committingBoundary (Return call : rest)
      | callOwner call == owner = Nothing
      | callCommits call = Just (guardDepth (callId call) (callEntryDepth call)
          (runningDepth running) (runningChoices running))
      | otherwise = committingBoundary rest
    committingBoundary (_ : rest) = committingBoundary rest
    guardDepth _ fallback _ [] = fallback
    guardDepth ident fallback depth (Choice _ _ alternative : rest) = case alternative of
      Guard found _ _ _ | ident == found -> depth
      _ -> guardDepth ident fallback (depth - 1) rest

runGoal :: Env -> Heap.Heap s -> Running -> Heap.Address -> Int -> Scopes -> MachineM s Step
runGoal environment heap running address fuel scopes = do
  shape <- checked (Heap.view heap address)
  case shape of
    Heap.AtomView "true" -> continue
    Heap.AtomView "fail" -> failBranch
    Heap.AtomView "false" -> failBranch
    Heap.AtomView "!" -> continue
    Heap.CompoundView "$cut" [ownerAddress] -> do
      ownerShape <- checked (Heap.viewRaw heap ownerAddress)
      case ownerShape of
        Heap.IntegerView owner
          | (local, _) : _ <- scopes, local == fromIntegral owner ->
              drive environment heap (cut local scopes running)
        -- A foreign marker travels after this goal's continuation. A later
        -- local cut or first-success commit can discard its retry before it
        -- reaches its owner, matching the reference's [Found, CutMarker].
        Heap.IntegerView owner -> do
          mark <- lift (Heap.checkpoint heap)
          deferred <- push (Choice mark branch (DeferredCut (fromIntegral owner) scopes)) running
          drive environment heap deferred
        _ -> adapted
    Heap.CompoundView "," [left, right] ->
      drive environment heap running
        { runningBranch = branch {branchTasks = Run left fuel scopes : Run right fuel scopes : branchTasks branch} }
    Heap.CompoundView ";" [left, right] -> do
      -- The reference recognizes literal (Condition -> Then ; Else) before
      -- dereferencing Condition. A variable bound to -> is an ordinary left
      -- alternative here, so inspect its original cell rather than its value.
      original <- checked (Heap.viewRaw heap left)
      case original of
        Heap.CompoundView "->" [condition, yes] ->
          enterScope environment heap running fuel condition (IfScope yes (Just right) fuel scopes)
        _ -> do
          mark <- lift (Heap.checkpoint heap)
          withRight <- push (Choice mark
            branch {branchTasks = Run right fuel scopes : branchTasks branch} Tasks) running
          drive environment heap withRight
            { runningBranch = branch {branchTasks = Run left fuel scopes : branchTasks branch} }
    Heap.CompoundView "->" [condition, yes] ->
      enterScope environment heap running fuel condition (IfScope yes Nothing fuel scopes)
    Heap.CompoundView "call" (callable : arguments) ->
      callGoal environment heap running fuel callable arguments
    Heap.CompoundView "once" [goal] -> enterScope environment heap running fuel goal OnceScope
    Heap.CompoundView "not" [goal] -> enterScope environment heap running fuel goal NotScope
    Heap.CompoundView "findall" [template, goal, result] ->
      enterScope environment heap running fuel goal (FindScope template result fuel scopes [] [])
    Heap.CompoundView "unify" [left, right]
      | not (constrained (branchState branch)) -> do
          accepted <- checked (Heap.unify heap left right)
          if accepted then continue else failBranch
    Heap.AtomView name -> predicate name 0
    Heap.CompoundView name arguments -> predicate name (length arguments)
    _ -> adapted
  where
    branch = runningBranch running
    continue = drive environment heap running
    failBranch = drive environment heap running {runningPhase = Backtracking}
    adapted = adapt environment heap running address fuel scopes
    predicate name arity
      | builtinDet name arity /= Nothing = adapted
      | otherwise = case lookupPred (name, arity) (envProg environment) of
          Just definition
            | not (predIsTabled (envProg environment) definition),
              not (predIsDynamic (envProg environment) definition),
              not (constrained (branchState branch)) ->
                callPredicate environment heap running address fuel scopes definition
          _ -> adapted

constrained :: SolverState -> Bool
constrained state = not (IM.null (stDomains store)) || not (null (stConstraints store))
  where
    store = ssStore state

callPredicate :: Env -> Heap.Heap s -> Running -> Heap.Address -> Int -> Scopes -> Pred -> MachineM s Step
callPredicate environment heap running address fuel scopes definition = do
  let branch = runningBranch running
  state <- checked (Bridge.exportState heap (branchBindings branch) (branchState branch))
  syntax <- checked (Bridge.exportRawTerms heap (branchBindings branch) [address])
  goal <- single syntax
  let normalized = normArithTerm (stSubst (ssStore state)) goal
      args = case normalized of Compound _ as -> as; _ -> []
      argsW = map (deepWalk (stSubst (ssStore state))) args
      key = predKey definition
  case Contracts.selectSignature key definition argsW of
    Left err -> emit environment heap running {runningPhase = Backtracking} (BranchError err)
    Right signature -> do
      (bindings, addresses) <- checked (Bridge.importTerms heap (branchBindings branch) [normalized])
      normalizedAddress <- single addresses
      normalizedShape <- checked (Heap.view heap normalizedAddress)
      let arguments = case normalizedShape of Heap.CompoundView _ as -> as; _ -> []
          ident = runningNextId running
      when (ident == maxBound) (throwError Heap.HeapCapacityExceeded)
      let call = Call ident (ssFresh state) (runningDepth running) key signature arguments
            (Contracts.commitsAfterSuccess definition signature argsW)
          entryBranch = branch {branchBindings = bindings, branchState = state}
          entry = running {runningBranch = entryBranch, runningNextId = ident + 1}
      mark <- lift (Heap.checkpoint heap)
      guarded <- push (Choice mark entryBranch
        (Guard ident key (Contracts.requiredSuccess signature) False)) entry
      if fuel <= 0
        then emit environment heap guarded {runningPhase = Backtracking} BranchExhausted
        else do
          let keys = if predIsIndexed (envProg environment) definition then map indexKey argsW else []
              clauses = [predClauses definition IM.! index | index <- candidateClauses definition keys]
          tryClauses environment heap guarded normalizedAddress fuel
            ((ssFresh state, runningDepth guarded) : scopes) call clauses

tryClauses :: Env -> Heap.Heap s -> Running -> Heap.Address -> Int -> Scopes -> Call -> [Clause] -> MachineM s Step
tryClauses environment heap running _ _ _ _ [] =
  drive environment heap running {runningPhase = Backtracking}
tryClauses environment heap running goal fuel scopes call (clause : remaining) = do
  let branch = runningBranch running
  mark <- lift (Heap.checkpoint heap)
  withRetry <- if null remaining then pure running else
    push (Choice mark branch (ClauseRetry goal fuel scopes call remaining)) running
  let base = ssFresh (branchState branch)
      fresh = base + max 1 (clauseNVars clause)
  when (fresh < base) (throwError Heap.HeapCapacityExceeded)
  let headTerm = renameTerm base (clauseHead clause)
      body = map (renameBody base) (clauseBody clause)
  (bindings, addresses) <- checked (Bridge.importTerms heap (branchBindings branch)
    (map Var [base .. fresh - 1] ++ headTerm : body))
  let activation = drop (fresh - base) addresses
  case activation of
    headAddress : bodyAddresses -> do
      accepted <- checked (Heap.unify heap goal headAddress)
      let nextBranch = branch
            { branchBindings = bindings,
              branchState = (branchState branch) {ssFresh = fresh},
              branchTasks = [Run bodyAddress (fuel - 1) scopes | bodyAddress <- bodyAddresses]
                ++ Return call : branchTasks branch
            }
      drive environment heap withRetry
        { runningBranch = nextBranch,
          runningPhase = if accepted then Seeking else Backtracking
        }
    _ -> throwError Heap.IncompatibleBindings

returnCall :: Env -> Heap.Heap s -> Running -> Call -> MachineM s Step
returnCall environment heap running call = do
  let branch = runningBranch running
  arguments <- checked (Bridge.exportTerms heap (branchBindings branch) (callArguments call))
  let problem = callSignature call >>= \signature ->
        Contracts.checkOutputs (callKey call) signature arguments
  case problem of
    Just err -> emit environment heap running {runningPhase = Backtracking} (BranchError err)
    Nothing ->
      let accepted = running {runningChoices = map mark (runningChoices running)}
          mark (Choice checkpoint saved (Guard ident key required seen))
            | ident == callId call = Choice checkpoint saved (Guard ident key required True)
            | otherwise = Choice checkpoint saved (Guard ident key required seen)
          mark choice = choice
          next = if callCommits call then prune (callEntryDepth call) accepted else accepted
       in drive environment heap next

-- The adapter retains the reference's lazy answer iterator as immutable
-- control state. Do not inspect its tail before returning the current answer:
-- a caller must be able to take a finite prefix of an unfinished search.
adapt :: Env -> Heap.Heap s -> Running -> Heap.Address -> Int -> Scopes -> MachineM s Step
adapt environment heap running address fuel scopes = do
  let branch = runningBranch running
  state <- checked (Bridge.exportState heap (branchBindings branch) (branchState branch))
  terms <- checked (Bridge.exportRawTerms heap (branchBindings branch) [address])
  goal <- single terms
  mark <- lift (Heap.checkpoint heap)
  let entry = running {runningBranch = branch {branchState = state}}
  referenceStep environment heap entry mark scopes (Reference.solveGoal environment fuel state goal)

referenceStep :: Env -> Heap.Heap s -> Running -> Heap.Checkpoint -> Scopes -> Search -> MachineM s Step
referenceStep environment heap running _ _ [] =
  drive environment heap running {runningPhase = Backtracking}
referenceStep environment heap running mark scopes (item : rest) = case item of
  CutMarker owner -> drive environment heap (cut owner scopes running) {runningPhase = Backtracking}
  _ -> do
    next <- push (Choice mark (runningBranch running) (ReferenceRetry scopes rest)) running
    case item of
      Found state -> do
        let branch = runningBranch running
        bindings <- checked (Bridge.syncState heap (branchBindings branch) state)
        drive environment heap next
          { runningBranch = branch {branchBindings = bindings, branchState = state},
            runningPhase = Seeking
          }
      _ -> emit environment heap next {runningPhase = Backtracking} item

backtrack :: Env -> Heap.Heap s -> Running -> MachineM s Step
backtrack environment heap running = case runningChoices running of
  [] -> case branchMarker (runningBranch running) of
    Nothing -> finish environment heap running
    Just owner -> emit environment heap running {runningPhase = Complete} (CutMarker owner)
  Choice mark branch alternative : rest -> do
    checked (Heap.rollback heap mark)
    let restored = running
          { runningBranch = branch,
            runningChoices = rest,
            runningDepth = runningDepth running - 1,
            runningPhase = Seeking
          }
    case alternative of
      Tasks -> drive environment heap restored
      ClauseRetry goal fuel scopes call clauses -> tryClauses environment heap restored goal fuel scopes call clauses
      ReferenceRetry scopes items -> referenceStep environment heap restored mark scopes items
      DeferredCut owner scopes -> drive environment heap (cut owner scopes restored) {runningPhase = Backtracking}
      NativeRetry saved ->
        let rebased = saved
              { runningNextId = max (runningNextId saved) (runningNextId restored),
                runningScope = fmap (\scope -> scope {scopeParent = restored}) (runningScope saved)
              }
         in drive environment heap rebased
      Guard _ key required seen -> case (seen, required) of
        (False, Just det) -> emit environment heap restored {runningPhase = Backtracking}
          (BranchError (DetError key det 0))
        _ -> drive environment heap restored {runningPhase = Backtracking}

-- Shallow callable expansion deliberately retains Compound f [] rather than
-- turning it into Atom f: even call true has that reference-language behavior.
callGoal :: Env -> Heap.Heap s -> Running -> Int -> Heap.Address -> [Heap.Address] -> MachineM s Step
callGoal environment heap running fuel callable arguments = do
  let branch = runningBranch running
  state <- checked (Bridge.exportState heap (branchBindings branch) (branchState branch))
  syntax <- checked (Bridge.exportRawTerms heap (branchBindings branch) (callable : arguments))
  case syntax of
    predicate : args -> do
      let substitution = stSubst (ssStore state)
          goal = case walk substitution predicate of
            Atom name -> Compound name args
            Compound name existing -> Compound name (existing ++ args)
            other -> other
      if isCallable goal
        then do
          mark <- lift (Heap.checkpoint heap)
          (bindings, addresses) <- checked (Bridge.importTerms heap (branchBindings branch)
            [replaceCuts (negate (ssFresh state) - 1) goal])
          address <- single addresses
          launchScope environment heap running mark fuel address bindings CallScope
        else emit environment heap running {runningPhase = Backtracking}
          (BranchError (TypeError "callable" (deepWalk substitution goal)))
    _ -> throwError Heap.IncompatibleBindings

enterScope :: Env -> Heap.Heap s -> Running -> Int -> Heap.Address -> ScopeKind -> MachineM s Step
enterScope environment heap running fuel goal kind = do
  mark <- lift (Heap.checkpoint heap)
  launchScope environment heap running mark fuel goal (branchBindings (runningBranch running)) kind

launchScope :: Env -> Heap.Heap s -> Running -> Heap.Checkpoint -> Int -> Heap.Address -> Bridge.Bindings -> ScopeKind -> MachineM s Step
launchScope environment heap parent mark fuel goal bindings kind =
  let branch = (runningBranch parent)
        { branchBindings = bindings,
          branchTasks = [Run goal fuel []],
          branchMarker = Nothing
        }
      scope = Scope parent mark kind []
      child = Running branch [] 0 (runningNextId parent) Seeking (Just scope)
   in drive environment heap child

scopeEvent :: Env -> Heap.Heap s -> Running -> Scope -> SearchItem -> MachineM s Step
scopeEvent environment heap running scope item = case item of
  CutMarker _ -> drive environment heap running
  Found state -> case scopeKind scope of
    CallScope -> forwardScope environment heap running scope (Just state) Nothing
    OnceScope ->
      drive environment heap (retained scope running state (map Emit (reverse (scopeIssues scope))))
    IfScope yes _ fuel scopes ->
      drive environment heap (retained scope running state
        (map Emit (reverse (scopeIssues scope)) ++ [Run yes fuel scopes]))
    NotScope -> do
      parent <- restoreScope heap scope running
      let dependencies = [issue | issue@(ConsumedIncomplete _) <- reverse (scopeIssues scope)]
      drive environment heap (withTasks (map Emit dependencies ++ [Fail]) parent)
    FindScope template target fuel scopes results outputs -> do
      terms <- checked (Bridge.exportTerms heap (branchBindings (runningBranch running)) [template])
      result <- single terms
      let entry = branchState (runningBranch (scopeParent scope))
          delta = take (ssOutLen state - ssOutLen entry) (ssOutput state)
          updated = scope {scopeKind = FindScope template target fuel scopes (result : results) (delta ++ outputs)}
      drive environment heap running {runningScope = Just updated}
  _ -> case scopeKind scope of
    CallScope -> forwardScope environment heap running scope Nothing (Just item)
    _ -> drive environment heap running
      {runningScope = Just scope {scopeIssues = item : scopeIssues scope}}

-- A streaming call parks the child at every visible item. Its caller may
-- backtrack, commit or cut before that child resumes. Rebase the saved parent
-- on retry so surrounding scope buffers and predicate success guards survive.
forwardScope :: Env -> Heap.Heap s -> Running -> Scope -> Maybe SolverState -> Maybe SearchItem -> MachineM s Step
forwardScope environment heap child scope answer issue = do
  mark <- lift (Heap.checkpoint heap)
  let parent = advanced scope child
  retry <- push (Choice mark (runningBranch parent) (NativeRetry child)) parent
  case (answer, issue) of
    (Just state, Nothing) -> drive environment heap
      (retainBranch child state retry) {runningPhase = Seeking}
    (Nothing, Just item) -> emit environment heap retry {runningPhase = Backtracking} item
    _ -> throwError Heap.IncompatibleBindings

advanced :: Scope -> Running -> Running
advanced scope child = (scopeParent scope)
  {runningNextId = max (runningNextId (scopeParent scope)) (runningNextId child)}

retainBranch :: Running -> SolverState -> Running -> Running
retainBranch child state parent = parent
  { runningBranch = (runningBranch parent)
      { branchBindings = branchBindings (runningBranch child),
        branchState = state
      }
  }

retained :: Scope -> Running -> SolverState -> [Task] -> Running
retained scope child state tasks = withTasks tasks
  (retainBranch child state (advanced scope child)) {runningPhase = Seeking}

restoreScope :: Heap.Heap s -> Scope -> Running -> MachineM s Running
restoreScope heap scope child = do
  checked (Heap.rollback heap (scopeEntry scope))
  pure (advanced scope child) {runningPhase = Seeking}

withTasks :: [Task] -> Running -> Running
withTasks tasks running = running
  {runningBranch = (runningBranch running) {branchTasks = tasks ++ branchTasks (runningBranch running)}}

finish :: Env -> Heap.Heap s -> Running -> MachineM s Step
finish environment heap child = case runningScope child of
  Nothing -> pure Finished
  Just scope -> do
    parent <- restoreScope heap scope child
    let issues = reverse (scopeIssues scope)
        blocked = any blocks issues
        queued tasks = drive environment heap (withTasks (map Emit issues ++ tasks) parent)
    case scopeKind scope of
      CallScope -> drive environment heap parent {runningPhase = Backtracking}
      OnceScope -> queued [Fail]
      NotScope -> queued [Fail | blocked]
      IfScope _ no fuel scopes ->
        queued (if blocked then [Fail] else maybe [Fail] (\goal -> [Run goal fuel scopes]) no)
      FindScope _ target fuel scopes results outputs -> case [issue | issue@(BranchError _) <- issues] of
        firstError : _ ->
          let dependencies = [issue | issue@(ConsumedIncomplete _) <- issues]
           in drive environment heap (withTasks (map Emit (dependencies ++ [firstError]) ++ [Fail]) parent)
        [] -> do
          let branch = runningBranch parent
              entry = branchState branch
              state = entry {ssOutput = outputs ++ ssOutput entry, ssOutLen = ssOutLen entry + length outputs}
          terms <- checked (Bridge.exportRawTerms heap (branchBindings branch) [target])
          targetTerm <- single terms
          (bindings, addresses) <- checked (Bridge.importTerms heap (branchBindings branch)
            [Compound "unify" [targetTerm, mkList (reverse results) Nothing]])
          goal <- single addresses
          let prepared = parent {runningBranch = branch {branchBindings = bindings, branchState = state}}
          drive environment heap (withTasks (map Emit issues ++ [Run goal fuel scopes]) prepared)
  where
    blocks (BranchError _) = True
    blocks BranchExhausted = True
    blocks _ = False

single :: [a] -> MachineM s a
single [value] = pure value
single _ = throwError Heap.IncompatibleBindings

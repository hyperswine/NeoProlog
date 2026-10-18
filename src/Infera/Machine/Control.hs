-- | Explicit native resolution, backtracking, opaque searches and CLP retries.
-- Persistent propagation and native table algorithms retain immutable state;
-- no reference goal evaluator participates in public execution.
--
-- Each externally visible step owns an immutable heap snapshot. Choices and
-- opaque parents independently own their frozen heaps, so active-branch root
-- collection can retire dead bindings without invalidating parked retries.
-- Source-proved first-order tail transfers additionally retire return frames.
module Infera.Machine.Control
  ( Checkpoint,
    Step (..),
    ExecutionBackend (..),
    start,
    startWithBackend,
    startMeasured,
    startMeasuredWithBackend,
    startTraced,
    startTracedWithBackend,
    resumeTraced,
    startGoals,
    startGoalsWithBackend,
    Metrics (..),
    checkpointMetrics,
    resume,
    solveQuery,
    solveQueryWithBackend,
    solveGoals,
  )
where

import Control.Monad (when)
import Control.Monad.Except (ExceptT, runExceptT, throwError)
import Control.Monad.ST (ST, runST)
import Control.Monad.Trans.Class (lift)
import qualified Data.IntMap.Strict as IM
import qualified Data.IntSet as IS
import Data.List (nub, sortOn)
import qualified Data.Map.Lazy as Map
import qualified Data.Set as Set
import qualified Infera.Compile as Compile
import qualified Infera.Compile.Cache as CodeCache
import Infera.Arith (arithOps, evalIntExpr, normArithTerm)
import Infera.CLP (Store (..))
import qualified Infera.CLP as CLP
import Infera.Engine.Reference (Env (..), OutputEvent (..), Search, SearchItem (..), SolverState (..))
import qualified Infera.Engine.Reference as Reference
import qualified Infera.Engine.Contracts as Contracts
import Infera.Error
import Infera.Infer (builtinDet)
import qualified Infera.Machine.Bridge as Bridge
import qualified Infera.Machine.Builtins as Builtins
import qualified Infera.Machine.Bytecode as BytecodeVM
import qualified Infera.Machine.CLP as NativeCLP
import qualified Infera.Machine.Heap as Heap
import qualified Infera.Machine.Tail as Tail
import qualified Infera.Machine.Table as Table
import qualified Infera.Machine.Trace.Types as Trace
import Infera.Program
import Infera.Syntax
import Infera.Unify (deepWalk, renameBody, renameTerm, replaceCuts, termVars, walk)

-- Source cut owners are the same fresh-variable bases used by the reference
-- resolver. The second component is the current choice-stack barrier.
type Scopes = [(Int, Int)]

-- The first compiler slice is opt-in; the interpreted native driver remains
-- an independent execution path for differential tests and unsupported clauses.
data ExecutionBackend = Interpreted | Bytecode deriving (Eq, Show)

data Task
  = Run !Heap.Address !Int Scopes
  | DirectRun !PredicateRoute !Heap.Address !Int Scopes
  | CompiledBody !BytecodeVM.BodyFrame !Int Scopes !(Maybe Trace.ClauseSource)
  | CompiledControl !VarId !Compile.ControlCode !Int Scopes
  | Located (Maybe SourceSpan) Task
  | Return !Call
  | Emit SearchItem
  | Fail
  | Label [VarId]
  | Optimize [VarId] Term

-- These values belong to one exact immutable Program snapshot. Keep proofs
-- lazy: a query need not inspect the call graph of untouched predicates.
data PredicateRoute = PredicateRoute
  { routeDefinition :: !Pred,
    routeDirect :: Bool,
    routeTabled :: Bool,
    routeIndexed :: Bool,
    routeTail :: Bool,
    routeFuelReuse :: Bool
  }

data Call = Call
  { callId :: !Int,
    callOwner :: !Int,
    callEntryDepth :: !Int,
    callKey :: !PredKey,
    callDefinition :: !Pred,
    callSignature :: !(Maybe Signature),
    callArguments :: ![Heap.Address],
    callCommits :: !Bool,
    callTailEligible :: !Bool,
    callFuelReusable :: !Bool,
    callGoalTerm :: !Term,
    callSite :: !(Maybe SourceSpan),
    callClause :: !(Maybe Int),
    callClauseSite :: !(Maybe SourceSpan),
    -- Force the disabled trace branch to []; its thunk would otherwise
    -- capture the retired caller and retain the entire activation history.
    callTraceParents :: ![(Term, Maybe SourceSpan, Trace.TraceFrame)]
  }

data Branch = Branch
  { branchBindings :: !Bridge.Bindings,
    -- The complete persistent store mirrors every native heap binding.
    -- Choices save it together with the heap checkpoint and logical IDs.
    branchState :: !SolverState,
    branchTasks :: [Task],
    branchMarker :: Maybe Int,
    branchTraceContext :: !(Maybe (Term, Maybe SourceSpan))
  }

-- A choice owns all branch state and the heap/trail checkpoint together.
-- Guards remember successful predicate returns across its clause retries;
-- success is decided before the caller's continuation is executed.
data Choice = Choice !Heap.FrozenHeap !Branch Alternative

data Alternative
  = Tasks
  | ClauseRetry !Heap.Address !Int Scopes !Call [(Int, Clause)]
  | IteratorRetry !Bool Scopes Table.InstrumentedSearch
  | Guard !Int !PredKey (Maybe Det) !Bool
  | DeferredCut !Int Scopes
  | NativeRetry !Heap.FrozenHeap !Running
  | LabelRetry [VarId] !VarId [Integer]
  | OptimizeRetry [VarId] Term !VarId !Integer

-- An opaque sub-search parks its caller's entire control state, then runs an
-- isolated choice stack on the same heap prefix. No caller cut barrier is
-- imported. Issues that may be suppressed are buffered inside this frame.
data Continuation
  = SourceGoal !Term
  | CodeGoal !VarId !Compile.ControlCode

data ScopeKind
  = CallScope
  | OnceScope
  | NotScope
  | IfScope !Continuation !(Maybe Continuation) !Int Scopes
  | FindScope Term Term !Int Scopes [Term] [OutputEvent]
  | MinimumScope Term (Maybe (Integer, Store))
  | GoalMinimumScope Term (Maybe (Integer, SolverState))
  | EmitScope Term

data Scope = Scope
  { scopeParent :: !Running,
    scopeEntry :: !Heap.FrozenHeap,
    scopeKind :: !ScopeKind,
    scopeIssues :: [SearchItem],
    scopeEntryEpoch :: !Integer
  }

data Phase = Seeking | Backtracking | Complete

-- The wrapper is strict in Running, but its ID set is computed only if a
-- collection needs it. Tiny opaque searches frequently finish without one.
data ProtectedRoots = ProtectedRoots IS.IntSet

data Running = Running
  { runningBranch :: !Branch,
    runningChoices :: ![Choice],
    runningDepth :: !Int,
    runningNextId :: !Int,
    runningPhase :: !Phase,
    runningScope :: Maybe Scope,
    runningTailReuse :: !Bool,
    runningRoutes :: Map.Map PredKey PredicateRoute,
    runningDynamicNames :: Set.Set String,
    runningProtected :: !ProtectedRoots,
    runningMeasured :: !Bool,
    runningMetrics :: !Metrics,
    runningCollectionLimit :: !Int,
    runningTraced :: !Bool,
    runningEvents :: [Trace.TraceEvent],
    runningSite :: !(Maybe SourceSpan),
    runningCurrent :: !(Maybe Term),
    runningExternalFrames :: [Trace.TraceFrame],
    runningBackend :: !ExecutionBackend,
    -- Force the map spine when crossing an opaque boundary, so a lazy field
    -- selector cannot retain the completed child Running. Values stay lazy.
    runningCode :: !(Map.Map (PredKey, Int) (Maybe Compile.ClauseCode)),
    -- Monotone within a driver lineage. A full restore or relocating
    -- collection invalidates direct reuse of a scope parent's physical roots.
    runningHeapEpoch :: !Integer
  }

-- | Opt-in execution high-water counts, independent of process RTS memory.
-- 'startMeasured' samples every driver step. Normal solving avoids sampling.
data Metrics = Metrics
  { metricCalls :: !Int,
    metricTailCalls :: !Int,
    metricCollections :: !Int,
    metricMaxTasks :: !Int,
    metricMaxChoices :: !Int,
    metricMaxScopes :: !Int,
    metricMaxCutOwners :: !Int,
    metricMaxHeapCells :: !Int,
    metricMaxTrailEntries :: !Int,
    metricMaxBindings :: !Int,
    metricMaxSubstitutions :: !Int,
    metricMaxConstants :: !Int,
    metricMaxFunctors :: !Int,
    metricCompiledActivations :: !Int,
    metricBytecodeInstructions :: !Int,
    metricDirectCalls :: !Int,
    -- Compiled instruction/allocation counts describe accepted activations;
    -- failed heads can execute instructions without returning an activation.
    metricHeadInstructions :: !Int,
    metricHeadCellsAvoided :: !Int,
    metricMaxActivationRegisters :: !Int,
    metricBodyGoalsMaterialized :: !Int,
    metricBodyAllocationInstructions :: !Int,
    metricCompiledControlInstructions :: !Int,
    metricCompiledCuts :: !Int,
    -- Query-local reuse avoids repeating the exact source-witness check.
    metricCodeCacheHits :: !Int,
    -- A predicate hit means its witness matched, not that its lazy plan was
    -- already evaluated by an earlier query.
    metricPredicateCacheHits :: !Int,
    metricPredicateCacheMisses :: !Int,
    -- Reached normal/measured typed builtin instructions (tracing uses the
    -- full source invocation path). One callable wrapper is avoided per call.
    metricTypedBuiltinCalls :: !Int,
    metricBuiltinWrappersAvoided :: !Int,
    metricScopeHandoffs :: !Int,
    metricScopeReplays :: !Int
  }
  deriving (Eq, Show)

emptyMetrics :: Metrics
emptyMetrics = Metrics 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0

data Checkpoint = Checkpoint !Env !Heap.FrozenHeap !Running

data Step = Finished | Yield SearchItem Checkpoint

data DriverStep = Done Running | Produced SearchItem Heap.FrozenHeap Running

checkpointMetrics :: Checkpoint -> Metrics
checkpointMetrics (Checkpoint _ _ running) = runningMetrics running

type MachineM s = ExceptT Heap.HeapError (ST s)

checked :: ST s (Either Heap.HeapError a) -> MachineM s a
checked action = lift action >>= either throwError pure

-- | Start a query with the reference root cut barrier. Eligible native tail
-- transfers reuse their depth budget; other calls keep the existing limit.
start :: Program -> Query -> Either Heap.HeapError Checkpoint
start = startWithBackend Interpreted

startWithBackend :: ExecutionBackend -> Program -> Query -> Either Heap.HeapError Checkpoint
startWithBackend backend = startQuery backend False

-- | As 'start', recording execution counters for testing and measurement.
startMeasured :: Program -> Query -> Either Heap.HeapError Checkpoint
startMeasured = startMeasuredWithBackend Interpreted

startMeasuredWithBackend :: ExecutionBackend -> Program -> Query -> Either Heap.HeapError Checkpoint
startMeasuredWithBackend backend = startQuery backend True

startTraced :: Program -> Query -> Either Heap.HeapError Checkpoint
startTraced = startTracedWithBackend Interpreted

startTracedWithBackend :: ExecutionBackend -> Program -> Query -> Either Heap.HeapError Checkpoint
startTracedWithBackend backend program query = do
  Checkpoint environment frozen running <- startWithBackend backend program query
  let branch = runningBranch running
  pure (Checkpoint environment frozen running {runningTraced = True,
    runningBranch = branch {branchTasks = map (Located Nothing) (branchTasks branch)}})

startQuery :: ExecutionBackend -> Bool -> Program -> Query -> Either Heap.HeapError Checkpoint
startQuery backend measured program query = startWithRoots backend True True measured [(-1, 0)] (Reference.mkEnv program)
  Reference.maxResolutionDepth (Reference.initialState (queryNVars query))
  (map (replaceCuts (-1)) (queryGoals query))

-- | Adapter-compatible entry point for existing solver states. Bare cuts
-- keep the reference solveGoals behavior; unowned internal cut markers are
-- propagated. Resolution fuel counts predicate nesting, not machine steps.
startGoals :: Env -> Int -> SolverState -> [Term] -> Either Heap.HeapError Checkpoint
startGoals = startGoalsWithBackend Interpreted

startGoalsWithBackend :: ExecutionBackend -> Env -> Int -> SolverState -> [Term] -> Either Heap.HeapError Checkpoint
startGoalsWithBackend backend = startWithRoots backend True False False []

-- Internal table producers preserve referenced logical roots, rather than
-- resurrecting every retired activation ID below the monotone fresh counter.
startWithRoots :: ExecutionBackend -> Bool -> Bool -> Bool -> Scopes -> Env -> Int -> SolverState -> [Term]
  -> Either Heap.HeapError Checkpoint
startWithRoots backend dense tailReuse measured scopes environment fuel state goals = runST $ runExceptT $ do
  heap <- lift Heap.newHeap
  bindings <- checked (Bridge.newBindings heap (if dense then [0 .. ssFresh state - 1] else []))
  synchronized <- checked (Bridge.syncState heap bindings (if dense then state else state {ssFresh = 0}))
  (imported, addresses) <- checked (Bridge.importTerms heap synchronized goals)
  frozen <- lift (Heap.freezeHeap heap)
  let branch = Branch imported state [Run address fuel scopes | address <- addresses] Nothing Nothing
      protected = ProtectedRoots (IS.union (Bridge.bindingVariableSet imported)
        (IS.fromList (concatMap termVars goals)))
      program = envProg environment
      dynamic = Set.fromList
        ([name | (name, flags) <- Map.toList (progNameFlags program), FlagDynamic `elem` flags]
          ++ [fst (predKey definition) | definition <- programPreds program,
            FlagDynamic `elem` predFlags definition])
      routes = Map.mapWithKey (\(name, arity) definition ->
        PredicateRoute definition (builtinDet name arity == Nothing && Set.notMember name dynamic)
          (predIsTabled program definition) (predIsIndexed program definition)
          (Tail.eligiblePredicate program definition) (Tail.eligibleFuelReuse program definition)) (progPreds program)
      running = Running branch [] 0 0 Seeking Nothing tailReuse routes dynamic protected measured emptyMetrics 1024 False [] Nothing Nothing [] backend Map.empty 0
  sampled <- sample heap running
  pure (Checkpoint environment frozen sampled)

-- | Run until the next search item or completion. Every mutable operation is
-- contained in this fresh ST scope; only immutable pages and control remain.
resume :: Checkpoint -> Either Heap.HeapError Step
resume checkpoint = snd <$> resumeTraced checkpoint

resumeTraced :: Checkpoint -> Either Heap.HeapError ([Trace.TraceEvent], Step)
resumeTraced (Checkpoint environment frozen running) = runST $ runExceptT $ do
  heap <- lift (Heap.thawHeap frozen)
  result <- drive environment heap running {runningEvents = []}
  pure $ case result of
    Done final -> (reverse (runningEvents final), Finished)
    Produced item saved final ->
      (reverse (runningEvents final), Yield item (Checkpoint environment saved final {runningEvents = []}))

solveQuery :: Program -> Query -> Search
solveQuery = solveQueryWithBackend Interpreted

solveQueryWithBackend :: ExecutionBackend -> Program -> Query -> Search
solveQueryWithBackend backend program query = unfold (startWithBackend backend program query)

solveGoals :: Env -> Int -> SolverState -> [Term] -> Search
solveGoals environment fuel state goals = unfold (startGoals environment fuel state goals)

unfold :: Either Heap.HeapError Checkpoint -> Search
unfold (Left err) = [BranchError (UserError ("machine heap: " ++ show err))]
unfold (Right checkpoint) = case resume checkpoint of
  Left err -> [BranchError (UserError ("machine heap: " ++ show err))]
  Right Finished -> []
  Right (Yield item next) -> item : unfold (Right next)

yield :: Env -> Heap.Heap s -> Running -> SearchItem -> MachineM s DriverStep
yield _ heap running item = do
  frozen <- lift (Heap.freezeHeap heap)
  pure (Produced item frozen running)

-- Scope events stay internal until their construct decides what escapes.
-- Public suspension still happens only through yield's immutable snapshot.
emit :: Env -> Heap.Heap s -> Running -> SearchItem -> MachineM s DriverStep
emit environment heap original item =
  let running = case item of
        BranchError err -> traceCurrent Trace.Exception (Just err) original
        _ -> original
   in emitRecorded environment heap running item

emitRecorded :: Env -> Heap.Heap s -> Running -> SearchItem -> MachineM s DriverStep
emitRecorded environment heap running item = case runningScope running of
  Nothing -> yield environment heap running item
  Just scope -> scopeEvent environment heap running scope item

drive :: Env -> Heap.Heap s -> Running -> MachineM s DriverStep
drive environment heap original = do
  running <- sample heap original
  (activeHeap, active) <- case runningPhase running of
    Seeking | runningTailReuse running -> collectLive heap running
    _ -> pure (heap, running)
  driveSampled environment activeHeap active

driveSampled :: Env -> Heap.Heap s -> Running -> MachineM s DriverStep
driveSampled environment heap running = case runningPhase running of
  Complete -> finish environment heap running
  Backtracking -> backtrack environment heap running
  Seeking -> case branchTasks (runningBranch running) of
    [] -> do
      let branch = runningBranch running
      -- The mirrored store is already an immutable public value. Re-exporting
      -- the heap would both repeat work and rename imported free aliases while
      -- leaving their domain/dependency metadata under the original IDs.
      emit environment heap running {runningPhase = Backtracking} (Found (branchState branch))
    task : rest ->
      let branch = (runningBranch running) {branchTasks = rest}
          next = running {runningBranch = branch}
       in case task of
            Located site inner -> drive environment heap (withTasks [inner] next {runningSite = site})
            Run address fuel scopes -> do
              traced <- beginTaskTrace heap next address
              runGoal environment heap traced address fuel scopes
            DirectRun route address fuel scopes -> do
              traced <- beginTaskTrace heap next address
              let previous = runningMetrics traced
                  counted = if runningMeasured traced then traced {runningMetrics = previous
                    {metricDirectCalls = metricDirectCalls previous + 1}} else traced
              callPredicate environment heap counted address fuel scopes route
            CompiledBody frame fuel scopes source -> materializeBody environment heap next frame fuel scopes source
            CompiledControl base code fuel scopes -> runCompiledControl environment heap next base code fuel scopes
            Return call -> returnCall environment heap next call
            Emit item -> emitRecorded environment heap next item
            Fail -> drive environment heap next {runningPhase = Backtracking}
            Label variables -> label environment heap next variables
            Optimize variables cost -> optimize environment heap next variables cost

-- Pending code holds logical IDs only. Reacquire their current roots after
-- collection, then construct just the reached goal. Removing the final body
-- frame before dispatch preserves the ordinary tail-call return boundary.
materializeBody :: Env -> Heap.Heap s -> Running -> BytecodeVM.BodyFrame -> Int
  -> Scopes -> Maybe Trace.ClauseSource -> MachineM s DriverStep
materializeBody environment heap running frame fuel scopes source = do
  case BytecodeVM.nextControl frame of
    Nothing -> drive environment heap running
    Just (base, code, remaining) -> do
      let continuation = maybe [] (\pending -> [CompiledBody pending fuel scopes source]) remaining
          prepared = withTasks continuation running
          located = if runningTraced running then prepared
            {runningSite = (\site -> Trace.goalSourceSpan site (Compile.controlTemplate code)) <$> source}
            else prepared
      runCompiledControl environment heap located base code fuel scopes

-- Ordinary calls materialize one graph. Transparent control keeps pure code
-- continuations in the native choice stack; opaque control uses the same
-- scope driver and issue policies as interpreted goals.
runCompiledControl :: Env -> Heap.Heap s -> Running -> VarId -> Compile.ControlCode
  -> Int -> Scopes -> MachineM s DriverStep
runCompiledControl environment heap original base code fuel scopes =
  case Compile.controlView code of
    Compile.BuiltinCall tag operands fallback
      | not (runningTraced original) -> runTypedBuiltin environment heap original base tag operands
      | otherwise -> invocation fallback (Just (Compile.builtinKey tag))
    Compile.Invoke plan key -> do
      invocation plan key
    instruction -> do
      traced <- beginCodeTrace original base code
      let previous = runningMetrics traced
          counted = if runningMeasured traced then traced {runningMetrics = previous
            {metricCompiledControlInstructions = metricCompiledControlInstructions previous + 1,
             metricBytecodeInstructions = metricBytecodeInstructions previous + 1}} else traced
          branch = runningBranch counted
          task child = CompiledControl base child fuel scopes
          opaque child kind = do
            mark <- lift (Heap.freezeHeap heap)
            launchTasks environment heap counted mark (branchBindings branch) (branchState branch)
              [CompiledControl base child fuel []] kind
      case instruction of
        Compile.Sequence children -> drive environment heap (withTasks (map task children) counted)
        Compile.Alternative left right -> do
          mark <- lift (Heap.freezeHeap heap)
          withRight <- push (Choice mark branch
            {branchTasks = task right : branchTasks branch} Tasks) counted
          drive environment heap (withTasks [task left] withRight)
        Compile.Cut owner -> do
          let ownerId = case owner of
                Compile.LocalBase -> base
                Compile.LiteralInteger value -> fromIntegral value
              metrics = runningMetrics counted
              cutCounted = if runningMeasured counted then counted {runningMetrics = metrics
                {metricCompiledCuts = metricCompiledCuts metrics + 1}} else counted
          runCut environment heap cutCounted ownerId scopes
        Compile.Once child -> opaque child OnceScope
        Compile.Not child -> opaque child NotScope
        Compile.If condition yes no -> opaque condition
          (IfScope (CodeGoal base yes) (CodeGoal base <$> no) fuel scopes)
        Compile.FindAll template child target -> do
          (templateRoot, withTemplate) <- materializeData heap counted base template
          (targetRoot, prepared) <- materializeData heap withTemplate base target
          let ready = runningBranch prepared
          terms <- checked (Bridge.exportRawTerms heap (branchBindings ready) [templateRoot, targetRoot])
          case terms of
            [templateTerm, targetTerm] -> do
              mark <- lift (Heap.freezeHeap heap)
              launchTasks environment heap prepared mark (branchBindings ready) (branchState ready)
                [CompiledControl base child fuel []] (FindScope templateTerm targetTerm fuel scopes [] [])
            _ -> throwError Heap.IncompatibleBindings
        Compile.Call callable arguments -> do
          (callableRoot, prepared) <- materializeData heap counted base callable
          (roots, ready) <- materializeArguments prepared arguments
          callGoal environment heap ready fuel callableRoot roots
        Compile.BuiltinCall {} -> throwError Heap.IncompatibleBindings
        Compile.Invoke {} -> throwError Heap.IncompatibleBindings
  where
    invocation plan key = do
      (root, allocated) <- materializeData heap original base plan
      let previous = runningMetrics allocated
          counted = if runningMeasured allocated then allocated {runningMetrics = previous
            {metricBodyGoalsMaterialized = metricBodyGoalsMaterialized previous + 1}} else allocated
      dispatchInvocation environment heap counted key root fuel scopes
    materializeArguments running [] = pure ([], running)
    materializeArguments running (plan : plans) = do
      (root, prepared) <- materializeData heap running base plan
      (remaining, ready) <- materializeArguments prepared plans
      pure (root : remaining, ready)

-- Operand roots live only inside this operation. No driver/collection boundary
-- occurs between construction and consumption; pending code retains logical
-- IDs, never these handles. One outer mark owns construction, scalar results,
-- heap writes and CLP reconciliation, including every rejected/error path.
runTypedBuiltin :: Env -> Heap.Heap s -> Running -> VarId -> Compile.BuiltinTag
  -> Compile.OperandPlan -> MachineM s DriverStep
runTypedBuiltin environment heap running base tag plan = do
  mark <- lift (Heap.checkpoint heap)
  attempted <- lift $ runExceptT $ do
    let build = if runningMeasured running
          then BytecodeVM.materializeOperandsInTransactionMeasured
          else BytecodeVM.materializeOperandsInTransaction
    step <- checked (build heap bindings base plan)
    result <- case (tag, BytecodeVM.operandStepRoots step) of
      (Compile.BuiltinUnify, [left, right]) ->
        checked (NativeCLP.unify heap bindings store left right)
      (Compile.BuiltinIs, [left, right]) -> do
        term <- checked (Bridge.exportRawTerms heap bindings [right]) >>= single
        case Builtins.evalIsOperand store term of
          Left err -> pure (Left err)
          Right value -> do
            scalar <- checked (Heap.importScalarInTransaction heap value)
            checked (NativeCLP.unify heap bindings store left scalar)
      _ -> do
        terms <- checked (Bridge.exportRawTerms heap bindings (BytecodeVM.operandStepRoots step))
        case Builtins.builtinOperands tag store terms of
          Builtins.Accept -> pure (Right (Just (bindings, store)))
          Builtins.Reject -> pure (Right Nothing)
          Builtins.Raise err -> pure (Left err)
          Builtins.Post operation -> checked (NativeCLP.applyAccepted heap bindings store operation)
          _ -> throwError Heap.IncompatibleBindings
    pure (result, step)
  case attempted of
    Left problem -> checked (Heap.rollback heap mark) >> throwError problem
    Right (result, step) -> do
      case result of
        Right (Just _) -> pure ()
        _ -> checked (Heap.rollback heap mark)
      let previous = runningMetrics running
          allocations = BytecodeVM.operandStepAllocationInstructions step
          counted = if runningMeasured running then running {runningMetrics = previous
            {metricBodyGoalsMaterialized = metricBodyGoalsMaterialized previous + 1,
             metricBodyAllocationInstructions = metricBodyAllocationInstructions previous + allocations,
             metricBytecodeInstructions = metricBytecodeInstructions previous + allocations + 1,
             metricMaxActivationRegisters = max (metricMaxActivationRegisters previous)
               (BytecodeVM.operandStepRegisterSlots step),
             metricTypedBuiltinCalls = metricTypedBuiltinCalls previous + 1,
             metricBuiltinWrappersAvoided = metricBuiltinWrappersAvoided previous + 1}} else running
      acceptGoalStore environment heap counted result
  where
    branch = runningBranch running
    bindings = branchBindings branch
    store = ssStore (branchState branch)

materializeData :: Heap.Heap s -> Running -> VarId -> Compile.DataPlan
  -> MachineM s (Heap.Address, Running)
materializeData heap running base plan = do
  let build = if runningMeasured running
        then BytecodeVM.materializeDataMeasured else BytecodeVM.materializeData
  step <- checked (build heap (branchBindings (runningBranch running)) base plan)
  let previous = runningMetrics running
      metrics = if runningMeasured running then previous
        {metricBodyAllocationInstructions = metricBodyAllocationInstructions previous
           + BytecodeVM.dataStepAllocationInstructions step,
         metricBytecodeInstructions = metricBytecodeInstructions previous
           + BytecodeVM.dataStepAllocationInstructions step,
         metricMaxActivationRegisters = max (metricMaxActivationRegisters previous)
           (BytecodeVM.dataStepRegisterSlots step)} else previous
  pure (BytecodeVM.dataStepRoot step, running {runningMetrics = metrics})

beginCodeTrace :: Running -> VarId -> Compile.ControlCode -> MachineM s Running
beginCodeTrace running _ _ | not (runningTraced running) = pure running
beginCodeTrace running base code =
  let goal = deepWalk (stSubst (ssStore (branchState (runningBranch running))))
        (renameBody base (Compile.controlTemplate code))
   in pure (recordTrace Trace.Call goal (runningSite running) Nothing running {runningCurrent = Just goal})

beginTaskTrace :: Heap.Heap s -> Running -> Heap.Address -> MachineM s Running
beginTaskTrace _ running _ | not (runningTraced running) = pure running
beginTaskTrace heap running address = do
  goal <- rawTerms heap running [address] >>= single
  let actual = deepWalk (stSubst (ssStore (branchState (runningBranch running)))) goal
  pure (recordTrace Trace.Call actual (runningSite running) Nothing running {runningCurrent = Just actual})

sample :: Heap.Heap s -> Running -> MachineM s Running
sample _ running | not (runningMeasured running) = pure running
sample heap running = do
  cells <- lift (Heap.heapSize heap)
  trail <- lift (Heap.trailSize heap)
  (constants, functors) <- lift (Heap.internSize heap)
  let branch = runningBranch running
      tasks = branchTasks branch
      previous = runningMetrics running
      owners (Located _ task) = owners task
      owners (Run _ _ scopes) = length scopes
      owners (DirectRun _ _ _ scopes) = length scopes
      owners (CompiledBody _ _ scopes _) = length scopes
      owners (CompiledControl _ _ _ scopes) = length scopes
      owners _ = 0
      scopeDepth Nothing = 0
      scopeDepth (Just scope) = 1 + scopeDepth (runningScope (scopeParent scope))
      updated = previous
        { metricMaxTasks = max (metricMaxTasks previous) (length tasks),
          metricMaxChoices = max (metricMaxChoices previous) (runningDepth running),
          metricMaxScopes = max (metricMaxScopes previous) (scopeDepth (runningScope running)),
          metricMaxCutOwners = max (metricMaxCutOwners previous) (maximum (0 : map owners tasks)),
          metricMaxHeapCells = max (metricMaxHeapCells previous) cells,
          metricMaxTrailEntries = max (metricMaxTrailEntries previous) trail,
          metricMaxBindings = max (metricMaxBindings previous) (Bridge.bindingCount (branchBindings branch)),
          metricMaxSubstitutions = max (metricMaxSubstitutions previous) (IM.size (stSubst (ssStore (branchState branch)))),
          metricMaxConstants = max (metricMaxConstants previous) constants,
          metricMaxFunctors = max (metricMaxFunctors previous) functors
        }
  pure running {runningMetrics = updated}

push :: Choice -> Running -> MachineM s Running
push (Choice frozen branch alternative) running = do
  when (runningDepth running == maxBound) (throwError Heap.HeapCapacityExceeded)
  pure running
    { runningChoices = Choice frozen branch {branchTraceContext = context} alternative : runningChoices running,
      runningDepth = runningDepth running + 1
    }
  where
    context = if runningTraced running
      then (\goal -> (goal, runningSite running)) <$> runningCurrent running else Nothing

-- Clamp still-active continuation barriers after a cut that crosses several
-- frames. A descendant may continue executing and create new alternatives
-- even though an ancestor cut has removed its old guard.
prune :: Int -> Running -> Running
prune requested running
  -- Existing continuation barriers are already at most the current depth.
  -- Re-clamping them when no choices are removed only creates lazy chains
  -- of identical scope bounds on every successful prefix helper.
  | depth == runningDepth running = running
  | otherwise = running
  { runningChoices = drop (runningDepth running - depth) (runningChoices running),
    runningDepth = depth,
    runningBranch = (runningBranch running)
      {branchTasks = map clampTask (branchTasks (runningBranch running))}
  }
  where
    depth = max 0 (min requested (runningDepth running))
    clampTask (Located site task) = Located site (clampTask task)
    clampTask (Run address fuel scopes) =
      Run address fuel [(owner, min barrier depth) | (owner, barrier) <- scopes]
    clampTask (DirectRun key address fuel scopes) =
      DirectRun key address fuel [(owner, min barrier depth) | (owner, barrier) <- scopes]
    clampTask (CompiledBody frame fuel scopes source) =
      CompiledBody frame fuel [(owner, min barrier depth) | (owner, barrier) <- scopes] source
    clampTask (CompiledControl base code fuel scopes) =
      CompiledControl base code fuel [(owner, min barrier depth) | (owner, barrier) <- scopes]
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
    committingBoundary (Located _ task : rest) = committingBoundary (task : rest)
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

-- A foreign marker travels after this goal's continuation. A later local
-- cut or first-success commit can discard its retry before it reaches its
-- owner. Compiled and interpreted cuts share this exact boundary policy.
runCut :: Env -> Heap.Heap s -> Running -> Int -> Scopes -> MachineM s DriverStep
runCut environment heap running owner scopes
  | (local, _) : _ <- scopes, local == owner =
      drive environment heap (traceCurrent Trace.Cut Nothing (cut local scopes running))
  | otherwise = do
      mark <- lift (Heap.freezeHeap heap)
      deferred <- push (Choice mark (runningBranch running) (DeferredCut owner scopes)) running
      drive environment heap deferred

runGoal :: Env -> Heap.Heap s -> Running -> Heap.Address -> Int -> Scopes -> MachineM s DriverStep
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
        Heap.IntegerView owner -> runCut environment heap running (fromIntegral owner) scopes
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
          do
            terms <- rawTerms heap running [yes, right]
            case terms of
              [yesTerm, noTerm] -> enterScope environment heap running fuel condition
                (IfScope (SourceGoal yesTerm) (Just (SourceGoal noTerm)) fuel scopes)
              _ -> throwError Heap.IncompatibleBindings
        _ -> do
          mark <- lift (Heap.freezeHeap heap)
          withRight <- push (Choice mark
            branch {branchTasks = Run right fuel scopes : branchTasks branch} Tasks) running
          drive environment heap withRight
            { runningBranch = branch {branchTasks = Run left fuel scopes : branchTasks branch} }
    Heap.CompoundView "->" [condition, yes] -> do
      yesTerm <- rawTerms heap running [yes] >>= single
      enterScope environment heap running fuel condition (IfScope (SourceGoal yesTerm) Nothing fuel scopes)
    Heap.CompoundView "call" (callable : arguments) ->
      callGoal environment heap running fuel callable arguments
    Heap.CompoundView "once" [goal] -> enterScope environment heap running fuel goal OnceScope
    Heap.CompoundView "not" [goal] -> enterScope environment heap running fuel goal NotScope
    Heap.CompoundView "findall" [template, goal, result] -> do
      terms <- rawTerms heap running [template, result]
      case terms of
        [templateTerm, resultTerm] -> enterScope environment heap running fuel goal (FindScope templateTerm resultTerm fuel scopes [] [])
        _ -> throwError Heap.IncompatibleBindings
    Heap.CompoundView "minimize" [cost, goal] -> do
      raw <- rawTerms heap running [cost] >>= single
      enterScope environment heap running fuel goal (GoalMinimumScope raw Nothing)
    Heap.CompoundView "forall" [condition, action] -> do
      terms <- rawTerms heap running [condition, action]
      case terms of
        [a, b] -> expanded (Compound "not" [Compound "," [a, Compound "not" [b]]])
        _ -> throwError Heap.IncompatibleBindings
    Heap.CompoundView "unify" [left, right] -> do
      result <- checked (NativeCLP.unify heap (branchBindings branch) (ssStore (branchState branch)) left right)
      acceptGoalStore environment heap running result
    Heap.CompoundView "label" [list] -> beginLabel environment heap running list
    Heap.CompoundView "labeling" [list] -> beginLabel environment heap running list
    Heap.CompoundView "labeling" [options, list] -> beginMinimum environment heap running options list
    Heap.CompoundView "phrase" [nonterminal, input] -> phrase environment heap running fuel scopes nonterminal input
    Heap.CompoundView "emit" [nonterminal] -> beginEmit environment heap running fuel nonterminal
    Heap.CompoundView "phrase_from_file" [nonterminal, path] -> do
      terms <- rawTerms heap running [nonterminal, path]
      case terms of
        [nt, file] -> case Builtins.readFileContents environment (ssStore (branchState branch)) file of
          Left err -> emit environment heap running {runningPhase = Backtracking} (BranchError err)
          Right contents -> expanded (phraseGoal (walk (stSubst (ssStore (branchState branch))) nt)
            (mkList (map CharLit contents) Nothing))
        _ -> throwError Heap.IncompatibleBindings
    Heap.AtomView name -> builtinOrPredicate name 0
    Heap.CompoundView name arguments -> builtinOrPredicate name (length arguments)
    _ -> adapted
  where
    branch = runningBranch running
    continue = drive environment heap (traceCurrent Trace.Exit Nothing running)
    failBranch = drive environment heap (traceCurrent Trace.Fail Nothing running) {runningPhase = Backtracking}
    expanded goal = do
      (bindings, addresses) <- checked (Bridge.importTerms heap (branchBindings branch) [goal])
      next <- single addresses
      drive environment heap (withTasks [Run next fuel scopes]
        running {runningBranch = branch {branchBindings = bindings}})
    adapted = do
      terms <- rawTerms heap running [address]
      original <- single terms
      case walk (stSubst (ssStore (branchState branch))) original of
        Var _ -> emit environment heap running {runningPhase = Backtracking} (BranchError (InstantiationError original))
        goal -> case functorOf goal of
          Nothing -> emit environment heap running {runningPhase = Backtracking} (BranchError (TypeError "callable goal" goal))
          Just (name, arity) -> predicate name arity
    builtinOrPredicate name arity = do
      syntax <- checked (Bridge.exportRawTerms heap (branchBindings branch) [address])
      goal <- single syntax
      case Builtins.builtin (ssStore (branchState branch)) goal of
        Builtins.NotBuiltin -> case Builtins.ordinaryBuiltin environment (branchState branch) goal of
          Nothing -> predicate name arity
          Just items -> do
            mark <- lift (Heap.freezeHeap heap)
            iteratorStep False environment heap running mark scopes (map Right items)
        action -> performBuiltin environment heap running action
    predicate name arity = case Map.lookup (name, arity) (runningRoutes running) of
      Just route -> callPredicate environment heap running address fuel scopes route
      Nothing
        | Set.member name (runningDynamicNames running) -> do
            terms <- rawTerms heap running [address]
            goal <- single terms
            mark <- lift (Heap.freezeHeap heap)
            iteratorStep False environment heap running mark scopes
              (map Right (Builtins.dynamicCall (branchState branch) (name, arity) goal))
        | otherwise -> emit environment heap running {runningPhase = Backtracking}
            (BranchError (UnknownPredicate (name, arity)))

-- Heap writes and propagation accept or reject one complete branch state.
-- On rejection the backend has already restored the heap transaction.
acceptStore :: Env -> Heap.Heap s -> Running -> Either SolveError (Maybe (Bridge.Bindings, Store)) -> (Running -> MachineM s DriverStep) -> MachineM s DriverStep
acceptStore environment heap running result next = case result of
  Left err -> emit environment heap running {runningPhase = Backtracking} (BranchError err)
  Right Nothing -> drive environment heap running {runningPhase = Backtracking}
  Right (Just (bindings, store)) ->
    let branch = runningBranch running
     in next running {runningBranch = branch
          {branchBindings = bindings, branchState = (branchState branch) {ssStore = store}}}

performBuiltin :: Env -> Heap.Heap s -> Running -> Builtins.Builtin -> MachineM s DriverStep
performBuiltin environment heap running action = case action of
  Builtins.NotBuiltin -> throwError Heap.IncompatibleBindings
  Builtins.Accept -> drive environment heap (traceCurrent Trace.Exit Nothing running)
  Builtins.Reject -> drive environment heap (traceCurrent Trace.Fail Nothing running) {runningPhase = Backtracking}
  Builtins.Raise err -> emit environment heap running {runningPhase = Backtracking} (BranchError err)
  Builtins.Post operation -> do
    result <- checked (NativeCLP.applyAccepted heap bindings store operation)
    acceptGoalStore environment heap running result
  Builtins.Unify left right -> do
    (imported, addresses) <- checked (Bridge.importTerms heap bindings [left, right])
    case addresses of
      [a, b] -> do
        result <- checked (NativeCLP.unify heap imported store a b)
        acceptGoalStore environment heap running result
      _ -> throwError Heap.IncompatibleBindings
  where
    branch = runningBranch running
    bindings = branchBindings branch
    store = ssStore (branchState branch)

acceptGoalStore :: Env -> Heap.Heap s -> Running -> Either SolveError (Maybe (Bridge.Bindings, Store)) -> MachineM s DriverStep
acceptGoalStore environment heap running result = case result of
  Right Nothing -> drive environment heap (traceCurrent Trace.Fail Nothing running) {runningPhase = Backtracking}
  _ -> acceptStore environment heap running result (drive environment heap . traceCurrent Trace.Exit Nothing)

rawTerms :: Heap.Heap s -> Running -> [Heap.Address] -> MachineM s [Term]
rawTerms heap running = checked . Bridge.exportRawTerms heap (branchBindings (runningBranch running))

beginLabel :: Env -> Heap.Heap s -> Running -> Heap.Address -> MachineM s DriverStep
beginLabel environment heap running address = do
  raw <- rawTerms heap running [address] >>= single
  let substitution = stSubst (ssStore (branchState (runningBranch running)))
      (terms, _) = unfoldCons (deepWalk substitution raw)
  label environment heap running (nub (concatMap termVars terms))

-- Plain label intentionally keeps the reference's permissive list handling
-- and original-variable alias test. Minimum labeling has stricter checks.
label :: Env -> Heap.Heap s -> Running -> [VarId] -> MachineM s DriverStep
label environment heap running variables =
  let store = ssStore (branchState (runningBranch running))
      pending = [v | v <- variables, Var w <- [walk (stSubst store) (Var v)], w == v]
      sizes = [(v, CLP.domainOf store v >>= CLP.domainSize) | v <- pending]
   in case pending of
        [] -> drive environment heap running
        _ -> case [v | (v, Nothing) <- sizes] of
          v : _ -> emit environment heap running {runningPhase = Backtracking} (BranchError (UnboundedDomain (Var v)))
          [] -> case sortOn snd sizes of
            (v, _) : _ -> labelValues environment heap running pending v
              (maybe [] id (CLP.domainOf store v >>= CLP.domainValues))
            [] -> throwError Heap.IncompatibleBindings

labelValues :: Env -> Heap.Heap s -> Running -> [VarId] -> VarId -> [Integer] -> MachineM s DriverStep
labelValues environment heap running _ _ [] = drive environment heap running {runningPhase = Backtracking}
labelValues environment heap running variables variable (value : rest) = do
  mark <- lift (Heap.freezeHeap heap)
  let branch = runningBranch running
  -- Keep the tail lazy: a huge finite domain must still yield its first value.
  retry <- push (Choice mark branch (LabelRetry variables variable rest)) running
  result <- checked (NativeCLP.bindInteger heap (branchBindings branch) (ssStore (branchState branch)) variable value)
  acceptStore environment heap retry result (drive environment heap . withTasks [Label variables])

beginMinimum :: Env -> Heap.Heap s -> Running -> Heap.Address -> Heap.Address -> MachineM s DriverStep
beginMinimum environment heap running optionsAddress listAddress = do
  syntax <- rawTerms heap running [optionsAddress, listAddress]
  case syntax of
    [options, rawList] ->
      let store = ssStore (branchState (runningBranch running))
          substitution = stSubst store
          list = deepWalk substitution rawList
          (terms, tailTerm) = unfoldCons list
          invalid (Var _) = False
          invalid (IntLit _) = False
          invalid _ = True
          problem message = emit environment heap running {runningPhase = Backtracking}
            (BranchError (TypeError message list))
       in case deepWalk substitution options of
            Compound "cons" [Compound "min" [cost], Atom "nil"] -> case tailTerm of
              Just _ -> problem "proper list of integer variables"
              Nothing
                | any invalid terms -> problem "list of integer variables"
                | otherwise -> do
                    mark <- lift (Heap.freezeHeap heap)
                    launchTasks environment heap running mark (branchBindings (runningBranch running))
                      (branchState (runningBranch running))
                      [Optimize (nub (concatMap termVars terms)) cost] (MinimumScope cost Nothing)
            other -> emit environment heap running {runningPhase = Backtracking}
              (BranchError (TypeError "labeling options [min Cost]" other))
    _ -> throwError Heap.IncompatibleBindings

minimumBound :: Running -> Term -> Store -> Either SolveError (Maybe Store)
minimumBound running cost store = case runningScope running of
  Just scope -> case scopeKind scope of
    MinimumScope _ (Just (value, _)) -> CLP.addRelation CLP.RelLe cost (IntLit (value - 1)) store
    _ -> Right (Just store)
  Nothing -> Right (Just store)

optimize :: Env -> Heap.Heap s -> Running -> [VarId] -> Term -> MachineM s DriverStep
optimize environment heap running variables cost = do
  let branch = runningBranch running
  result <- checked (NativeCLP.applyAccepted heap (branchBindings branch) (ssStore (branchState branch)) (minimumBound running cost))
  acceptStore environment heap running result $ \bounded ->
    let store = ssStore (branchState (runningBranch bounded))
        pending = nub [w | v <- variables, Var w <- [walk (stSubst store) (Var v)]]
        sizes = [(v, CLP.domainOf store v >>= CLP.domainSize) | v <- pending]
     in case pending of
          [] -> drive environment heap bounded
          _ -> case [v | (v, Nothing) <- sizes] of
            v : _ -> emit environment heap bounded {runningPhase = Backtracking} (BranchError (UnboundedDomain (Var v)))
            [] -> case sortOn snd sizes of
              (v, _) : _ -> case CLP.domainOf store v of
                Just (CLP.Domain (CLP.Fin lower) _ _) -> optimizeValues environment heap bounded pending cost v lower
                _ -> emit environment heap bounded {runningPhase = Backtracking} (BranchError (UnboundedDomain (Var v)))
              [] -> throwError Heap.IncompatibleBindings

-- Retry from the candidate before the sibling's lower bound and incumbent
-- were posted. The incumbent lives in the enclosing scope, outside choices,
-- so each sibling refreshes propagation against the newest optimum.
optimizeValues :: Env -> Heap.Heap s -> Running -> [VarId] -> Term -> VarId -> Integer -> MachineM s DriverStep
optimizeValues environment heap running variables cost variable lower = do
  mark <- lift (Heap.freezeHeap heap)
  let branch = runningBranch running
      operation store = CLP.addDomain (Var variable) (CLP.Fin lower) CLP.PosInf store
        >>= maybe (Right Nothing) (minimumBound running cost)
  result <- checked (NativeCLP.applyAccepted heap (branchBindings branch) (ssStore (branchState branch)) operation)
  acceptStore environment heap running result $ \bounded ->
    let current = runningBranch bounded
        store = ssStore (branchState current)
        values = case walk (stSubst store) (Var variable) of
          IntLit value -> [value]
          _ -> maybe [] id (CLP.domainOf store variable >>= CLP.domainValues)
     in case values of
          [] -> drive environment heap bounded {runningPhase = Backtracking}
          value : _ -> do
            retry <- push (Choice mark branch (OptimizeRetry variables cost variable (value + 1))) bounded
            bound <- checked (NativeCLP.bindInteger heap (branchBindings current) store variable value)
            acceptStore environment heap retry bound (drive environment heap . withTasks [Optimize variables cost])

phraseGoal :: Term -> Term -> Term
phraseGoal nonterminal input = case nonterminal of
  Atom name -> Compound name [input, Atom "nil"]
  Compound name arguments -> Compound name (arguments ++ [input, Atom "nil"])
  other -> Compound "call" [other, input, Atom "nil"]

phrase :: Env -> Heap.Heap s -> Running -> Int -> Scopes -> Heap.Address -> Heap.Address -> MachineM s DriverStep
phrase environment heap running fuel scopes nonterminal inputAddress = do
  syntax <- rawTerms heap running [nonterminal, inputAddress]
  case syntax of
    [nt, rawInput] -> do
      let branch = runningBranch running
          substitution = stSubst (ssStore (branchState branch))
          input = case walk substitution rawInput of
            StrLit text -> mkList (map CharLit text) Nothing
            _ -> rawInput
      (bindings, addresses) <- checked (Bridge.importTerms heap (branchBindings branch)
        [phraseGoal (walk substitution nt) input])
      goal <- single addresses
      drive environment heap (withTasks [Run goal fuel scopes]
        running {runningBranch = branch {branchBindings = bindings}})
    _ -> throwError Heap.IncompatibleBindings

beginEmit :: Env -> Heap.Heap s -> Running -> Int -> Heap.Address -> MachineM s DriverStep
beginEmit environment heap running fuel nonterminal = do
  nt <- rawTerms heap running [nonterminal] >>= single
  mark <- lift (Heap.freezeHeap heap)
  let branch = runningBranch running
      state = branchState branch
      fresh = ssFresh state
  when (fresh == maxBound) (throwError Heap.HeapCapacityExceeded)
  (bindings, addresses) <- checked (Bridge.importTerms heap (branchBindings branch)
    [Var fresh, phraseGoal (walk (stSubst (ssStore state)) nt) (Var fresh)])
  case addresses of
    [_, goal] -> launchTasks environment heap running mark bindings state {ssFresh = fresh + 1}
      [Run goal fuel []] (EmitScope (Var fresh))
    _ -> throwError Heap.IncompatibleBindings

callPredicate :: Env -> Heap.Heap s -> Running -> Heap.Address -> Int -> Scopes -> PredicateRoute -> MachineM s DriverStep
callPredicate environment heap running address fuel scopes route = do
  let branch = runningBranch running
      state = branchState branch
      definition = routeDefinition route
  syntax <- checked (Bridge.exportRawTerms heap (branchBindings branch) [address])
  goal <- single syntax
  let normalized = normArithTerm (stSubst (ssStore state)) goal
      args = case normalized of Compound _ as -> as; _ -> []
      argsW = map (deepWalk (stSubst (ssStore state))) args
      key = predKey definition
  case Contracts.selectSignature key definition argsW of
    Left err -> emit environment heap running {runningPhase = Backtracking} (BranchError err)
    Right signature -> do
      let commits = Contracts.commitsAfterSuccess definition signature argsW
          eligible = routeTail route
            && Tail.eligibleArguments signature argsW
            && Contracts.requiredSuccess signature == Nothing
          fuelEligible = eligible && routeFuelReuse route
          reusable = runningTailReuse running && eligible && quiet running
            && case branchTasks branch of
              Return parent : _ -> callTailEligible parent
                && callCommits parent == commits
                -- Noncommitting calls have no success action that can prune
                -- these retries. Each frozen retry owns its original return
                -- and cut scope, so the active tail may retire independently.
                && (not commits || runningDepth running == callEntryDepth parent)
                && case scopes of
                  (owner, _) : _ -> owner == callOwner parent
                  [] -> False
              _ -> False
          retiredTasks = drop 1 (branchTasks branch)
          prepared = if reusable then running
            {runningBranch = branch {branchTasks = retiredTasks}} else running
          liveScopes = if reusable then drop 1 scopes else scopes
          refundable = reusable && fuelEligible && case branchTasks branch of
            Return parent : _ -> callFuelReusable parent
            _ -> False
          nextFuel = if refundable then fuel + 1 else fuel
          previous = runningMetrics prepared
          counted = if runningMeasured prepared then prepared {runningMetrics = previous
            {metricCalls = metricCalls previous + 1,
             metricTailCalls = metricTailCalls previous + if reusable then 1 else 0}} else prepared
      when (refundable && fuel == maxBound) (throwError Heap.HeapCapacityExceeded)
      -- Force both retired tails even in unmeasured execution. Otherwise a
      -- chain of lazy drop/filter thunks retains the supposedly dead frames.
      when reusable (retiredTasks `seq` liveScopes `seq` pure ())
      (activeHeap, active, activeGoal) <- if reusable
        then collectCallGoal heap counted address
        else pure (heap, counted, address)
      let activeBranch = runningBranch active
          activeState = branchState activeBranch
      -- Normalize the shared graph itself. Exporting and importing a fully
      -- expanded term duplicates unchanged grid/list suffixes at every call.
      normalizedAddress <- if requiresNormalization (stSubst (ssStore state)) goal
        then checked (Bridge.normalizeTermGraph activeHeap (branchBindings activeBranch) activeGoal)
        else pure activeGoal
      let bindings = branchBindings activeBranch
      normalizedShape <- checked (Heap.view activeHeap normalizedAddress)
      let arguments = case normalizedShape of Heap.CompoundView _ as -> as; _ -> []
          ident = runningNextId active
      when (ident == maxBound) (throwError Heap.HeapCapacityExceeded)
      let inherited = case branchTasks branch of
            Return parent : _ | reusable && runningTraced active ->
              (callGoalTerm parent, callSite parent `orSite` callClauseSite parent,
                Trace.TraceFrame (callKey parent) (callClause parent) (callClauseSite parent)) : callTraceParents parent
            _ -> []
          -- Undeclared calls have no delayed output/sort obligation. Their
          -- return frames need no argument graph; keeping every ground list
          -- suffix alive here defeats reclamation of completed activations.
          checkedArguments = case signature of
            Nothing -> []
            Just _ -> arguments
          call = Call ident (ssFresh activeState) (runningDepth active) key definition signature checkedArguments commits eligible fuelEligible
            (if runningTraced active then normalized else Atom "") (runningSite active) Nothing Nothing inherited
          entryBranch = activeBranch {branchBindings = bindings}
          entry = active {runningBranch = entryBranch, runningNextId = ident + 1}
      -- A silent guard has no failure obligation and need not be retained.
      -- Committing foreign cuts use callEntryDepth when there is no guard.
      guarded <- case Contracts.requiredSuccess signature of
        Nothing -> pure entry
        required -> do
          mark <- lift (Heap.freezeHeap activeHeap)
          push (Choice mark entryBranch (Guard ident key required False)) entry
      -- Constrained calls cannot use variant tables. Keep their plain fallback
      -- on the active driver; entering the table callback would reconstruct
      -- the entire caller heap for each body even though no table is used.
      let activeStore = ssStore activeState
          constrainedCall = not (IS.null (stWatched activeStore))
            && any (CLP.isConstrained activeStore)
              (termVarIds (deepWalk (stSubst activeStore) normalized))
      if routeTabled route && not constrainedCall
        then do
          mark <- lift (Heap.freezeHeap activeHeap)
          let tableBranch = (runningBranch guarded)
                {branchTasks = Return call : branchTasks (runningBranch guarded)}
          let callers = [parent | (_, _, parent) <- callTraceParents call] ++ executionFrames guarded
              stream = if runningTraced guarded
                then Table.evalTabledTracedWithContext callers (solveLocatedGoals (runningBackend guarded) (runningTailReuse guarded) callers) environment nextFuel activeState definition normalized
                else map Right (Table.evalTabled (solveNativeGoals (runningBackend guarded) (runningTailReuse guarded)) environment nextFuel activeState definition normalized)
          iteratorStep True environment activeHeap guarded {runningBranch = tableBranch} mark liveScopes stream
        else if nextFuel <= 0
          then emit environment activeHeap guarded {runningPhase = Backtracking} BranchExhausted
          else do
          let keys = if routeIndexed route then map indexKey argsW else []
              clauses = [(index, predClauses definition IM.! index) | index <- candidateClauses definition keys]
          tryClauses environment activeHeap guarded normalizedAddress nextFuel
            ((ssFresh activeState, runningDepth guarded) : liveScopes) call clauses
-- Foreign cut delivery remains a call-boundary obligation. General active
-- collection preserves it; a tail transfer must not retire that obligation.
quiet :: Running -> Bool
quiet running = case branchMarker (runningBranch running) of
  Nothing -> True
  Just _ -> False

-- A tail call's Run task has already been popped. Keep its goal as a temporary
-- control root while retiring the caller and relocating the active heap. The
-- synthetic task is removed before any execution, sampling or snapshot.
collectCallGoal :: Heap.Heap s -> Running -> Heap.Address
  -> MachineM s (Heap.Heap s, Running, Heap.Address)
collectCallGoal heap running goal = do
  let branch = runningBranch running
      rooted = running {runningBranch = branch
        {branchTasks = Run goal 0 [] : branchTasks branch}}
  (activeHeap, active) <- collectLive heap rooted
  case branchTasks (runningBranch active) of
    Run relocated _ _ : rest -> pure (activeHeap,
      active {runningBranch = (runningBranch active) {branchTasks = rest}}, relocated)
    _ -> throwError Heap.IncompatibleBindings

-- Rebuild at seeking boundaries before popping control roots, and after a
-- proved tail transfer. Parked retries own independent frozen heaps. All active
-- control addresses, scope terms and caller logical IDs are roots; Bridge follows
-- raw substitution links rather than changing shallow control syntax.
collectLive :: Heap.Heap s -> Running -> MachineM s (Heap.Heap s, Running)
collectLive heap running = do
  size <- lift (Heap.heapSize heap)
  if size < runningCollectionLimit running then pure (heap, running) else do
    let branch = runningBranch running
        tasks = branchTasks branch
        roots (Located _ task) = roots task
        roots (Run address _ _) = [address]
        roots (DirectRun _ address _ _) = [address]
        roots (Return call) = callArguments call
        roots _ = []
        variables (Located _ task) = variables task
        variables (Return call) = if runningTraced running
          then concatMap termVars (callGoalTerm call : [goal | (goal, _, _) <- callTraceParents call]) else []
        variables (Label pending) = pending
        variables (Optimize pending cost) = pending ++ termVars cost
        variables (CompiledBody frame _ _ _) = BytecodeVM.frameVariables frame
        variables (CompiledControl base code _ _) = map (+ base) (IS.toAscList (Compile.controlVariables code))
        variables _ = []
        scopeVariables = case runningScope running of
          Nothing -> []
          Just scope -> case scopeKind scope of
            FindScope template target _ _ results _ -> concatMap termVars (template : target : results)
            IfScope yes no _ _ -> continuationVariables yes ++ maybe [] continuationVariables no
            EmitScope text -> termVars text
            MinimumScope cost _ -> termVars cost
            GoalMinimumScope cost _ -> termVars cost
            _ -> []
        traceVariables = if runningTraced running then maybe [] termVars (runningCurrent running) else []
        ProtectedRoots protectedIds = runningProtected running
        protected = IS.toAscList protectedIds ++ scopeVariables ++ traceVariables ++ concatMap variables tasks
    (rebuiltHeap, bindings, state, addresses) <- checked
      (Bridge.rebuild heap (branchBindings branch) protected (branchState branch) (concatMap roots tasks))
    relocated <- relocate tasks addresses
    liveSize <- lift (Heap.heapSize rebuiltHeap)
    let previous = runningMetrics running
        metrics = if runningMeasured running then previous
          {metricCollections = metricCollections previous + 1} else previous
        limit = if liveSize > maxBound `div` 2 then maxBound else max 1024 (liveSize * 2)
    pure (rebuiltHeap, running {runningBranch = branch
      {branchBindings = bindings, branchState = state, branchTasks = relocated},
      runningMetrics = metrics, runningCollectionLimit = limit,
      runningHeapEpoch = runningHeapEpoch running + 1})
  where
    relocate :: [Task] -> [Heap.Address] -> MachineM s [Task]
    relocate [] [] = pure []
    relocate (Located site task : rest) addresses = do
      (first, remaining) <- splitAtTask task addresses
      relocated <- relocate rest remaining
      pure (Located site first : relocated)
    relocate (Run _ fuel scopes : rest) (address : addresses) =
      (Run address fuel scopes :) <$> relocate rest addresses
    relocate (DirectRun key _ fuel scopes : rest) (address : addresses) =
      (DirectRun key address fuel scopes :) <$> relocate rest addresses
    relocate (Return call : rest) addresses =
      let count = length (callArguments call)
          (arguments, remaining) = splitAt count addresses
       in if length arguments /= count then throwError Heap.IncompatibleBindings else
            (Return call {callArguments = arguments} :) <$> relocate rest remaining
    relocate (task : rest) addresses = case task of
      Run _ _ _ -> throwError Heap.IncompatibleBindings
      DirectRun _ _ _ _ -> throwError Heap.IncompatibleBindings
      _ -> (task :) <$> relocate rest addresses
    relocate _ _ = throwError Heap.IncompatibleBindings
    splitAtTask task addresses = do
      let count (Located _ inner) = count inner
          count (Run _ _ _) = 1
          count (DirectRun _ _ _ _) = 1
          count (Return call) = length (callArguments call)
          count _ = 0
          (first, remaining) = splitAt (count task) addresses
      rebuilt <- relocate [task] first
      one <- single rebuilt
      pure (one, remaining)

tryClauses :: Env -> Heap.Heap s -> Running -> Heap.Address -> Int -> Scopes -> Call -> [(Int, Clause)] -> MachineM s DriverStep
tryClauses environment heap running _ _ _ _ [] =
  drive environment heap running {runningPhase = Backtracking}
tryClauses environment heap running goal fuel scopes call ((ordinal, clause) : remaining) = do
  let branch = runningBranch running
  withRetry <- if null remaining then pure running else do
    mark <- lift (Heap.freezeHeap heap)
    push (Choice mark branch (ClauseRetry goal fuel scopes call remaining)) running
  let base = ssFresh (branchState branch)
      fresh = base + max 1 (clauseNVars clause)
  when (fresh < base) (throwError Heap.HeapCapacityExceeded)
  let source = if runningTraced running then
        Trace.lookupClauseSource (progSources (envProg environment)) (callKey call) ordinal else Nothing
      selected = call {callClause = Just ordinal, callClauseSite = Trace.sourceClauseSpan <$> source}
      located template task
        | not (runningTraced running) = task
        | otherwise = Located ((\site -> Trace.goalSourceSpan site template) <$> source) task
      (compiled, cached) = resolveClause withRetry call ordinal clause
  (bindings, result, tasks, activation, acceptedFresh) <-
    case compiled of
      Just code -> do
        let activate = if runningMeasured running then BytecodeVM.activateHeadMeasured else BytecodeVM.activateHead
        matched <- checked (activate heap (branchBindings branch)
          (ssStore (branchState branch)) goal base code)
        case matched of
          Left problem -> pure (branchBindings branch, Left problem, [], Nothing, base)
          Right Nothing -> pure (branchBindings branch, Right Nothing, [], Nothing, base)
          Right (Just accepted) -> do
            let allocated = BytecodeVM.headBindings accepted
                pending = maybe [] (\frame -> [CompiledBody frame (fuel - 1) scopes source])
                  (BytecodeVM.headBodyFrame accepted)
            pure (allocated, Right (Just (allocated, BytecodeVM.headStore accepted)), pending,
              Just accepted, fresh)
      Nothing -> do
        let headTerm = renameTerm base (clauseHead clause)
            body = map (renameBody base) (clauseBody clause)
        (allocated, addresses) <- checked (Bridge.importTerms heap (branchBindings branch)
          (map Var [base .. fresh - 1] ++ headTerm : body))
        case drop (fresh - base) addresses of
          headRoot : bodyRoots -> do
            matched <- checked (NativeCLP.unify heap allocated (ssStore (branchState branch)) goal headRoot)
            pure (allocated, matched,
              zipWith (\template bodyRoot -> located template (Run bodyRoot (fuel - 1) scopes))
                (clauseBody clause) bodyRoots, Nothing, fresh)
          _ -> throwError Heap.IncompatibleBindings
  let previous = runningMetrics cached
      metrics = case activation of
        Just accepted | runningMeasured cached -> previous
          {metricCompiledActivations = metricCompiledActivations previous + 1,
           metricBytecodeInstructions = metricBytecodeInstructions previous
             + BytecodeVM.headInstructions accepted
             + BytecodeVM.headAllocationInstructions accepted,
           metricHeadInstructions = metricHeadInstructions previous + BytecodeVM.headInstructions accepted,
           metricHeadCellsAvoided = metricHeadCellsAvoided previous + BytecodeVM.headCellsAvoided accepted,
           metricMaxActivationRegisters = max (metricMaxActivationRegisters previous)
             (BytecodeVM.headRegisterSlots accepted)}
        _ -> previous
      nextBranch = branch
        { branchBindings = bindings,
          branchState = (branchState branch) {ssFresh = acceptedFresh},
          branchTasks = tasks ++ Return selected : branchTasks branch }
      selectedRunning = cached {runningBranch = nextBranch, runningMetrics = metrics}
      locatedHead = case result of
        Left _ | runningTraced selectedRunning -> selectedRunning
          {runningSite = (Trace.sourceHeadSpan <$> source) `orSite` runningSite selectedRunning}
        _ -> selectedRunning
  acceptStore environment heap locatedHead result (drive environment heap)

-- Plans carry no heap addresses or logical state, so retain this memo across
-- retries and opaque returns. Cache unsupported clauses too. Public record
-- updates can leave a predicate's cache stale; validate its selected source
-- once per query before sharing the lazy plan.
resolveClause :: Running -> Call -> Int -> Clause -> (Maybe Compile.ClauseCode, Running)
resolveClause running call ordinal clause
  | runningBackend running == Interpreted = (Nothing, running)
  | otherwise = case Map.lookup key (runningCode running) of
      Just code -> (code, counted previous
        {metricCodeCacheHits = metricCodeCacheHits previous + 1})
      Nothing ->
        let (hit, code) = CodeCache.lookupClauseCode ordinal clause
              (predClauseCache (callDefinition call))
            metrics = if hit
              then previous {metricPredicateCacheHits = metricPredicateCacheHits previous + 1}
              else previous {metricPredicateCacheMisses = metricPredicateCacheMisses previous + 1}
            cached = counted metrics
         in (code, cached {runningCode = Map.insert key code (runningCode running)})
  where
    key = (callKey call, ordinal)
    previous = runningMetrics running
    counted metrics
      | runningMeasured running = running {runningMetrics = metrics}
      | otherwise = running

-- A route is resolved once for this Program version. Builtins retain
-- precedence; dynamic names still enter the generic branch-local dispatcher.
compiledRoute :: Running -> PredKey -> Maybe PredicateRoute
compiledRoute running key = case Map.lookup key (runningRoutes running) of
  Just route | routeDirect route -> Just route
  _ -> Nothing

-- Below the collection threshold, materialization already leaves exactly the
-- continuation that a queued Run/DirectRun would expose after being popped.
-- Dispatch it directly instead of allocating a task and entering the driver
-- again. At a collection boundary the queued task remains an explicit root;
-- measured/traced execution also retains the original sampling/event boundary.
dispatchInvocation :: Env -> Heap.Heap s -> Running -> Maybe PredKey
  -> Heap.Address -> Int -> Scopes -> MachineM s DriverStep
dispatchInvocation environment heap running key address fuel scopes
  | runningMeasured running || runningTraced running = queued
  | not (runningTailReuse running) = direct
  | otherwise = do
      cells <- lift (Heap.heapSize heap)
      if cells >= runningCollectionLimit running then queued else direct
  where
    route = key >>= compiledRoute running
    queued = drive environment heap (withTasks
      [maybe (Run address fuel scopes) (\resolved -> DirectRun resolved address fuel scopes) route] running)
    direct = case route of
      Just resolved -> callPredicate environment heap running address fuel scopes resolved
      Nothing -> runGoal environment heap running address fuel scopes

returnCall :: Env -> Heap.Heap s -> Running -> Call -> MachineM s DriverStep
returnCall environment heap running call = do
  let branch = runningBranch running
  raw <- checked (Bridge.exportRawTerms heap (branchBindings branch) (callArguments call))
  let arguments = map (deepWalk (stSubst (ssStore (branchState branch)))) raw
      problem = callSignature call >>= \signature ->
        Contracts.checkOutputs (callKey call) signature arguments
  case problem of
    Just err -> emit environment heap (traceCallError call err running)
      {runningPhase = Backtracking, runningCurrent = Nothing,
       runningSite = callSite call `orSite` callClauseSite call} (BranchError err)
    Nothing ->
      let accepted = case Contracts.requiredSuccess (callSignature call) of
            Nothing -> running
            Just _ -> running {runningChoices = markSeen (runningChoices running)}
          -- A call owns one required-success guard. Build its updated prefix
          -- now, rather than retaining a lazy map of historical helper returns.
          markSeen [] = []
          markSeen (Choice checkpoint saved (Guard ident key required _) : rest)
            | ident == callId call = Choice checkpoint saved (Guard ident key required True) : rest
          markSeen (choice : rest) =
            let marked = markSeen rest in marked `seq` (choice : marked)
          next = if callCommits call then prune (callEntryDepth call) accepted else accepted
       in drive environment heap (traceCallReturns call next)

-- Native finite builtin and table algorithms return immutable result iterators.
-- Their tails stay lazy until the corresponding retry is actually taken.
iteratorStep :: Bool -> Env -> Heap.Heap s -> Running -> Heap.FrozenHeap -> Scopes -> Table.InstrumentedSearch -> MachineM s DriverStep
iteratorStep _ environment heap running _ _ [] =
  drive environment heap (traceCurrent Trace.Fail Nothing running) {runningPhase = Backtracking}
iteratorStep table environment heap running mark scopes (Left event : rest) =
  iteratorStep table environment heap running {runningEvents = event : runningEvents running} mark scopes rest
iteratorStep table environment heap running mark scopes (Right item : rest) = case item of
  CutMarker owner -> drive environment heap (cut owner scopes running) {runningPhase = Backtracking}
  _ -> do
    next <- push (Choice mark (runningBranch running) (IteratorRetry table scopes rest)) running
    case item of
      Found state -> do
        let branch = runningBranch running
        bindings <- checked (Bridge.syncAcceptedState heap (branchBindings branch) (branchState branch) state)
        let accepted = next
              { runningBranch = branch {branchBindings = bindings, branchState = state},
                runningPhase = Seeking
              }
            traced = case branchTasks branch of
              Return _ : _ -> accepted
              _ -> traceCurrent Trace.Exit Nothing accepted
        drive environment heap traced
      BranchError err | table, runningTraced running,
        any ((== Just err) . Trace.traceError) (runningEvents running) ->
          emitRecorded environment heap next {runningPhase = Backtracking} item
      _ -> emit environment heap next {runningPhase = Backtracking} item

backtrack :: Env -> Heap.Heap s -> Running -> MachineM s DriverStep
backtrack environment heap running = case runningChoices running of
  [] -> case branchMarker (runningBranch running) of
    Nothing -> finish environment heap running
    Just owner -> emit environment heap running {runningPhase = Complete} (CutMarker owner)
  Choice mark branch alternative : rest -> do
    lift (Heap.restoreHeap heap mark)
    let restored = running
          { runningBranch = branch,
            runningChoices = rest,
            runningDepth = runningDepth running - 1,
            runningPhase = Seeking,
            runningHeapEpoch = runningHeapEpoch running + 1,
            runningCurrent = fst <$> branchTraceContext branch,
            runningSite = branchTraceContext branch >>= snd
          }
    case alternative of
      Tasks -> drive environment heap restored
      ClauseRetry goal fuel scopes call clauses -> tryClauses environment heap
        (recordTrace Trace.Redo (callGoalTerm call) (callSite call) Nothing restored) goal fuel scopes call clauses
      IteratorRetry table scopes items -> iteratorStep table environment heap
        (traceCurrent Trace.Redo Nothing restored) mark scopes items
      LabelRetry variables variable values -> labelValues environment heap restored variables variable values
      OptimizeRetry variables cost variable lower -> optimizeValues environment heap restored variables cost variable lower
      DeferredCut owner scopes -> drive environment heap (cut owner scopes restored) {runningPhase = Backtracking}
      NativeRetry frozen saved -> do
        lift (Heap.restoreHeap heap frozen)
        let rebased = saved
              { runningNextId = max (runningNextId saved) (runningNextId restored),
                runningMetrics = runningMetrics restored,
                runningEvents = runningEvents restored,
                runningCode = Map.union (runningCode restored) (runningCode saved),
                runningHeapEpoch = runningHeapEpoch restored + 1,
                runningScope = fmap (\scope -> scope {scopeParent = restored}) (runningScope saved)
              }
        drive environment heap rebased
      Guard _ key required seen -> case (seen, required) of
        (False, Just det) -> emit environment heap restored {runningPhase = Backtracking}
          (BranchError (DetError key det 0))
        _ -> drive environment heap restored {runningPhase = Backtracking}

-- Shallow callable expansion deliberately retains Compound f [] rather than
-- turning it into Atom f: even call true has that reference-language behavior.
callGoal :: Env -> Heap.Heap s -> Running -> Int -> Heap.Address -> [Heap.Address] -> MachineM s DriverStep
callGoal environment heap running fuel callable arguments = do
  let branch = runningBranch running
  let state = branchState branch
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
          mark <- lift (Heap.freezeHeap heap)
          (bindings, addresses) <- checked (Bridge.importTerms heap (branchBindings branch)
            [replaceCuts (negate (ssFresh state) - 1) goal])
          address <- single addresses
          launchScope environment heap running mark fuel address bindings CallScope
        else emit environment heap running {runningPhase = Backtracking}
          (BranchError (TypeError "callable" (deepWalk substitution goal)))
    _ -> throwError Heap.IncompatibleBindings

enterScope :: Env -> Heap.Heap s -> Running -> Int -> Heap.Address -> ScopeKind -> MachineM s DriverStep
enterScope environment heap running fuel goal kind = do
  mark <- lift (Heap.freezeHeap heap)
  launchScope environment heap running mark fuel goal (branchBindings (runningBranch running)) kind

launchScope :: Env -> Heap.Heap s -> Running -> Heap.FrozenHeap -> Int -> Heap.Address -> Bridge.Bindings -> ScopeKind -> MachineM s DriverStep
launchScope environment heap parent mark fuel goal bindings kind =
  launchTasks environment heap parent mark bindings (branchState (runningBranch parent)) [Run goal fuel []] kind

launchTasks :: Env -> Heap.Heap s -> Running -> Heap.FrozenHeap -> Bridge.Bindings -> SolverState -> [Task] -> ScopeKind -> MachineM s DriverStep
launchTasks environment heap parent mark bindings state tasks kind =
  let branch = (runningBranch parent)
        { branchBindings = bindings,
          branchState = state,
          branchTasks = tasks,
          branchMarker = Nothing
        }
      scope = Scope parent mark kind [] (runningHeapEpoch parent)
      child = parent {runningBranch = branch, runningChoices = [], runningDepth = 0,
        runningPhase = Seeking, runningScope = Just scope,
        runningProtected = scopeProtectedRoots parent}
   in drive environment heap child

-- Extract the lazy set and bindings before making its union thunk. The outer
-- wrapper is forced at scope entry, so that thunk retains only ID metadata,
-- never a selector closure over the complete parent driver. Do not inline the
-- extraction back into that thunk or eagerly compute unused short-scope sets.
{-# NOINLINE scopeProtectedRoots #-}
scopeProtectedRoots :: Running -> ProtectedRoots
scopeProtectedRoots Running
  {runningProtected = ProtectedRoots parentIds,
   runningBranch = Branch {branchBindings = bindings}} =
  ProtectedRoots (IS.union parentIds (Bridge.bindingVariableSet bindings))

scopeEvent :: Env -> Heap.Heap s -> Running -> Scope -> SearchItem -> MachineM s DriverStep
scopeEvent environment heap running scope item = case item of
  CutMarker _ -> drive environment heap running
  Found state -> case scopeKind scope of
    CallScope -> forwardScope environment heap running scope (Just state) Nothing
    OnceScope ->
      resumeRetained environment heap scope running state (map Emit (reverse (scopeIssues scope)))
    IfScope yes _ fuel scopes -> do
      parent <- restoreSelected heap scope running state
      prepared <- withContinuation heap parent yes fuel scopes
      drive environment heap (withTasks (map Emit (reverse (scopeIssues scope))) prepared)
    NotScope -> do
      parent <- restoreScope heap scope running
      let dependencies = [issue | issue@(ConsumedIncomplete _) <- reverse (scopeIssues scope)]
      drive environment heap (withTasks (map Emit dependencies ++ [Fail]) parent)
    FindScope template target fuel scopes results outputs -> do
      let result = deepWalk (stSubst (ssStore state)) template
      let entry = branchState (runningBranch (scopeParent scope))
          delta = take (ssOutLen state - ssOutLen entry) (ssOutput state)
          updated = scope {scopeKind = FindScope template target fuel scopes (result : results) (delta ++ outputs)}
      drive environment heap running {runningScope = Just updated}
    MinimumScope cost best ->
      let substitution = stSubst (ssStore state)
          problem err = scopeEvent environment heap running scope (BranchError err)
       in case evalIntExpr substitution cost of
            Left err -> problem err
            Right Nothing -> problem (InstantiationError (deepWalk substitution cost))
            Right (Just value) ->
              let improved = case best of
                    Just (previous, _) | previous <= value -> best
                    _ -> Just (value, ssStore state)
               in drive environment heap running
                    {runningScope = Just scope {scopeKind = MinimumScope cost improved}}
    GoalMinimumScope cost best ->
      let substitution = stSubst (ssStore state)
          problem err = scopeEvent environment heap running scope (BranchError err)
       in case evalIntExpr substitution cost of
            Left err -> problem err
            Right Nothing -> problem (InstantiationError (deepWalk substitution cost))
            Right (Just value) ->
              let improved = case best of
                    Just (previous, _) | previous <= value -> best
                    _ -> Just (value, state)
               in drive environment heap running
                    {runningScope = Just scope {scopeKind = GoalMinimumScope cost improved}}
    EmitScope raw -> do
      let textTerm = deepWalk (stSubst (ssStore state)) raw
          (characters, tailTerm) = unfoldCons textTerm
          character (CharLit c) = Just c
          character _ = Nothing
          prefix = map Emit (reverse (scopeIssues scope))
      case (tailTerm, traverse character characters) of
        (Nothing, Just text) ->
          let output = state {ssOutput = WriteEvent text : ssOutput state, ssOutLen = ssOutLen state + 1}
           in resumeRetained environment heap scope running output prefix
        _ -> resumeRetained environment heap scope running state
          (prefix ++ [Emit (BranchError (TypeError "character list from the DCG" textTerm)), Fail])
  _ -> case scopeKind scope of
    CallScope -> forwardScope environment heap running scope Nothing (Just item)
    _ -> drive environment heap running
      {runningScope = Just scope {scopeIssues = item : scopeIssues scope}}

-- A streaming call parks the child at every visible item. Its caller may
-- backtrack, commit or cut before that child resumes. Rebase the saved parent
-- on retry so surrounding scope buffers and predicate success guards survive.
forwardScope :: Env -> Heap.Heap s -> Running -> Scope -> Maybe SolverState -> Maybe SearchItem -> MachineM s DriverStep
forwardScope environment heap child scope answer issue = do
  childFrozen <- lift (Heap.freezeHeap heap)
  parent <- restoreScope heap scope child
  mark <- lift (Heap.freezeHeap heap)
  retry <- push (Choice mark (runningBranch parent) (NativeRetry childFrozen child)) parent
  case (answer, issue) of
    (Just state, Nothing) -> do
      let branch = runningBranch parent
      bindings <- checked (Bridge.syncAcceptedState heap (branchBindings branch) (branchState branch) state)
      drive environment heap retry
        {runningBranch = branch {branchBindings = bindings, branchState = state}, runningPhase = Seeking}
    (Nothing, Just item) -> emit environment heap retry {runningPhase = Backtracking} item
    _ -> throwError Heap.IncompatibleBindings

advanced :: Scope -> Running -> Running
advanced scope child = (scopeParent scope)
  {runningNextId = max (runningNextId (scopeParent scope)) (runningNextId child),
   runningMetrics = runningMetrics child,
   runningEvents = runningEvents child,
   runningCode = runningCode child}

-- The selected store must belong to the current child heap. Only once,
-- successful conditions and emit call here; minimizers replay their earlier
-- best result separately. An unchanged epoch proves the parked parent roots
-- still address the same prefix; a restore/collection uses the replay path.
restoreSelected :: Heap.Heap s -> Scope -> Running -> SolverState -> MachineM s Running
restoreSelected heap scope child state
  | not (runningTraced child) && runningHeapEpoch child == scopeEntryEpoch scope =
      let parent = advanced scope child
          branch = runningBranch parent
          previous = runningMetrics parent
          metrics = if runningMeasured parent then previous
            {metricScopeHandoffs = metricScopeHandoffs previous + 1} else previous
       in pure parent {runningBranch = branch
            {branchBindings = branchBindings (runningBranch child), branchState = state},
            runningMetrics = metrics, runningHeapEpoch = runningHeapEpoch child}
  | otherwise = do
      parent <- restoreScope heap scope child
      let branch = runningBranch parent
          previous = runningMetrics parent
          metrics = if runningMeasured parent then previous
            {metricScopeReplays = metricScopeReplays previous + 1} else previous
      bindings <- checked (Bridge.syncAcceptedState heap (branchBindings branch) (branchState branch) state)
      pure parent {runningBranch = branch {branchBindings = bindings, branchState = state},
        runningMetrics = metrics}

resumeRetained :: Env -> Heap.Heap s -> Scope -> Running -> SolverState -> [Task] -> MachineM s DriverStep
resumeRetained environment heap scope child state tasks = do
  parent <- restoreSelected heap scope child state
  drive environment heap (withTasks tasks parent)

restoreScope :: Heap.Heap s -> Scope -> Running -> MachineM s Running
restoreScope heap scope child = do
  lift (Heap.restoreHeap heap (scopeEntry scope))
  pure (advanced scope child) {runningPhase = Seeking,
    runningHeapEpoch = runningHeapEpoch child + 1}

withTasks :: [Task] -> Running -> Running
withTasks tasks running = running
  {runningBranch = (runningBranch running) {branchTasks = tasks ++ branchTasks (runningBranch running)}}

continuationVariables :: Continuation -> [VarId]
continuationVariables (SourceGoal goal) = termVars goal
continuationVariables (CodeGoal base code) = map (+ base) (IS.toAscList (Compile.controlVariables code))

withContinuation :: Heap.Heap s -> Running -> Continuation -> Int -> Scopes -> MachineM s Running
withContinuation _ running (CodeGoal base code) fuel scopes =
  pure (withTasks [CompiledControl base code fuel scopes] running)
withContinuation heap running (SourceGoal goal) fuel scopes = do
  let branch = runningBranch running
  (bindings, addresses) <- checked (Bridge.importTerms heap (branchBindings branch) [goal])
  address <- single addresses
  pure (withTasks [Run address fuel scopes] running {runningBranch = branch {branchBindings = bindings}})

finish :: Env -> Heap.Heap s -> Running -> MachineM s DriverStep
finish environment heap child = case runningScope child of
  Nothing -> pure (Done child)
  Just scope -> do
    parent <- restoreScope heap scope child
    let issues = reverse (scopeIssues scope)
        blocked = any blocks issues
        queued tasks = drive environment heap (withTasks (map Emit issues ++ tasks) parent)
    case scopeKind scope of
      CallScope -> drive environment heap parent {runningPhase = Backtracking}
      OnceScope -> queued [Fail]
      EmitScope _ -> queued [Fail]
      MinimumScope _ best -> case (issues, best) of
        ([], Just (_, store)) -> do
          let branch = runningBranch parent
          result <- checked (NativeCLP.applyAccepted heap (branchBindings branch) (ssStore (branchState branch)) (const (Right (Just store))))
          acceptStore environment heap parent result (drive environment heap)
        _ -> queued [Fail]
      GoalMinimumScope _ best -> case (issues, best) of
        ([], Just (_, state)) -> do
          let branch = runningBranch parent
          bindings <- checked (Bridge.syncAcceptedState heap (branchBindings branch) (branchState branch) state)
          drive environment heap parent {runningBranch = branch {branchBindings = bindings, branchState = state}}
        _ -> queued [Fail]
      NotScope -> queued [Fail | blocked]
      IfScope _ no fuel scopes -> case (blocked, no) of
        (False, Just goal) -> do
          prepared <- withContinuation heap parent goal fuel scopes
          drive environment heap (withTasks (map Emit issues) prepared)
        _ -> queued [Fail]
      FindScope _ target fuel scopes results outputs -> case [issue | issue@(BranchError _) <- issues] of
        firstError : _ ->
          let dependencies = [issue | issue@(ConsumedIncomplete _) <- issues]
           in drive environment heap (withTasks (map Emit (dependencies ++ [firstError]) ++ [Fail]) parent)
        [] -> do
          let branch = runningBranch parent
              entry = branchState branch
              -- Solutions are copies, renamed apart as in the reference.
              (copies, fresh) = Reference.renameApart (ssFresh entry) (reverse results)
              state = entry {ssOutput = outputs ++ ssOutput entry, ssOutLen = ssOutLen entry + length outputs, ssFresh = fresh}
          (bindings, addresses) <- checked (Bridge.importTerms heap (branchBindings branch)
            [Compound "unify" [target, mkList copies Nothing]])
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


orSite :: Maybe a -> Maybe a -> Maybe a
orSite (Just value) _ = Just value
orSite Nothing other = other

traceCurrent :: Trace.TracePort -> Maybe SolveError -> Running -> Running
traceCurrent port problem running = case runningCurrent running of
  Just goal -> recordTrace port (deepWalk (stSubst (ssStore (branchState (runningBranch running)))) goal)
    (runningSite running) problem running
  Nothing -> running

-- Physical tail frames may retire while tracing remains enabled. Emit their
-- logical returns in innermost-first order without changing control tasks.
traceCallReturns :: Call -> Running -> Running
traceCallReturns _ running | not (runningTraced running) = running
traceCallReturns call running = go running (current : callTraceParents call)
  where
    current = (callGoalTerm call, callSite call `orSite` callClauseSite call,
      Trace.TraceFrame (callKey call) (callClause call) (callClauseSite call))
    substitution = stSubst (ssStore (branchState (runningBranch running)))
    go active [] = active
    go active ((goal, site, frame) : parents) =
      let event = Trace.TraceEvent Trace.Exit (deepWalk substitution goal) site
            (frame : [parent | (_, _, parent) <- parents] ++ executionFrames active) Nothing
       in go active {runningEvents = event : runningEvents active} parents

traceCallError :: Call -> SolveError -> Running -> Running
traceCallError _ _ running | not (runningTraced running) = running
traceCallError call problem running = running {runningEvents = event : runningEvents running}
  where
    event = Trace.TraceEvent Trace.Exception (callGoalTerm call)
      (callSite call `orSite` callClauseSite call)
      (Trace.TraceFrame (callKey call) (callClause call) (callClauseSite call)
        : [parent | (_, _, parent) <- callTraceParents call] ++ executionFrames running)
      (Just problem)

recordTrace :: Trace.TracePort -> Term -> Maybe SourceSpan -> Maybe SolveError -> Running -> Running
recordTrace _ _ _ _ running | not (runningTraced running) = running
recordTrace port goal site problem running = running
  {runningEvents = Trace.TraceEvent port goal site (executionFrames running) problem : runningEvents running}

executionFrames :: Running -> [Trace.TraceFrame]
executionFrames running = frames running
  where
    frames active = concatMap frame (branchTasks (runningBranch active))
      ++ case runningScope active of
        Just scope -> frames (scopeParent scope)
        Nothing -> runningExternalFrames active
    frame (Located _ task) = frame task
    frame (Return call) = Trace.TraceFrame (callKey call) (callClause call) (callClauseSite call)
      : [parent | (_, _, parent) <- callTraceParents call]
    frame _ = []


-- Native table producer bodies enter their own immutable machine checkpoint.
-- Source identities are stamped before renaming; outer frames are pure metadata.
solveLocatedGoals :: ExecutionBackend -> Bool -> [Trace.TraceFrame] -> Env -> Int -> SolverState
  -> [(Term, Maybe SourceSpan)] -> [Trace.TraceFrame] -> Table.InstrumentedSearch
solveLocatedGoals backend tailReuse callers environment fuel state goals frames = unfoldTraced prepared
  where
    prepared = do
      Checkpoint _ frozen running <- startWithRoots backend False tailReuse False [] environment fuel state (map fst goals)
      let stamp (_, site) (Located _ inner) = Located site inner
          stamp (_, site) task = Located site task
          located = zipWith stamp goals (branchTasks (runningBranch running))
      pure (Checkpoint environment frozen running
        {runningTraced = True, runningExternalFrames = frames ++ callers,
         runningBranch = (runningBranch running) {branchTasks = located}})
    unfoldTraced (Left err) = [Right (BranchError (UserError ("machine heap: " ++ show err)))]
    unfoldTraced (Right checkpoint) = case resumeTraced checkpoint of
      Left err -> unfoldTraced (Left err)
      Right (events, step) -> map Left events ++ case step of
        Finished -> []
        Yield item next -> Right item : unfoldTraced (Right next)


solveNativeGoals :: ExecutionBackend -> Bool -> Env -> Int -> SolverState -> [Term] -> Search
solveNativeGoals backend tailReuse environment fuel state goals =
  unfold (startWithRoots backend False tailReuse False [] environment fuel state goals)


requiresNormalization :: IM.IntMap Term -> Term -> Bool
requiresNormalization substitution goal = case walk substitution goal of
  Compound name arguments -> special name || any argument arguments
  _ -> False
  where
    special name = name `elem` arithOps || name `elem`
      [";", "->", "$cut", "call", "once", "not", "findall", "forall", "minimize", "phrase", "phrase_from_file", "emit"]
    argument term = case walk substitution term of
      Compound name children -> special name || any nested children
      _ -> False
    nested (Var variable) | IM.member variable substitution = True
    nested term = argument term

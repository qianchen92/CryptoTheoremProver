import Crypto.Infrastructure.Asymptotic.SecurityParameter
import Crypto.Infrastructure.Computation.Cost.Distribution
import Mathlib.Probability.ProbabilityMassFunction.Basic
import Mathlib.Probability.ProbabilityMassFunction.Monad

namespace Crypto.Infrastructure.Computation.Oracle

universe uOracle uQuery uResponse uState uValue

/-- A heterogeneous collection of oracle endpoints, indexed by oracle name. -/
structure OracleSpec where
  Name : Type uOracle
  Query : Name → Type uQuery
  Response : (name : Name) → Type uResponse

/-- A stateful probabilistic implementation of every endpoint in an oracle spec. -/
structure OracleEnv (Spec : OracleSpec.{uOracle, uQuery, uResponse}) where
  State : Type uState
  init : State
  query :
    (name : Spec.Name) →
    Crypto.SecPar →
    State →
    Spec.Query name →
    PMF (Spec.Response name × State)

/-- A stateful probabilistic oracle indexed by the security parameter. -/
structure OracleFn (Query : Type uQuery) (Response : Type uResponse) where
  State : Type uState
  init : State
  query : Crypto.SecPar → State → Query → PMF (Response × State)

/-- Resources accumulated along one oracle-program execution path. -/
structure OracleProfile (Spec : OracleSpec.{uOracle, uQuery, uResponse}) where
  cost : Crypto.Infrastructure.Computation.Cost.Cost
  queryTrace : List Spec.Name

namespace OracleProfile

variable {Spec : OracleSpec.{uOracle, uQuery, uResponse}}

/-- The empty execution profile. -/
def zero (Spec : OracleSpec.{uOracle, uQuery, uResponse}) : OracleProfile Spec :=
  ⟨0, []⟩

/-- Sequential composition of two execution profiles. -/
def append (left right : OracleProfile Spec) : OracleProfile Spec :=
  ⟨left.cost + right.cost, left.queryTrace ++ right.queryTrace⟩

/-- A local computation cost with no oracle queries. -/
def ofCost (cost : Crypto.Infrastructure.Computation.Cost.Cost) :
    OracleProfile Spec :=
  ⟨cost, []⟩

/--
The unit-cost profile of one oracle query.

This unit charges for the oracle call itself.  It does not include any
computation performed internally by `OracleEnv.query`.
-/
def ofQuery (name : Spec.Name) : OracleProfile Spec :=
  ⟨1, [name]⟩

@[simp] theorem cost_zero :
    (zero Spec).cost = 0 :=
  rfl

@[simp] theorem queryTrace_zero :
    (zero Spec).queryTrace = [] :=
  rfl

@[simp] theorem cost_append (left right : OracleProfile Spec) :
    (append left right).cost = left.cost + right.cost :=
  rfl

@[simp] theorem queryTrace_append (left right : OracleProfile Spec) :
    (append left right).queryTrace = left.queryTrace ++ right.queryTrace :=
  rfl

@[simp] theorem cost_ofCost (cost : Crypto.Infrastructure.Computation.Cost.Cost) :
    (ofCost (Spec := Spec) cost).cost = cost :=
  rfl

@[simp] theorem queryTrace_ofCost
    (cost : Crypto.Infrastructure.Computation.Cost.Cost) :
    (ofCost (Spec := Spec) cost).queryTrace = [] :=
  rfl

@[simp] theorem cost_ofQuery (name : Spec.Name) :
    (ofQuery name).cost = 1 :=
  rfl

@[simp] theorem queryTrace_ofQuery (name : Spec.Name) :
    (ofQuery name).queryTrace = [name] :=
  rfl

/-- Number of calls to a fixed oracle name along a profile. -/
noncomputable def queryCount (profile : OracleProfile Spec) (name : Spec.Name) : Nat := by
  classical
  exact profile.queryTrace.count name

/-- Total number of oracle calls along a profile. -/
def totalQueries (profile : OracleProfile Spec) : Nat :=
  profile.queryTrace.length

@[simp] theorem queryCount_zero (name : Spec.Name) :
    (zero Spec).queryCount name = 0 := by
  classical
  simp [queryCount, zero]

@[simp] theorem queryCount_ofCost
    (cost : Crypto.Infrastructure.Computation.Cost.Cost) (name : Spec.Name) :
    (ofCost (Spec := Spec) cost).queryCount name = 0 := by
  classical
  simp [queryCount, ofCost]

@[simp] theorem queryCount_ofQuery_self (name : Spec.Name) :
    (ofQuery name).queryCount name = 1 := by
  classical
  simp [queryCount, ofQuery]

@[simp] theorem queryCount_ofQuery_of_ne
    {queried name : Spec.Name} (hne : queried ≠ name) :
    (ofQuery queried).queryCount name = 0 := by
  classical
  simp [queryCount, ofQuery, hne]

@[simp] theorem totalQueries_zero :
    (zero Spec).totalQueries = 0 :=
  rfl

@[simp] theorem totalQueries_ofCost
    (cost : Crypto.Infrastructure.Computation.Cost.Cost) :
    (ofCost (Spec := Spec) cost).totalQueries = 0 :=
  rfl

@[simp] theorem totalQueries_ofQuery (name : Spec.Name) :
    (ofQuery name).totalQueries = 1 :=
  rfl

@[simp] theorem queryCount_append
    (left right : OracleProfile Spec) (name : Spec.Name) :
    (append left right).queryCount name =
      left.queryCount name + right.queryCount name := by
  classical
  simp [queryCount, append]

@[simp] theorem totalQueries_append
    (left right : OracleProfile Spec) :
    (append left right).totalQueries =
      left.totalQueries + right.totalQueries := by
  simp [totalQueries, append]

/-- Calls to one oracle are bounded by the total number of oracle calls. -/
theorem queryCount_le_totalQueries
    (profile : OracleProfile Spec) (name : Spec.Name) :
    profile.queryCount name ≤ profile.totalQueries := by
  classical
  exact List.count_le_length

end OracleProfile

/--
A program with oracle access.

This is a syntax for adaptive oracle interactions.  The machine builds an
`OracleProgram`; the interpreter is responsible for threading the oracle state.
This keeps oracle state hidden from the machine interface.
-/
inductive OracleProgram (Spec : OracleSpec.{uOracle, uQuery, uResponse}) :
    Type (max uValue uResponse) →
      Type (max (uOracle + 1) uQuery (uResponse + 1) (uValue + 1)) where
  | pure {α : Type (max uValue uResponse)} : α → OracleProgram Spec α
  | bind {α : Type (max uValue uResponse)} {β : Type (max uValue uResponse)} :
      OracleProgram Spec α → (α → OracleProgram Spec β) → OracleProgram Spec β
  | liftCosted {α : Type (max uValue uResponse)} :
      Crypto.Infrastructure.Computation.Cost.RandCosted α → OracleProgram Spec α
  | query (name : Spec.Name) :
      Spec.Query name → OracleProgram Spec (ULift.{uValue} (Spec.Response name))

namespace OracleProgram

variable {Spec : OracleSpec.{uOracle, uQuery, uResponse}}

instance : Monad (OracleProgram Spec) where
  pure := fun value => OracleProgram.pure value
  bind := fun program next => OracleProgram.bind program next

/-- Abstract execution paths of an oracle program, independent of an environment. -/
inductive Execution :
    {α : Type (max uValue uResponse)} →
    OracleProgram Spec α →
    α →
    OracleProfile Spec →
    Prop where
  | pure
      {α : Type (max uValue uResponse)}
      (value : α) :
      Execution (OracleProgram.pure value) value (OracleProfile.zero Spec)
  | bind
      {α : Type (max uValue uResponse)}
      {β : Type (max uValue uResponse)}
      {first : OracleProgram Spec α}
      {next : α → OracleProgram Spec β}
      {firstValue : α}
      {value : β}
      {firstProfile nextProfile : OracleProfile Spec}
      (firstExecution : Execution first firstValue firstProfile)
      (nextExecution : Execution (next firstValue) value nextProfile) :
      Execution (OracleProgram.bind first next) value
        (OracleProfile.append firstProfile nextProfile)
  | liftCosted
      {α : Type (max uValue uResponse)}
      {dist : Crypto.Infrastructure.Computation.Cost.RandCosted α}
      {result : Crypto.Infrastructure.Computation.Cost.Costed α}
      (result_mem : result ∈ dist.support) :
      Execution (OracleProgram.liftCosted dist) result.val
        (OracleProfile.ofCost result.cost)
  | query
      (name : Spec.Name)
      (oracleQuery : Spec.Query name)
      (response : Spec.Response name) :
      Execution (OracleProgram.query name oracleQuery) (ULift.up response)
        (OracleProfile.ofQuery name)

/-- A uniform upper bound on the annotated cost of every abstract execution path. -/
def CostBound
    {α : Type (max uValue uResponse)}
    (program : OracleProgram Spec α) (bound : Nat) : Prop :=
  ∀ value profile, Execution program value profile → profile.cost ≤ bound

/-- Per-oracle upper bounds on every abstract execution path. -/
def QueryBound
    {α : Type (max uValue uResponse)}
    (program : OracleProgram Spec α) (bound : Spec.Name → Nat) : Prop :=
  ∀ value profile, Execution program value profile →
    ∀ name, profile.queryCount name ≤ bound name

/-- Every query contributes one unit to the annotated execution cost. -/
theorem Execution.totalQueries_le_cost
    {α : Type (max uValue uResponse)}
    {program : OracleProgram Spec α}
    {value : α}
    {profile : OracleProfile Spec}
    (execution : Execution program value profile) :
    profile.totalQueries ≤ profile.cost := by
  induction execution with
  | pure value =>
      exact Nat.le_refl 0
  | bind firstExecution nextExecution ihFirst ihNext =>
      simpa only [OracleProfile.totalQueries, OracleProfile.append, List.length_append] using
        Nat.add_le_add ihFirst ihNext
  | liftCosted result_mem =>
      exact Nat.zero_le _
  | query name oracleQuery response =>
      exact Nat.le_refl 1

/-- A profiled result of interpreting an oracle program. -/
structure RunResult
    (Spec : OracleSpec.{uOracle, uQuery, uResponse})
    (State : Type uState)
    (α : Type (max uValue uResponse)) where
  value : α
  state : State
  profile : OracleProfile Spec

/--
Interpret an oracle program while recording annotated local cost and the exact
oracle-query trace, threading environment state linearly.
-/
noncomputable def runProfiled
    {α : Type (max uValue uResponse)}
    (program : OracleProgram Spec α)
    (sec : Crypto.SecPar)
    (env : OracleEnv.{uOracle, uQuery, uResponse, uState} Spec)
    (state : env.State) :
    PMF (RunResult Spec env.State α) :=
  match program with
  | OracleProgram.pure value =>
      PMF.pure ⟨value, state, OracleProfile.zero Spec⟩
  | OracleProgram.bind first next =>
      PMF.bind (runProfiled first sec env state) fun firstResult =>
        PMF.bind (runProfiled (next firstResult.value) sec env firstResult.state)
          fun nextResult =>
            PMF.pure
              ⟨nextResult.value, nextResult.state,
                OracleProfile.append firstResult.profile nextResult.profile⟩
  | OracleProgram.liftCosted dist =>
      PMF.bind dist fun result =>
        PMF.pure ⟨result.val, state, OracleProfile.ofCost result.cost⟩
  | OracleProgram.query name oracleQuery =>
      PMF.bind (env.query name sec state oracleQuery) fun result =>
        PMF.pure ⟨ULift.up result.1, result.2, OracleProfile.ofQuery name⟩

/--
Every result in the support of the profiled interpreter follows one of the
environment-independent abstract execution paths.
-/
theorem execution_of_mem_support_runProfiled
    {α : Type (max uValue uResponse)}
    (program : OracleProgram Spec α)
    (sec : Crypto.SecPar)
    (env : OracleEnv.{uOracle, uQuery, uResponse, uState} Spec)
    (state : env.State)
    (result : RunResult Spec env.State α)
    (hresult : result ∈ (runProfiled program sec env state).support) :
    Execution program result.value result.profile := by
  induction program generalizing state with
  | pure value =>
      simp only [runProfiled] at hresult
      rw [PMF.mem_support_pure_iff] at hresult
      subst result
      exact Execution.pure value
  | bind first next ihFirst ihNext =>
      simp only [runProfiled] at hresult
      rw [PMF.mem_support_bind_iff] at hresult
      rcases hresult with ⟨firstResult, hfirstResult, hnextResult⟩
      rw [PMF.mem_support_bind_iff] at hnextResult
      rcases hnextResult with ⟨nextResult, hnextResult, hresult⟩
      rw [PMF.mem_support_pure_iff] at hresult
      subst result
      exact Execution.bind
        (ihFirst state firstResult hfirstResult)
        (ihNext firstResult.value firstResult.state nextResult hnextResult)
  | liftCosted dist =>
      simp only [runProfiled] at hresult
      rw [PMF.mem_support_bind_iff] at hresult
      rcases hresult with ⟨costedResult, hcostedResult, hresult⟩
      rw [PMF.mem_support_pure_iff] at hresult
      subst result
      exact Execution.liftCosted hcostedResult
  | query name oracleQuery =>
      simp only [runProfiled] at hresult
      rw [PMF.mem_support_bind_iff] at hresult
      rcases hresult with ⟨oracleResult, _horacleResult, hresult⟩
      rw [PMF.mem_support_pure_iff] at hresult
      subst result
      exact Execution.query name oracleQuery oracleResult.1

/-- Interpret an oracle program and forget its resource profile. -/
noncomputable def run
    {α : Type (max uValue uResponse)}
    (program : OracleProgram Spec α)
    (sec : Crypto.SecPar)
    (env : OracleEnv.{uOracle, uQuery, uResponse, uState} Spec)
    (state : env.State) :
    PMF (α × env.State) :=
  PMF.map (fun result => (result.value, result.state))
    (runProfiled program sec env state)

/-- Interpret an oracle program from the environment's initial state and forget the final state. -/
noncomputable def runWithEnv
    {α : Type (max uValue uResponse)}
    (program : OracleProgram Spec α)
    (sec : Crypto.SecPar)
    (env : OracleEnv.{uOracle, uQuery, uResponse, uState} Spec) :
    PMF α :=
  PMF.map RunResult.value (runProfiled program sec env env.init)

/-- Interpret from the initial state while retaining the resource profile. -/
noncomputable def runProfiledWithEnv
    {α : Type (max uValue uResponse)}
    (program : OracleProgram Spec α)
    (sec : Crypto.SecPar)
    (env : OracleEnv.{uOracle, uQuery, uResponse, uState} Spec) :
    PMF (RunResult Spec env.State α) :=
  runProfiled program sec env env.init

/-- Interpret from the initial state and retain the annotated path cost. -/
noncomputable def runCostedWithEnv
    {α : Type (max uValue uResponse)}
    (program : OracleProgram Spec α)
    (sec : Crypto.SecPar)
    (env : OracleEnv.{uOracle, uQuery, uResponse, uState} Spec) :
    Crypto.Infrastructure.Computation.Cost.RandCosted α :=
  PMF.map (fun result => ⟨result.value, result.profile.cost⟩)
    (runProfiledWithEnv program sec env)

/-- Erasing the retained path cost recovers the ordinary output distribution. -/
@[simp] theorem valueDist_runCostedWithEnv
    {α : Type (max uValue uResponse)}
    (program : OracleProgram Spec α)
    (sec : Crypto.SecPar)
    (env : OracleEnv.{uOracle, uQuery, uResponse, uState} Spec) :
    Crypto.Infrastructure.Computation.Cost.RandCosted.valueDist
        (runCostedWithEnv program sec env) =
      runWithEnv program sec env := by
  simp only [
    Crypto.Infrastructure.Computation.Cost.RandCosted.valueDist,
    runCostedWithEnv, runProfiledWithEnv, runWithEnv, PMF.map_comp]
  rfl

/-- Forgetting the final state from `run` agrees with `runWithEnv`. -/
@[simp] theorem map_fst_run_eq_runWithEnv
    {α : Type (max uValue uResponse)}
    (program : OracleProgram Spec α)
    (sec : Crypto.SecPar)
    (env : OracleEnv.{uOracle, uQuery, uResponse, uState} Spec) :
    PMF.map Prod.fst (run program sec env env.init) =
      runWithEnv program sec env := by
  simp only [run, runWithEnv, PMF.map_comp]
  rfl

@[simp] theorem runWithEnv_pure
    {α : Type (max uValue uResponse)}
    (value : α)
    (sec : Crypto.SecPar)
    (env : OracleEnv.{uOracle, uQuery, uResponse, uState} Spec) :
    runWithEnv (pure value : OracleProgram Spec α) sec env = PMF.pure value := by
  rw [show runWithEnv (pure value : OracleProgram Spec α) sec env =
    PMF.map RunResult.value
      (PMF.pure ⟨value, env.init, OracleProfile.zero Spec⟩) by rfl]
  exact PMF.pure_map (f := RunResult.value)
    ⟨value, env.init, OracleProfile.zero Spec⟩

end OracleProgram

end Crypto.Infrastructure.Computation.Oracle

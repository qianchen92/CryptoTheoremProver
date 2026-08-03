import Crypto.Infrastructure.Asymptotic.SecurityParameter
import Crypto.Infrastructure.Computation.Cost.Distribution
import Mathlib.Probability.ProbabilityMassFunction.Basic
import Mathlib.Probability.ProbabilityMassFunction.Monad

namespace Crypto.Infrastructure.Computation.Oracle

universe uCost uOracle uQuery uResponse uState uValue

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

/-!
## Generic-cost oracle programs

The `...T` declarations below are the cost-model-polymorphic core.  The
long-standing `OracleProfile` and `OracleProgram` declarations later in this
file remain the public natural-number compatibility API.  Every legacy query
has its original unit local cost; callers that need another explicit cost use
`OracleProgramT natCostModel` directly.
-/

/-- Resources accumulated along one oracle-program path in cost model `M`. -/
structure OracleProfileT
    (M : Crypto.Infrastructure.Computation.Cost.CostModel.{uCost})
    (Spec : OracleSpec.{uOracle, uQuery, uResponse}) where
  cost : M.Cost
  queryTrace : List Spec.Name

namespace OracleProfileT

open Crypto.Infrastructure.Computation.Cost

variable {M : CostModel.{uCost}}
variable {Spec : OracleSpec.{uOracle, uQuery, uResponse}}

/-- The empty generic execution profile. -/
def zero (M : CostModel.{uCost})
    (Spec : OracleSpec.{uOracle, uQuery, uResponse}) : OracleProfileT M Spec := by
  letI := M.instAddMonoid
  exact ⟨0, []⟩

/-- Sequential profile composition, preserving left-to-right cost order. -/
def append (left right : OracleProfileT M Spec) : OracleProfileT M Spec := by
  letI := M.instAddMonoid
  exact ⟨left.cost + right.cost, left.queryTrace ++ right.queryTrace⟩

/-- Local work with no oracle queries. -/
def ofCost (cost : M.Cost) : OracleProfileT M Spec :=
  ⟨cost, []⟩

/-- One oracle call with an explicit cost in the caller's cost model. -/
def ofQueryWithCost (localCost : M.Cost) (name : Spec.Name) :
    OracleProfileT M Spec :=
  ⟨localCost, [name]⟩

@[simp] theorem cost_zero : (zero M Spec).cost = M.instAddMonoid.zero :=
  rfl

@[simp] theorem queryTrace_zero : (zero M Spec).queryTrace = [] :=
  rfl

@[simp] theorem cost_append (left right : OracleProfileT M Spec) :
    (append left right).cost = M.instAddMonoid.add left.cost right.cost :=
  rfl

@[simp] theorem queryTrace_append (left right : OracleProfileT M Spec) :
    (append left right).queryTrace = left.queryTrace ++ right.queryTrace :=
  rfl

@[simp] theorem cost_ofCost (cost : M.Cost) :
    (ofCost (Spec := Spec) cost).cost = cost :=
  rfl

@[simp] theorem queryTrace_ofCost (cost : M.Cost) :
    (ofCost (Spec := Spec) cost).queryTrace = [] :=
  rfl

@[simp] theorem cost_ofQueryWithCost (localCost : M.Cost) (name : Spec.Name) :
    (ofQueryWithCost localCost name).cost = localCost :=
  rfl

@[simp] theorem queryTrace_ofQueryWithCost
    (localCost : M.Cost) (name : Spec.Name) :
    (ofQueryWithCost localCost name).queryTrace = [name] :=
  rfl

/-- Number of calls to a fixed oracle name. -/
noncomputable def queryCount
    (profile : OracleProfileT M Spec) (name : Spec.Name) : Nat := by
  classical
  exact profile.queryTrace.count name

/-- Total number of calls, deliberately separate from the modelled cost. -/
def totalQueries (profile : OracleProfileT M Spec) : Nat :=
  profile.queryTrace.length

@[simp] theorem queryCount_zero (name : Spec.Name) :
    (zero M Spec).queryCount name = 0 := by
  classical
  simp [queryCount, zero]

@[simp] theorem queryCount_ofCost (cost : M.Cost) (name : Spec.Name) :
    (ofCost (Spec := Spec) cost).queryCount name = 0 := by
  classical
  simp [queryCount, ofCost]

@[simp] theorem queryCount_ofQueryWithCost_self
    (localCost : M.Cost) (name : Spec.Name) :
    (ofQueryWithCost localCost name).queryCount name = 1 := by
  classical
  simp [queryCount, ofQueryWithCost]

@[simp] theorem queryCount_ofQueryWithCost_of_ne
    (localCost : M.Cost) {queried name : Spec.Name} (hne : queried ≠ name) :
    (ofQueryWithCost localCost queried).queryCount name = 0 := by
  classical
  simp [queryCount, ofQueryWithCost, hne]

@[simp] theorem totalQueries_zero : (zero M Spec).totalQueries = 0 :=
  rfl

@[simp] theorem totalQueries_ofCost (cost : M.Cost) :
    (ofCost (Spec := Spec) cost).totalQueries = 0 :=
  rfl

@[simp] theorem totalQueries_ofQueryWithCost
    (localCost : M.Cost) (name : Spec.Name) :
    (ofQueryWithCost localCost name).totalQueries = 1 :=
  rfl

@[simp] theorem queryCount_append
    (left right : OracleProfileT M Spec) (name : Spec.Name) :
    (append left right).queryCount name =
      left.queryCount name + right.queryCount name := by
  classical
  simp [queryCount, append]

@[simp] theorem totalQueries_append (left right : OracleProfileT M Spec) :
    (append left right).totalQueries =
      left.totalQueries + right.totalQueries := by
  simp [totalQueries, append]

theorem queryCount_le_totalQueries
    (profile : OracleProfileT M Spec) (name : Spec.Name) :
    profile.queryCount name ≤ profile.totalQueries := by
  classical
  exact List.count_le_length

end OracleProfileT

/-- An adaptive oracle program whose local paths carry costs from `M`. -/
inductive OracleProgramT
    (M : Crypto.Infrastructure.Computation.Cost.CostModel.{uCost})
    (Spec : OracleSpec.{uOracle, uQuery, uResponse}) :
    Type (max uValue uResponse) →
      Type (max (uCost + 1) (uOracle + 1) uQuery (uResponse + 1) (uValue + 1)) where
  | pure {α : Type (max uValue uResponse)} : α → OracleProgramT M Spec α
  | bind {α : Type (max uValue uResponse)} {β : Type (max uValue uResponse)} :
      OracleProgramT M Spec α → (α → OracleProgramT M Spec β) →
        OracleProgramT M Spec β
  | liftCosted {α : Type (max uValue uResponse)} :
      Crypto.Infrastructure.Computation.Cost.RandCostedT M α →
        OracleProgramT M Spec α
  | queryWithCost
      (localCost : M.Cost) (name : Spec.Name) :
      Spec.Query name → OracleProgramT M Spec (ULift.{uValue} (Spec.Response name))

namespace OracleProgramT

open Crypto.Infrastructure.Computation.Cost

variable {M : CostModel.{uCost}}
variable {Spec : OracleSpec.{uOracle, uQuery, uResponse}}

instance : Monad (OracleProgramT M Spec) where
  pure := fun value => OracleProgramT.pure value
  bind := fun program next => OracleProgramT.bind program next

/-- Abstract generic-cost execution paths, independent of an environment. -/
inductive Execution :
    {α : Type (max uValue uResponse)} →
    OracleProgramT M Spec α → α → OracleProfileT M Spec → Prop where
  | pure {α : Type (max uValue uResponse)} (value : α) :
      Execution (OracleProgramT.pure value) value (OracleProfileT.zero M Spec)
  | bind
      {α : Type (max uValue uResponse)} {β : Type (max uValue uResponse)}
      {first : OracleProgramT M Spec α} {next : α → OracleProgramT M Spec β}
      {firstValue : α} {value : β}
      {firstProfile nextProfile : OracleProfileT M Spec}
      (firstExecution : Execution first firstValue firstProfile)
      (nextExecution : Execution (next firstValue) value nextProfile) :
      Execution (OracleProgramT.bind first next) value
        (OracleProfileT.append firstProfile nextProfile)
  | liftCosted
      {α : Type (max uValue uResponse)}
      {dist : RandCostedT M α} {result : CostedT M α}
      (result_mem : result ∈ dist.support) :
      Execution (OracleProgramT.liftCosted dist) result.val
        (OracleProfileT.ofCost result.cost)
  | queryWithCost
      (localCost : M.Cost) (name : Spec.Name) (oracleQuery : Spec.Query name)
      (response : Spec.Response name) :
      Execution (OracleProgramT.queryWithCost localCost name oracleQuery)
        (ULift.up response) (OracleProfileT.ofQueryWithCost localCost name)

/-- Upper bound on every local-cost path. -/
def CostBound {α : Type (max uValue uResponse)}
    (program : OracleProgramT M Spec α) (bound : M.Cost) : Prop :=
  ∀ value profile, Execution program value profile →
    M.instPartialOrder.le profile.cost bound

/-- Per-name query bounds stay natural-number structural resources. -/
def QueryBound {α : Type (max uValue uResponse)}
    (program : OracleProgramT M Spec α) (bound : Spec.Name → Nat) : Prop :=
  ∀ value profile, Execution program value profile →
    ∀ name, profile.queryCount name ≤ bound name

/-- Total query bounds stay independent of local runtime. -/
def TotalQueryBound {α : Type (max uValue uResponse)}
    (program : OracleProgramT M Spec α) (bound : Nat) : Prop :=
  ∀ value profile, Execution program value profile →
    profile.totalQueries ≤ bound

/-- A generic-cost profiled interpreter result. -/
structure RunResult
    (M : CostModel.{uCost}) (Spec : OracleSpec.{uOracle, uQuery, uResponse})
    (State : Type uState) (α : Type (max uValue uResponse)) where
  value : α
  state : State
  profile : OracleProfileT M Spec

/-- Interpret a generic-cost oracle program and retain local cost and trace. -/
noncomputable def runProfiled
    {α : Type (max uValue uResponse)} (program : OracleProgramT M Spec α)
    (sec : Crypto.SecPar)
    (env : OracleEnv.{uOracle, uQuery, uResponse, uState} Spec)
    (state : env.State) : PMF (RunResult M Spec env.State α) :=
  match program with
  | OracleProgramT.pure value =>
      PMF.pure ⟨value, state, OracleProfileT.zero M Spec⟩
  | OracleProgramT.bind first next =>
      PMF.bind (runProfiled first sec env state) fun firstResult =>
        PMF.bind (runProfiled (next firstResult.value) sec env firstResult.state)
          fun nextResult =>
            PMF.pure
              ⟨nextResult.value, nextResult.state,
                OracleProfileT.append firstResult.profile nextResult.profile⟩
  | OracleProgramT.liftCosted dist =>
      PMF.bind dist fun result =>
        PMF.pure ⟨result.val, state, OracleProfileT.ofCost result.cost⟩
  | OracleProgramT.queryWithCost localCost name oracleQuery =>
      PMF.bind (env.query name sec state oracleQuery) fun result =>
        PMF.pure
          ⟨ULift.up result.1, result.2,
            OracleProfileT.ofQueryWithCost localCost name⟩

theorem execution_of_mem_support_runProfiled
    {α : Type (max uValue uResponse)} (program : OracleProgramT M Spec α)
    (sec : Crypto.SecPar)
    (env : OracleEnv.{uOracle, uQuery, uResponse, uState} Spec)
    (state : env.State) (result : RunResult M Spec env.State α)
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
  | queryWithCost localCost name oracleQuery =>
      simp only [runProfiled] at hresult
      rw [PMF.mem_support_bind_iff] at hresult
      rcases hresult with ⟨oracleResult, _horacleResult, hresult⟩
      rw [PMF.mem_support_pure_iff] at hresult
      subst result
      exact Execution.queryWithCost localCost name oracleQuery oracleResult.1

/-- Run from the initial state and retain the full generic profile. -/
noncomputable def runProfiledWithEnv
    {α : Type (max uValue uResponse)} (program : OracleProgramT M Spec α)
    (sec : Crypto.SecPar)
    (env : OracleEnv.{uOracle, uQuery, uResponse, uState} Spec) :
    PMF (RunResult M Spec env.State α) :=
  runProfiled program sec env env.init

/-- Run from the initial state and retain only the returned value. -/
noncomputable def runWithEnv
    {α : Type (max uValue uResponse)} (program : OracleProgramT M Spec α)
    (sec : Crypto.SecPar)
    (env : OracleEnv.{uOracle, uQuery, uResponse, uState} Spec) : PMF α :=
  PMF.map RunResult.value (runProfiled program sec env env.init)

/-- Retain the generic local path cost while forgetting the final state. -/
noncomputable def runCostedWithEnv
    {α : Type (max uValue uResponse)} (program : OracleProgramT M Spec α)
    (sec : Crypto.SecPar)
    (env : OracleEnv.{uOracle, uQuery, uResponse, uState} Spec) :
    RandCostedT M α :=
  PMF.map (fun result => ⟨result.value, result.profile.cost⟩)
    (runProfiledWithEnv program sec env)

@[simp] theorem valueDist_runCostedWithEnv
    {α : Type (max uValue uResponse)} (program : OracleProgramT M Spec α)
    (sec : Crypto.SecPar)
    (env : OracleEnv.{uOracle, uQuery, uResponse, uState} Spec) :
    RandCostedT.valueDist (runCostedWithEnv program sec env) =
      runWithEnv program sec env := by
  simp only [RandCostedT.valueDist, runCostedWithEnv, runProfiledWithEnv,
    runWithEnv, PMF.map_comp]
  rfl

end OracleProgramT

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
The profile of one oracle query with an explicit local call cost.

This cost belongs to the calling program.  It does not include any computation
performed internally by `OracleEnv.query`.
-/
def ofQueryWithCost (localCost : Crypto.Infrastructure.Computation.Cost.Cost)
    (name : Spec.Name) : OracleProfile Spec :=
  ⟨localCost, [name]⟩

/-- The compatibility profile for an oracle query charged one local unit. -/
def ofUnitCostQuery (name : Spec.Name) : OracleProfile Spec :=
  ofQueryWithCost 1 name

/-- Backwards-compatible name for a query profile charged one local unit. -/
def ofQuery (name : Spec.Name) : OracleProfile Spec :=
  ofUnitCostQuery name

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

@[simp] theorem cost_ofQueryWithCost
    (localCost : Crypto.Infrastructure.Computation.Cost.Cost)
    (name : Spec.Name) :
    (ofQueryWithCost localCost name).cost = localCost :=
  rfl

@[simp] theorem queryTrace_ofQueryWithCost
    (localCost : Crypto.Infrastructure.Computation.Cost.Cost)
    (name : Spec.Name) :
    (ofQueryWithCost localCost name).queryTrace = [name] :=
  rfl

@[simp] theorem cost_ofUnitCostQuery (name : Spec.Name) :
    (ofUnitCostQuery name).cost = 1 :=
  rfl

@[simp] theorem queryTrace_ofUnitCostQuery (name : Spec.Name) :
    (ofUnitCostQuery name).queryTrace = [name] :=
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

@[simp] theorem queryCount_ofQueryWithCost_self
    (localCost : Crypto.Infrastructure.Computation.Cost.Cost)
    (name : Spec.Name) :
    (ofQueryWithCost localCost name).queryCount name = 1 := by
  classical
  simp [queryCount, ofQueryWithCost]

@[simp] theorem queryCount_ofQueryWithCost_of_ne
    (localCost : Crypto.Infrastructure.Computation.Cost.Cost)
    {queried name : Spec.Name} (hne : queried ≠ name) :
    (ofQueryWithCost localCost queried).queryCount name = 0 := by
  classical
  simp [queryCount, ofQueryWithCost, hne]

@[simp] theorem queryCount_ofQuery_self (name : Spec.Name) :
    (ofQuery name).queryCount name = 1 :=
  queryCount_ofQueryWithCost_self 1 name

@[simp] theorem queryCount_ofQuery_of_ne
    {queried name : Spec.Name} (hne : queried ≠ name) :
    (ofQuery queried).queryCount name = 0 :=
  queryCount_ofQueryWithCost_of_ne 1 hne

@[simp] theorem totalQueries_zero :
    (zero Spec).totalQueries = 0 :=
  rfl

@[simp] theorem totalQueries_ofCost
    (cost : Crypto.Infrastructure.Computation.Cost.Cost) :
    (ofCost (Spec := Spec) cost).totalQueries = 0 :=
  rfl

@[simp] theorem totalQueries_ofQueryWithCost
    (localCost : Crypto.Infrastructure.Computation.Cost.Cost)
    (name : Spec.Name) :
    (ofQueryWithCost localCost name).totalQueries = 1 :=
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

/-- Embed a legacy natural-number profile into the generic profile type. -/
def toT (profile : OracleProfile Spec) :
    OracleProfileT Crypto.Infrastructure.Computation.Cost.natCostModel Spec :=
  ⟨profile.cost, profile.queryTrace⟩

/-- Project a natural-number generic profile back to the legacy profile type. -/
def ofT
    (profile :
      OracleProfileT Crypto.Infrastructure.Computation.Cost.natCostModel Spec) :
    OracleProfile Spec :=
  ⟨profile.cost, profile.queryTrace⟩

@[simp] theorem ofT_toT (profile : OracleProfile Spec) :
    ofT profile.toT = profile := by
  cases profile
  rfl

@[simp] theorem toT_ofT
    (profile :
      OracleProfileT Crypto.Infrastructure.Computation.Cost.natCostModel Spec) :
    toT (OracleProfile.ofT profile) = profile := by
  cases profile
  rfl

@[simp] theorem toT_zero :
    toT (zero Spec) =
      OracleProfileT.zero Crypto.Infrastructure.Computation.Cost.natCostModel Spec :=
  rfl

@[simp] theorem toT_append (left right : OracleProfile Spec) :
    toT (append left right) =
      OracleProfileT.append left.toT right.toT :=
  rfl

@[simp] theorem toT_ofCost (cost : Crypto.Infrastructure.Computation.Cost.Cost) :
    toT (ofCost (Spec := Spec) cost) = OracleProfileT.ofCost cost :=
  rfl

@[simp] theorem toT_ofQueryWithCost
    (localCost : Crypto.Infrastructure.Computation.Cost.Cost) (name : Spec.Name) :
    toT (ofQueryWithCost localCost name) =
      OracleProfileT.ofQueryWithCost localCost name :=
  rfl

@[simp] theorem cost_ofT
    (profile :
      OracleProfileT Crypto.Infrastructure.Computation.Cost.natCostModel Spec) :
    (OracleProfile.ofT profile).cost = profile.cost :=
  rfl

@[simp] theorem queryCount_ofT
    (profile :
      OracleProfileT Crypto.Infrastructure.Computation.Cost.natCostModel Spec)
    (name : Spec.Name) :
    (OracleProfile.ofT profile).queryCount name = profile.queryCount name :=
  rfl

@[simp] theorem totalQueries_ofT
    (profile :
      OracleProfileT Crypto.Infrastructure.Computation.Cost.natCostModel Spec) :
    (OracleProfile.ofT profile).totalQueries = profile.totalQueries :=
  rfl

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

/--
Embed the constructor-compatible legacy syntax into the generic-cost syntax.
All exact execution is routed through this translation.
-/
def toT {alpha : Type (max uValue uResponse)}
    (program : OracleProgram Spec alpha) :
    OracleProgramT Crypto.Infrastructure.Computation.Cost.natCostModel Spec alpha :=
  match program with
  | OracleProgram.pure value => OracleProgramT.pure value
  | OracleProgram.bind first next =>
      OracleProgramT.bind first.toT (fun value => (next value).toT)
  | OracleProgram.liftCosted dist => OracleProgramT.liftCosted dist
  | OracleProgram.query name oracleQuery =>
      OracleProgramT.queryWithCost
        (M := Crypto.Infrastructure.Computation.Cost.natCostModel)
        (1 : Nat) name oracleQuery

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
      Execution (OracleProgram.query name oracleQuery)
        (ULift.up response) (OracleProfile.ofQuery name)

/-- A legacy structural execution embeds into the generic natural-cost relation. -/
theorem Execution.toT
    {alpha : Type (max uValue uResponse)}
    {program : OracleProgram Spec alpha} {value : alpha}
    {profile : OracleProfile Spec}
    (execution : Execution program value profile) :
    OracleProgramT.Execution program.toT value profile.toT := by
  induction execution with
  | pure value =>
      exact OracleProgramT.Execution.pure value
  | @bind alpha beta first next firstValue value firstProfile nextProfile
      firstExecution nextExecution ihFirst ihNext =>
      exact
        OracleProgramT.Execution.bind
          (next := fun input => (next input).toT) ihFirst ihNext
  | liftCosted result_mem =>
      exact OracleProgramT.Execution.liftCosted result_mem
  | query name oracleQuery response =>
      exact
        OracleProgramT.Execution.queryWithCost
          (M := Crypto.Infrastructure.Computation.Cost.natCostModel)
          (1 : Nat) name oracleQuery response

/-- Every legacy query contributes one unit to the annotated execution cost. -/
theorem Execution.totalQueries_le_cost
    {alpha : Type (max uValue uResponse)}
    {program : OracleProgram Spec alpha} {value : alpha}
    {profile : OracleProfile Spec}
    (execution : Execution program value profile) :
    profile.totalQueries ≤ profile.cost := by
  induction execution with
  | pure returned =>
      exact Nat.le_refl 0
  | bind firstExecution nextExecution ihFirst ihNext =>
      exact
        (by
          simpa only [OracleProfile.totalQueries_append,
            OracleProfile.cost_append] using
            Nat.add_le_add ihFirst ihNext)
  | liftCosted result_mem =>
      exact Nat.zero_le _
  | query name oracleQuery response =>
      exact Nat.le_refl 1

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

/-- A uniform upper bound on the total number of oracle calls on every path. -/
def TotalQueryBound
    {α : Type (max uValue uResponse)}
    (program : OracleProgram Spec α) (bound : Nat) : Prop :=
  ∀ value profile, Execution program value profile →
    profile.totalQueries ≤ bound

/-- A profiled result of interpreting an oracle program. -/
structure RunResult
    (Spec : OracleSpec.{uOracle, uQuery, uResponse})
    (State : Type uState)
    (α : Type (max uValue uResponse)) where
  value : α
  state : State
  profile : OracleProfile Spec

namespace RunResult

/-- Project a generic natural-cost profiled result to its legacy packaging. -/
def ofT
    {State : Type uState} {alpha : Type (max uValue uResponse)}
    (result :
      OracleProgramT.RunResult
        Crypto.Infrastructure.Computation.Cost.natCostModel Spec State alpha) :
    RunResult Spec State alpha :=
  ⟨result.value, result.state, OracleProfile.ofT result.profile⟩

end RunResult

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
The recursive compatibility interpreter is exactly the projection of the
generic interpreter applied to the one-way translation `toT`.
-/
theorem map_ofT_runProfiled_toT
    {alpha : Type (max uValue uResponse)}
    (program : OracleProgram Spec alpha)
    (sec : Crypto.SecPar)
    (env : OracleEnv.{uOracle, uQuery, uResponse, uState} Spec)
    (state : env.State) :
    PMF.map RunResult.ofT
        (OracleProgramT.runProfiled program.toT sec env state) =
      runProfiled program sec env state := by
  induction program generalizing state with
  | pure value =>
      simp only [toT, OracleProgramT.runProfiled, runProfiled, PMF.pure_map,
        RunResult.ofT, OracleProfile.ofT]
      rfl
  | bind first next ihFirst ihNext =>
    simp only [toT, OracleProgramT.runProfiled, runProfiled,
      PMF.map_bind, PMF.pure_map]
    rw [← ihFirst state]
    refine Eq.trans ?_ (PMF.bind_map
      (OracleProgramT.runProfiled first.toT sec env state)
      RunResult.ofT
      (fun firstResult =>
        (runProfiled (next firstResult.value) sec env firstResult.state).bind
          fun nextResult =>
            PMF.pure
              ({
                value := nextResult.value
                state := nextResult.state
                profile :=
                  OracleProfile.append firstResult.profile nextResult.profile
              } : RunResult Spec env.State _))).symm
    congr 1
    funext firstResult
    simp only [Function.comp_apply, RunResult.ofT]
    rw [← ihNext firstResult.value firstResult.state]
    exact
      (PMF.bind_map
        (OracleProgramT.runProfiled
          (next firstResult.value).toT sec env firstResult.state)
        RunResult.ofT
        (fun nextResult =>
          PMF.pure
            ({
              value := nextResult.value
              state := nextResult.state
              profile :=
                OracleProfile.append
                  (OracleProfile.ofT firstResult.profile) nextResult.profile
            } : RunResult Spec env.State _))).symm
  | liftCosted dist =>
      simp only [toT, OracleProgramT.runProfiled, runProfiled,
        PMF.map_bind, PMF.pure_map]
      rfl
  | query name oracleQuery =>
      simp only [toT, OracleProgramT.runProfiled, runProfiled,
        PMF.map_bind, PMF.pure_map]
      rfl

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
    Crypto.Infrastructure.Computation.Cost.RandCostedT.valueDist,
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
  simp only [runWithEnv, runProfiled, PMF.pure_map]

end OracleProgram

end Crypto.Infrastructure.Computation.Oracle

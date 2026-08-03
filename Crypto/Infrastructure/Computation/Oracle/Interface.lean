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
## Cost-aware oracle programs

Oracle profiles and programs are parameterized by their exact cost model.
The query constructor receives its caller-side cost explicitly; query counts
remain a separate structural resource.
-/

/-- Resources accumulated along one oracle-program path in cost model `M`. -/
structure OracleProfile
    (M : Crypto.Infrastructure.Computation.Cost.CostModel.{uCost})
    (Spec : OracleSpec.{uOracle, uQuery, uResponse}) where
  cost : M.Cost
  queryTrace : List Spec.Name

namespace OracleProfile

open Crypto.Infrastructure.Computation.Cost

variable {M : CostModel.{uCost}}
variable {Spec : OracleSpec.{uOracle, uQuery, uResponse}}

/-- The empty generic execution profile. -/
def zero (M : CostModel.{uCost})
    (Spec : OracleSpec.{uOracle, uQuery, uResponse}) : OracleProfile M Spec := by
  letI := M.instAddMonoid
  exact ⟨0, []⟩

/-- Sequential profile composition, preserving left-to-right cost order. -/
def append (left right : OracleProfile M Spec) : OracleProfile M Spec := by
  letI := M.instAddMonoid
  exact ⟨left.cost + right.cost, left.queryTrace ++ right.queryTrace⟩

/-- Local work with no oracle queries. -/
def ofCost (cost : M.Cost) : OracleProfile M Spec :=
  ⟨cost, []⟩

/-- One oracle call with an explicit cost in the caller's cost model. -/
def ofQuery (localCost : M.Cost) (name : Spec.Name) :
    OracleProfile M Spec :=
  ⟨localCost, [name]⟩

@[simp] theorem cost_zero : (zero M Spec).cost = M.instAddMonoid.zero :=
  rfl

@[simp] theorem queryTrace_zero : (zero M Spec).queryTrace = [] :=
  rfl

@[simp] theorem cost_append (left right : OracleProfile M Spec) :
    (append left right).cost = M.instAddMonoid.add left.cost right.cost :=
  rfl

@[simp] theorem queryTrace_append (left right : OracleProfile M Spec) :
    (append left right).queryTrace = left.queryTrace ++ right.queryTrace :=
  rfl

@[simp] theorem cost_ofCost (cost : M.Cost) :
    (ofCost (Spec := Spec) cost).cost = cost :=
  rfl

@[simp] theorem queryTrace_ofCost (cost : M.Cost) :
    (ofCost (Spec := Spec) cost).queryTrace = [] :=
  rfl

@[simp] theorem cost_ofQuery (localCost : M.Cost) (name : Spec.Name) :
    (ofQuery localCost name).cost = localCost :=
  rfl

@[simp] theorem queryTrace_ofQuery
    (localCost : M.Cost) (name : Spec.Name) :
    (ofQuery localCost name).queryTrace = [name] :=
  rfl

/-- Number of calls to a fixed oracle name. -/
noncomputable def queryCount
    (profile : OracleProfile M Spec) (name : Spec.Name) : Nat := by
  classical
  exact profile.queryTrace.count name

/-- Total number of calls, deliberately separate from the modelled cost. -/
def totalQueries (profile : OracleProfile M Spec) : Nat :=
  profile.queryTrace.length

@[simp] theorem queryCount_zero (name : Spec.Name) :
    (zero M Spec).queryCount name = 0 := by
  classical
  simp [queryCount, zero]

@[simp] theorem queryCount_ofCost (cost : M.Cost) (name : Spec.Name) :
    (ofCost (Spec := Spec) cost).queryCount name = 0 := by
  classical
  simp [queryCount, ofCost]

@[simp] theorem queryCount_ofQuery_self
    (localCost : M.Cost) (name : Spec.Name) :
    (ofQuery localCost name).queryCount name = 1 := by
  classical
  simp [queryCount, ofQuery]

@[simp] theorem queryCount_ofQuery_of_ne
    (localCost : M.Cost) {queried name : Spec.Name} (hne : queried ≠ name) :
    (ofQuery localCost queried).queryCount name = 0 := by
  classical
  simp [queryCount, ofQuery, hne]

@[simp] theorem totalQueries_zero : (zero M Spec).totalQueries = 0 :=
  rfl

@[simp] theorem totalQueries_ofCost (cost : M.Cost) :
    (ofCost (Spec := Spec) cost).totalQueries = 0 :=
  rfl

@[simp] theorem totalQueries_ofQuery
    (localCost : M.Cost) (name : Spec.Name) :
    (ofQuery localCost name).totalQueries = 1 :=
  rfl

@[simp] theorem queryCount_append
    (left right : OracleProfile M Spec) (name : Spec.Name) :
    (append left right).queryCount name =
      left.queryCount name + right.queryCount name := by
  classical
  simp [queryCount, append]

@[simp] theorem totalQueries_append (left right : OracleProfile M Spec) :
    (append left right).totalQueries =
      left.totalQueries + right.totalQueries := by
  simp [totalQueries, append]

theorem queryCount_le_totalQueries
    (profile : OracleProfile M Spec) (name : Spec.Name) :
    profile.queryCount name ≤ profile.totalQueries := by
  classical
  exact List.count_le_length

end OracleProfile

/-- An adaptive oracle program whose local paths carry costs from `M`. -/
inductive OracleProgram
    (M : Crypto.Infrastructure.Computation.Cost.CostModel.{uCost})
    (Spec : OracleSpec.{uOracle, uQuery, uResponse}) :
    Type (max uValue uResponse) →
      Type (max (uCost + 1) (uOracle + 1) uQuery (uResponse + 1) (uValue + 1)) where
  | pure {α : Type (max uValue uResponse)} : α → OracleProgram M Spec α
  | bind {α : Type (max uValue uResponse)} {β : Type (max uValue uResponse)} :
      OracleProgram M Spec α → (α → OracleProgram M Spec β) →
        OracleProgram M Spec β
  | liftCosted {α : Type (max uValue uResponse)} :
      Crypto.Infrastructure.Computation.Cost.RandCostedT M α →
        OracleProgram M Spec α
  | query
      (localCost : M.Cost) (name : Spec.Name) :
      Spec.Query name → OracleProgram M Spec (ULift.{uValue} (Spec.Response name))

namespace OracleProgram

open Crypto.Infrastructure.Computation.Cost

variable {M : CostModel.{uCost}}
variable {Spec : OracleSpec.{uOracle, uQuery, uResponse}}

instance : Monad (OracleProgram M Spec) where
  pure := fun value => OracleProgram.pure value
  bind := fun program next => OracleProgram.bind program next

/--
Replace every caller-side oracle-query cost by one while preserving the
program's typed control flow and all non-query randomized work.

This is a specialization of the cost-aware oracle language, not a second
oracle-program representation or interpreter.
-/
def withUnitQueryCost :
    {α : Type (max uValue uResponse)} →
      OracleProgram CostModel.nat Spec α →
        OracleProgram CostModel.nat Spec α
  | _, OracleProgram.pure value => OracleProgram.pure value
  | _, OracleProgram.bind first next =>
      OracleProgram.bind (withUnitQueryCost first)
        (fun value => withUnitQueryCost (next value))
  | _, OracleProgram.liftCosted dist => OracleProgram.liftCosted dist
  | _, OracleProgram.query _localCost name oracleQuery =>
      OracleProgram.query (M := CostModel.nat) 1 name oracleQuery

/-- Abstract generic-cost execution paths, independent of an environment. -/
inductive Execution :
    {α : Type (max uValue uResponse)} →
    OracleProgram M Spec α → α → OracleProfile M Spec → Prop where
  | pure {α : Type (max uValue uResponse)} (value : α) :
      Execution (OracleProgram.pure value) value (OracleProfile.zero M Spec)
  | bind
      {α : Type (max uValue uResponse)} {β : Type (max uValue uResponse)}
      {first : OracleProgram M Spec α} {next : α → OracleProgram M Spec β}
      {firstValue : α} {value : β}
      {firstProfile nextProfile : OracleProfile M Spec}
      (firstExecution : Execution first firstValue firstProfile)
      (nextExecution : Execution (next firstValue) value nextProfile) :
      Execution (OracleProgram.bind first next) value
        (OracleProfile.append firstProfile nextProfile)
  | liftCosted
      {α : Type (max uValue uResponse)}
      {dist : RandCostedT M α} {result : CostedT M α}
      (result_mem : result ∈ dist.support) :
      Execution (OracleProgram.liftCosted dist) result.val
        (OracleProfile.ofCost result.cost)
  | query
      (localCost : M.Cost) (name : Spec.Name) (oracleQuery : Spec.Query name)
      (response : Spec.Response name) :
      Execution (OracleProgram.query localCost name oracleQuery)
        (ULift.up response) (OracleProfile.ofQuery localCost name)

/-- Every oracle query in a natural-cost program is charged at least one. -/
def QueriesCostAtLeastOne :
    {α : Type (max uValue uResponse)} →
      OracleProgram CostModel.nat Spec α → Prop
  | _, OracleProgram.pure _value => True
  | _, OracleProgram.bind first next =>
      QueriesCostAtLeastOne first ∧
        ∀ value, QueriesCostAtLeastOne (next value)
  | _, OracleProgram.liftCosted _dist => True
  | _, OracleProgram.query localCost _name _oracleQuery => 1 ≤ localCost

/-- Unit-query-cost specialization charges every query at least one. -/
theorem queriesCostAtLeastOne_withUnitQueryCost
    {α : Type (max uValue uResponse)}
    (program : OracleProgram CostModel.nat Spec α) :
    QueriesCostAtLeastOne (withUnitQueryCost program) := by
  induction program with
  | pure value =>
      trivial
  | bind first next ihFirst ihNext =>
      exact ⟨ihFirst, ihNext⟩
  | liftCosted dist =>
      trivial
  | query localCost name oracleQuery =>
      exact Nat.le_refl 1

/-- Query count is bounded by path cost whenever every query costs at least one. -/
theorem Execution.totalQueries_le_cost_of_queriesCostAtLeastOne
    {α : Type (max uValue uResponse)}
    {program : OracleProgram CostModel.nat Spec α}
    {value : α} {profile : OracleProfile CostModel.nat Spec}
    (execution : Execution program value profile)
    (queriesCostAtLeastOne : QueriesCostAtLeastOne program) :
    profile.totalQueries ≤ profile.cost := by
  induction execution with
  | pure value =>
      exact Nat.zero_le 0
  | bind firstExecution nextExecution ihFirst ihNext =>
      simpa using Nat.add_le_add
        (ihFirst queriesCostAtLeastOne.1)
        (ihNext (queriesCostAtLeastOne.2 _))
  | liftCosted result_mem =>
      exact Nat.zero_le _
  | query localCost name oracleQuery response =>
      exact queriesCostAtLeastOne

/--
Every execution of the unit-query-cost specialization charges at least one
natural-number cost unit per oracle query.  Costs of `liftCosted` nodes remain
additional local work, so the result is an inequality rather than an equality.
-/
theorem totalQueries_le_cost_withUnitQueryCost
    {α : Type (max uValue uResponse)}
    (program : OracleProgram CostModel.nat Spec α)
    {value : α} {profile : OracleProfile CostModel.nat Spec}
    (execution : Execution (withUnitQueryCost program) value profile) :
    profile.totalQueries ≤ profile.cost := by
  exact execution.totalQueries_le_cost_of_queriesCostAtLeastOne
    (queriesCostAtLeastOne_withUnitQueryCost program)

/-- Upper bound on every local-cost path. -/
def CostBound {α : Type (max uValue uResponse)}
    (program : OracleProgram M Spec α) (bound : M.Cost) : Prop :=
  ∀ value profile, Execution program value profile →
    M.instPartialOrder.le profile.cost bound

/-- Per-name query bounds stay natural-number structural resources. -/
def QueryBound {α : Type (max uValue uResponse)}
    (program : OracleProgram M Spec α) (bound : Spec.Name → Nat) : Prop :=
  ∀ value profile, Execution program value profile →
    ∀ name, profile.queryCount name ≤ bound name

/-- Total query bounds stay independent of local runtime. -/
def TotalQueryBound {α : Type (max uValue uResponse)}
    (program : OracleProgram M Spec α) (bound : Nat) : Prop :=
  ∀ value profile, Execution program value profile →
    profile.totalQueries ≤ bound

/--
For the unit-query-cost specialization, any natural-number cost bound is also
a total-query bound.
-/
theorem totalQueryBound_withUnitQueryCost_of_costBound
    {α : Type (max uValue uResponse)}
    (program : OracleProgram CostModel.nat Spec α) (bound : Nat)
    (costBound : CostBound (withUnitQueryCost program) bound) :
    TotalQueryBound (withUnitQueryCost program) bound := by
  intro value profile execution
  exact (totalQueries_le_cost_withUnitQueryCost program execution).trans
    (costBound value profile execution)

/-- A generic-cost profiled interpreter result. -/
structure RunResult
    (M : CostModel.{uCost}) (Spec : OracleSpec.{uOracle, uQuery, uResponse})
    (State : Type uState) (α : Type (max uValue uResponse)) where
  value : α
  state : State
  profile : OracleProfile M Spec

/-- Interpret a generic-cost oracle program and retain local cost and trace. -/
noncomputable def runProfiled
    {α : Type (max uValue uResponse)} (program : OracleProgram M Spec α)
    (sec : Crypto.SecPar)
    (env : OracleEnv.{uOracle, uQuery, uResponse, uState} Spec)
    (state : env.State) : PMF (RunResult M Spec env.State α) :=
  match program with
  | OracleProgram.pure value =>
      PMF.pure ⟨value, state, OracleProfile.zero M Spec⟩
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
  | OracleProgram.query localCost name oracleQuery =>
      PMF.bind (env.query name sec state oracleQuery) fun result =>
        PMF.pure
          ⟨ULift.up result.1, result.2,
            OracleProfile.ofQuery localCost name⟩

/--
Changing only explicit query charges does not affect any continuation that
observes the returned value and state but not the execution profile.
-/
theorem bind_runProfiled_withUnitQueryCost
    {α β : Type (max uValue uResponse)}
    (program : OracleProgram CostModel.nat Spec α)
    (sec : Crypto.SecPar)
    (env : OracleEnv.{uOracle, uQuery, uResponse, uState} Spec)
    (state : env.State) (continuation : α → env.State → PMF β) :
    PMF.bind
        (runProfiled (withUnitQueryCost program) sec env state)
        (fun result => continuation result.value result.state) =
      PMF.bind (runProfiled program sec env state)
        (fun result => continuation result.value result.state) := by
  induction program generalizing state with
  | pure value =>
      simp [withUnitQueryCost, runProfiled]
  | bind first next ihFirst ihNext =>
      simp only [withUnitQueryCost, runProfiled, PMF.bind_bind, PMF.pure_bind]
      calc
        PMF.bind (runProfiled (withUnitQueryCost first) sec env state)
            (fun firstResult =>
              PMF.bind
                (runProfiled
                  (withUnitQueryCost (next firstResult.value)) sec env
                  firstResult.state)
                (fun nextResult =>
                  continuation nextResult.value nextResult.state)) =
          PMF.bind (runProfiled (withUnitQueryCost first) sec env state)
            (fun firstResult =>
              PMF.bind
                (runProfiled (next firstResult.value) sec env firstResult.state)
                (fun nextResult =>
                  continuation nextResult.value nextResult.state)) := by
            congr 1
            funext firstResult
            exact ihNext firstResult.value firstResult.state continuation
        _ =
          PMF.bind (runProfiled first sec env state)
            (fun firstResult =>
              PMF.bind
                (runProfiled (next firstResult.value) sec env firstResult.state)
                (fun nextResult =>
                  continuation nextResult.value nextResult.state)) := by
            exact ihFirst state (fun firstValue firstState =>
              PMF.bind (runProfiled (next firstValue) sec env firstState)
                (fun nextResult =>
                  continuation nextResult.value nextResult.state))
  | liftCosted dist =>
      simp [withUnitQueryCost, runProfiled, PMF.bind_bind]
  | query localCost name oracleQuery =>
      simp [withUnitQueryCost, runProfiled, PMF.bind_bind]

theorem execution_of_mem_support_runProfiled
    {α : Type (max uValue uResponse)} (program : OracleProgram M Spec α)
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
  | query localCost name oracleQuery =>
      simp only [runProfiled] at hresult
      rw [PMF.mem_support_bind_iff] at hresult
      rcases hresult with ⟨oracleResult, _horacleResult, hresult⟩
      rw [PMF.mem_support_pure_iff] at hresult
      subst result
      exact Execution.query localCost name oracleQuery oracleResult.1

/-- Run from the initial state and retain the full generic profile. -/
noncomputable def runProfiledWithEnv
    {α : Type (max uValue uResponse)} (program : OracleProgram M Spec α)
    (sec : Crypto.SecPar)
    (env : OracleEnv.{uOracle, uQuery, uResponse, uState} Spec) :
    PMF (RunResult M Spec env.State α) :=
  runProfiled program sec env env.init

/-- Run from the initial state and retain only the returned value. -/
noncomputable def runWithEnv
    {α : Type (max uValue uResponse)} (program : OracleProgram M Spec α)
    (sec : Crypto.SecPar)
    (env : OracleEnv.{uOracle, uQuery, uResponse, uState} Spec) : PMF α :=
  PMF.map RunResult.value (runProfiled program sec env env.init)

/-- Replacing query charges by one preserves the oracle program's value law. -/
@[simp] theorem runWithEnv_withUnitQueryCost
    {α : Type (max uValue uResponse)}
    (program : OracleProgram CostModel.nat Spec α)
    (sec : Crypto.SecPar)
    (env : OracleEnv.{uOracle, uQuery, uResponse, uState} Spec) :
    runWithEnv (withUnitQueryCost program) sec env =
      runWithEnv program sec env := by
  simpa only [runWithEnv, PMF.bind_pure_comp, Function.comp_apply] using
    bind_runProfiled_withUnitQueryCost program sec env env.init
      (fun value _state => PMF.pure value)

/-- Retain the generic local path cost while forgetting the final state. -/
noncomputable def runCostedWithEnv
    {α : Type (max uValue uResponse)} (program : OracleProgram M Spec α)
    (sec : Crypto.SecPar)
    (env : OracleEnv.{uOracle, uQuery, uResponse, uState} Spec) :
    RandCostedT M α :=
  PMF.map (fun result => ⟨result.value, result.profile.cost⟩)
    (runProfiledWithEnv program sec env)

@[simp] theorem valueDist_runCostedWithEnv
    {α : Type (max uValue uResponse)} (program : OracleProgram M Spec α)
    (sec : Crypto.SecPar)
    (env : OracleEnv.{uOracle, uQuery, uResponse, uState} Spec) :
    RandCostedT.valueDist (runCostedWithEnv program sec env) =
      runWithEnv program sec env := by
  simp only [RandCostedT.valueDist, runCostedWithEnv, runProfiledWithEnv,
    runWithEnv, PMF.map_comp]
  rfl

end OracleProgram

end Crypto.Infrastructure.Computation.Oracle

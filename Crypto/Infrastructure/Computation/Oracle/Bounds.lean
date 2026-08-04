import Crypto.Infrastructure.Computation.Algebra.Bounds
import Crypto.Infrastructure.Computation.Cost.PathBound
import Crypto.Infrastructure.Computation.Oracle.Interpreter

namespace Crypto.Infrastructure.Computation.Oracle

open Crypto.Infrastructure.Computation.Algebra
open Crypto.Infrastructure.Computation.Cost

universe uCost uOracle uQuery uResponse uState uValue

namespace CostedOracleEnv

variable {M : CostModel.{uCost}}
variable {Spec : OracleSpec.{uOracle, uQuery, uResponse}}

/-- Every internal query path is bounded by `budget`. -/
def QueryCostBound
    (env : CostedOracleEnv.{uCost, uOracle, uQuery, uResponse, uState} M Spec)
    (budget : Crypto.SecPar → M.Cost) : Prop :=
  ∀ name sec state query,
    RandCosted.CostBound (env.query name sec state query) (budget sec)

/-- Internal query paths at one fixed security parameter are bounded by `budget`. -/
def QueryCostBoundAt
    (env : CostedOracleEnv.{uCost, uOracle, uQuery, uResponse, uState} M Spec)
    (sec : Crypto.SecPar) (budget : M.Cost) : Prop :=
  ∀ name state query,
    RandCosted.CostBound (env.query name sec state query) budget

theorem QueryCostBound.at
    {env : CostedOracleEnv.{uCost, uOracle, uQuery, uResponse, uState} M Spec}
    {budget : Crypto.SecPar → M.Cost}
    (bound : env.QueryCostBound budget) (sec : Crypto.SecPar) :
    env.QueryCostBoundAt sec (budget sec) :=
  fun name state query => bound name sec state query

end CostedOracleEnv

namespace QueryIssue

/--
The independent exact-cost certificate for an explicit query-issuance handler.

The handler remains the sole source of exact cost; this declaration merely
certifies that its unique supported result is bounded by that same cost.
-/
noncomputable def costBounds
    (M : CostModel.{uCost}) (Spec : OracleSpec.{uOracle, uQuery, uResponse})
    (cost : (name : Spec.Name) → Spec.Query name → M.Cost) :
    OperationBounds (costAlgebra M Spec cost) where
  budget operation :=
    match operation with
    | .issue name query => cost name query
  cost_le operation result hresult := by
    cases operation with
    | issue name query =>
        simp only [costAlgebra, RandCosted.liftCosted,
          PMF.mem_support_pure_iff] at hresult
        subst result
        exact M.instPartialOrder.le_refl (cost name query)

end QueryIssue

namespace Program

variable {M : CostModel.{uCost}}
variable {Spec : OracleSpec.{uOracle, uQuery, uResponse}}
variable {issueAlgebra : CostedAlgebra M (QueryIssue.signature Spec)}

/--
An environment-independent possible path through an oracle program.

Oracle responses are deliberately unconstrained, while caller-side randomized
work and query-issuance costs must occur in their exact handler supports.  This
relation therefore overapproximates executions against any concrete environment.
-/
inductive PossibleExecution :
    {α : Type (max uValue uResponse)} →
      Program issueAlgebra α → α → M.Cost → QueryTrace Spec → Prop where
  | pure {α : Type (max uValue uResponse)} (value : α) :
      PossibleExecution (.pure value) value M.instAddMonoid.zero
        (QueryTrace.empty Spec)
  | bind
      {α β : Type (max uValue uResponse)}
      {first : Program issueAlgebra α} {next : α → Program issueAlgebra β}
      {firstValue : α} {value : β}
      {firstCost nextCost : M.Cost}
      {firstTrace nextTrace : QueryTrace Spec}
      (firstExecution : PossibleExecution first firstValue firstCost firstTrace)
      (nextExecution : PossibleExecution (next firstValue) value nextCost nextTrace) :
      PossibleExecution (.bind first next) value
        (M.instAddMonoid.add firstCost nextCost)
        (QueryTrace.append firstTrace nextTrace)
  | liftCosted
      {α : Type (max uValue uResponse)}
      {dist : RandCosted M α} {result : Costed M α}
      (result_mem : result ∈ dist.support) :
      PossibleExecution (.liftCosted dist) result.val result.cost
        (QueryTrace.empty Spec)
  | query
      (name : Spec.Name) (oracleQuery : Spec.Query name)
      (issueResult : Costed M Unit)
      (issueResult_mem :
        issueResult ∈ (issueAlgebra.exec (.issue name oracleQuery)).support)
      (response : Spec.Response name) :
      PossibleExecution (.query name oracleQuery) (ULift.up response)
        issueResult.cost (QueryTrace.singleton name)

/-- Every supported exact run yields an environment-independent possible path. -/
theorem possibleExecution_of_mem_support_runExact
    {α : Type (max uValue uResponse)} (program : Program issueAlgebra α)
    (sec : Crypto.SecPar)
    (env : CostedOracleEnv.{uCost, uOracle, uQuery, uResponse, uState} M Spec)
    (state : env.State) (result : ExactRunResult M Spec env.State α)
    (hresult : result ∈ (runExact program sec env state).support) :
    PossibleExecution program result.value result.localCost result.trace := by
  induction program generalizing state with
  | pure value =>
      simp only [runExact] at hresult
      rw [PMF.mem_support_pure_iff] at hresult
      subst result
      exact PossibleExecution.pure value
  | bind first next ihFirst ihNext =>
      simp only [runExact] at hresult
      rw [PMF.mem_support_bind_iff] at hresult
      rcases hresult with ⟨firstResult, hfirstResult, hnextResult⟩
      rw [PMF.mem_support_bind_iff] at hnextResult
      rcases hnextResult with ⟨nextResult, hnextResult, hresult⟩
      rw [PMF.mem_support_pure_iff] at hresult
      subst result
      exact PossibleExecution.bind
        (ihFirst state firstResult hfirstResult)
        (ihNext firstResult.value firstResult.state nextResult hnextResult)
  | liftCosted dist =>
      simp only [runExact] at hresult
      rw [PMF.mem_support_bind_iff] at hresult
      rcases hresult with ⟨costedResult, hcostedResult, hresult⟩
      rw [PMF.mem_support_pure_iff] at hresult
      subst result
      exact PossibleExecution.liftCosted hcostedResult
  | query name oracleQuery =>
      simp only [runExact] at hresult
      rw [PMF.mem_support_bind_iff] at hresult
      rcases hresult with ⟨issueResult, hissueResult, horacleResult⟩
      rw [PMF.mem_support_bind_iff] at horacleResult
      rcases horacleResult with ⟨oracleResult, _horacleResult, hresult⟩
      rw [PMF.mem_support_pure_iff] at hresult
      subst result
      exact PossibleExecution.query name oracleQuery issueResult hissueResult
        oracleResult.val.1

/-- An upper bound on caller-local cost for every possible path. -/
def LocalCostBound
    {α : Type (max uValue uResponse)}
    (program : Program issueAlgebra α) (budget : M.Cost) : Prop :=
  ∀ value cost trace, PossibleExecution program value cost trace →
    M.instPartialOrder.le cost budget

/-- A per-name bound on query counts for every possible path. -/
def QueryBound
    {α : Type (max uValue uResponse)}
    (program : Program issueAlgebra α) (budget : Spec.Name → Nat) : Prop :=
  ∀ value cost trace, PossibleExecution program value cost trace →
    ∀ name, trace.count name ≤ budget name

/-- A bound on the total number of queries for every possible path. -/
def TotalQueryBound
    {α : Type (max uValue uResponse)}
    (program : Program issueAlgebra α) (budget : Nat) : Prop :=
  ∀ value cost trace, PossibleExecution program value cost trace →
    trace.total ≤ budget

namespace LocalCostBound

variable {α : Type (max uValue uResponse)}

/-- Pure programs have zero caller-local cost. -/
theorem pure
    (value : α) :
    LocalCostBound (Program.pure value : Program issueAlgebra α)
      M.instAddMonoid.zero := by
  intro _value _cost _trace execution
  cases execution
  exact M.instPartialOrder.le_refl M.instAddMonoid.zero

/-- Sequential local bounds compose in execution order. -/
theorem bind
    {β : Type (max uValue uResponse)}
    {first : Program issueAlgebra α} {next : α → Program issueAlgebra β}
    {firstBudget nextBudget : M.Cost}
    (firstBound : LocalCostBound first firstBudget)
    (nextBound : ∀ value, LocalCostBound (next value) nextBudget) :
    LocalCostBound (.bind first next)
      (M.instAddMonoid.add firstBudget nextBudget) := by
  intro _value _cost _trace execution
  cases execution with
  | bind firstExecution nextExecution =>
      exact
        @add_le_add M.Cost M.instAddMonoid.toAdd
          M.instPartialOrder.toPreorder M.instAddLeftMono M.instAddRightMono
          _ _ _ _
          (firstBound _ _ _ firstExecution)
          (nextBound _ _ _ _ nextExecution)

/-- A lifted randomized computation keeps its independent path-cost bound. -/
theorem liftCosted
    {dist : RandCosted M α} {budget : M.Cost}
    (bound : RandCosted.CostBound dist budget) :
    LocalCostBound (.liftCosted dist : Program issueAlgebra α) budget := by
  intro _value _cost _trace execution
  cases execution with
  | liftCosted result_mem => exact bound _ result_mem

/-- A caller-local certificate remains valid at any larger exact budget. -/
theorem weaken
    {program : Program issueAlgebra α} {budget largerBudget : M.Cost}
    (bound : LocalCostBound program budget)
    (budget_le : M.instPartialOrder.le budget largerBudget) :
    LocalCostBound program largerBudget := by
  letI := M.instPartialOrder
  intro value cost trace execution
  exact (bound value cost trace execution).trans budget_le

end LocalCostBound

namespace QueryBound

variable {α : Type (max uValue uResponse)}

/-- Pure programs issue no query of any name. -/
theorem pure
    (value : α) :
    QueryBound (Program.pure value : Program issueAlgebra α)
      (fun _name => 0) := by
  intro _value _cost _trace execution name
  cases execution
  exact Nat.le_refl 0

/-- Lifted local work issues no query of any name. -/
theorem liftCosted
    (dist : RandCosted M α) :
    QueryBound (.liftCosted dist : Program issueAlgebra α)
      (fun _name => 0) := by
  intro _value _cost _trace execution name
  cases execution
  exact Nat.le_refl 0

/-- Sequential per-name query bounds add pointwise. -/
theorem bind
    {β : Type (max uValue uResponse)}
    {first : Program issueAlgebra α} {next : α → Program issueAlgebra β}
    {firstBudget nextBudget : Spec.Name → Nat}
    (firstBound : QueryBound first firstBudget)
    (nextBound : ∀ value, QueryBound (next value) nextBudget) :
    QueryBound (.bind first next)
      (fun name => firstBudget name + nextBudget name) := by
  intro _value _cost _trace execution name
  cases execution with
  | bind firstExecution nextExecution =>
      simpa only [QueryTrace.count_append] using
        Nat.add_le_add
          (firstBound _ _ _ firstExecution name)
          (nextBound _ _ _ _ nextExecution name)

end QueryBound

namespace TotalQueryBound

variable {α : Type (max uValue uResponse)}

/-- Pure programs issue no queries. -/
theorem pure
    (value : α) :
    TotalQueryBound (Program.pure value : Program issueAlgebra α) 0 := by
  intro _value _cost _trace execution
  cases execution
  exact Nat.le_refl 0

/-- Lifted local randomized computations issue no queries. -/
theorem liftCosted
    (dist : RandCosted M α) :
    TotalQueryBound (.liftCosted dist : Program issueAlgebra α) 0 := by
  intro _value _cost _trace execution
  cases execution
  exact Nat.le_refl 0

/-- Sequential total-query bounds add. -/
theorem bind
    {β : Type (max uValue uResponse)}
    {first : Program issueAlgebra α} {next : α → Program issueAlgebra β}
    {firstBudget nextBudget : Nat}
    (firstBound : TotalQueryBound first firstBudget)
    (nextBound : ∀ value, TotalQueryBound (next value) nextBudget) :
    TotalQueryBound (.bind first next) (firstBudget + nextBudget) := by
  intro _value _cost _trace execution
  cases execution with
  | bind firstExecution nextExecution =>
      simpa only [QueryTrace.total_append] using
        Nat.add_le_add
          (firstBound _ _ _ firstExecution)
          (nextBound _ _ _ _ nextExecution)

end TotalQueryBound

variable {α : Type (max uValue uResponse)}

/-- A total-query certificate induces the corresponding uniform per-name bound. -/
theorem QueryBound.ofTotal
    {program : Program issueAlgebra α} {budget : Nat}
    (bound : TotalQueryBound program budget) :
    QueryBound program (fun _name => budget) := by
  intro value cost trace execution name
  exact (trace.count_le_total name).trans (bound value cost trace execution)

/-- Every supported exact run respects a certified caller-local bound. -/
theorem localCost_le_of_mem_support_runExact
    {program : Program issueAlgebra α}
    {budget : M.Cost} (bound : LocalCostBound program budget)
    (sec : Crypto.SecPar)
    (env : CostedOracleEnv.{uCost, uOracle, uQuery, uResponse, uState} M Spec)
    (state : env.State) (result : ExactRunResult M Spec env.State α)
    (hresult : result ∈ (runExact program sec env state).support) :
    M.instPartialOrder.le result.localCost budget :=
  bound result.value result.localCost result.trace
    (possibleExecution_of_mem_support_runExact program sec env state result hresult)

/-- Every supported exact run respects all certified per-name query bounds. -/
theorem queryCount_le_of_mem_support_runExact
    {program : Program issueAlgebra α}
    {budget : Spec.Name → Nat} (bound : QueryBound program budget)
    (sec : Crypto.SecPar)
    (env : CostedOracleEnv.{uCost, uOracle, uQuery, uResponse, uState} M Spec)
    (state : env.State) (result : ExactRunResult M Spec env.State α)
    (hresult : result ∈ (runExact program sec env state).support)
    (name : Spec.Name) :
    result.trace.count name ≤ budget name :=
  bound result.value result.localCost result.trace
    (possibleExecution_of_mem_support_runExact program sec env state result hresult) name

/-- Every supported exact run respects a certified total-query bound. -/
theorem totalQueries_le_of_mem_support_runExact
    {program : Program issueAlgebra α}
    {budget : Nat} (bound : TotalQueryBound program budget)
    (sec : Crypto.SecPar)
    (env : CostedOracleEnv.{uCost, uOracle, uQuery, uResponse, uState} M Spec)
    (state : env.State) (result : ExactRunResult M Spec env.State α)
    (hresult : result ∈ (runExact program sec env state).support) :
    result.trace.total ≤ budget :=
  bound result.value result.localCost result.trace
    (possibleExecution_of_mem_support_runExact program sec env state result hresult)

end Program

end Crypto.Infrastructure.Computation.Oracle

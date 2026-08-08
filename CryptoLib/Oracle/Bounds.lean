import CryptoLib.Core.Infrastructure.Computation.Cost.PathBound
import CryptoLib.Oracle.Interpreter

namespace CryptoLib.Oracle

open CryptoLib.Core.Infrastructure.Computation.Cost

universe uCost uOracle uQuery uResponse uState uValue

namespace CostedOracleEnv

variable {M : CostModel.{uCost}}
variable {Spec : OracleSpec.{uOracle, uQuery, uResponse}}

/-- Every internal query path is bounded by `budget`. -/
def QueryCostBound
    (env : CostedOracleEnv.{uCost, uOracle, uQuery, uResponse, uState} M Spec)
    (budget : CryptoLib.Core.SecPar → M.Cost) : Prop :=
  ∀ name sec state query,
    RandCosted.CostBound (env.query name sec state query) (budget sec)

/-- Internal query paths at one fixed security parameter are bounded by `budget`. -/
def QueryCostBoundAt
    (env : CostedOracleEnv.{uCost, uOracle, uQuery, uResponse, uState} M Spec)
    (sec : CryptoLib.Core.SecPar) (budget : M.Cost) : Prop :=
  ∀ name state query,
    RandCosted.CostBound (env.query name sec state query) budget

theorem QueryCostBound.at
    {env : CostedOracleEnv.{uCost, uOracle, uQuery, uResponse, uState} M Spec}
    {budget : CryptoLib.Core.SecPar → M.Cost}
    (bound : env.QueryCostBound budget) (sec : CryptoLib.Core.SecPar) :
    env.QueryCostBoundAt sec (budget sec) :=
  fun name state query => bound name sec state query

end CostedOracleEnv

namespace Program

variable {M : CostModel.{uCost}}
variable {Spec : OracleSpec.{uOracle, uQuery, uResponse}}
variable {issueCost : (name : Spec.Name) → Spec.Query name → M.Cost}

/--
An environment-independent possible path through an oracle program.

Oracle responses are deliberately unconstrained, while caller-side randomized
work and query-issuance costs must occur in their exact handler supports.  This
relation therefore overapproximates executions against any concrete environment.
-/
inductive PossibleExecution :
    {α : Type (max uValue uResponse)} →
      Program issueCost α → α → M.Cost → QueryTrace Spec → Prop where
  | pure {α : Type (max uValue uResponse)} (value : α) :
      PossibleExecution (.pure value) value M.instAddMonoid.zero
        (QueryTrace.empty Spec)
  | bind
      {α β : Type (max uValue uResponse)}
      {first : Program issueCost α} {next : α → Program issueCost β}
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
      (response : Spec.Response name) :
      PossibleExecution (.query name oracleQuery) (ULift.up response)
        (issueCost name oracleQuery) (QueryTrace.singleton name)

variable
    {α β : Type (max uValue uResponse)}
    {first : Program issueCost α} {next : α → Program issueCost β}

/-- Every supported exact run yields an environment-independent possible path. -/
theorem possibleExecution_of_mem_support_runExact
    (program : Program issueCost α)
    (sec : CryptoLib.Core.SecPar)
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
      rcases hresult with ⟨oracleResult, _horacleResult, hresult⟩
      rw [PMF.mem_support_pure_iff] at hresult
      subst result
      exact PossibleExecution.query name oracleQuery oracleResult.val.1

/-- An upper bound on caller-local cost for every possible path. -/
def LocalCostBound
    (program : Program issueCost α) (budget : M.Cost) : Prop :=
  ∀ value cost trace, PossibleExecution program value cost trace →
    M.instPartialOrder.le cost budget

/-- A per-name bound on query counts for every possible path. -/
def QueryBound
    (program : Program issueCost α) (budget : Spec.Name → Nat) : Prop :=
  ∀ value cost trace, PossibleExecution program value cost trace →
    ∀ name, trace.count name ≤ budget name

/-- A bound on the total number of queries for every possible path. -/
def TotalQueryBound
    (program : Program issueCost α) (budget : Nat) : Prop :=
  ∀ value cost trace, PossibleExecution program value cost trace →
    trace.total ≤ budget

namespace LocalCostBound

/-- Pure programs have zero caller-local cost. -/
theorem pure
    (value : α) :
    LocalCostBound (Program.pure value : Program issueCost α)
      M.instAddMonoid.zero := by
  intro _value _cost _trace execution
  cases execution
  exact M.instPartialOrder.le_refl M.instAddMonoid.zero

/-- Sequential local bounds compose in execution order. -/
theorem bind
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
    LocalCostBound (.liftCosted dist : Program issueCost α) budget := by
  intro _value _cost _trace execution
  cases execution with
  | liftCosted result_mem => exact bound _ result_mem

/-- A caller-local certificate remains valid at any larger exact budget. -/
theorem weaken
    {program : Program issueCost α} {budget largerBudget : M.Cost}
    (bound : LocalCostBound program budget)
    (budget_le : M.instPartialOrder.le budget largerBudget) :
    LocalCostBound program largerBudget := by
  letI := M.instPartialOrder
  intro value cost trace execution
  exact (bound value cost trace execution).trans budget_le

end LocalCostBound

namespace QueryBound

/-- Pure programs issue no query of any name. -/
theorem pure
    (value : α) :
    QueryBound (Program.pure value : Program issueCost α)
      (fun _name => 0) := by
  intro _value _cost _trace execution name
  cases execution
  exact Nat.le_refl 0

/-- Lifted local work issues no query of any name. -/
theorem liftCosted
    (dist : RandCosted M α) :
    QueryBound (.liftCosted dist : Program issueCost α)
      (fun _name => 0) := by
  intro _value _cost _trace execution name
  cases execution
  exact Nat.le_refl 0

/-- Sequential per-name query bounds add pointwise. -/
theorem bind
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

/-- Pure programs issue no queries. -/
theorem pure
    (value : α) :
    TotalQueryBound (Program.pure value : Program issueCost α) 0 := by
  intro _value _cost _trace execution
  cases execution
  exact Nat.le_refl 0

/-- Lifted local randomized computations issue no queries. -/
theorem liftCosted
    (dist : RandCosted M α) :
    TotalQueryBound (.liftCosted dist : Program issueCost α) 0 := by
  intro _value _cost _trace execution
  cases execution
  exact Nat.le_refl 0

/-- Sequential total-query bounds add. -/
theorem bind
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

variable {program : Program issueCost α}

/-- A total-query certificate induces the corresponding uniform per-name bound. -/
theorem QueryBound.ofTotal
    {budget : Nat}
    (bound : TotalQueryBound program budget) :
    QueryBound program (fun _name => budget) := by
  intro value cost trace execution name
  exact (trace.count_le_total name).trans (bound value cost trace execution)

/-- Every supported exact run respects a certified caller-local bound. -/
theorem localCost_le_of_mem_support_runExact
    {budget : M.Cost} (bound : LocalCostBound program budget)
    (sec : CryptoLib.Core.SecPar)
    (env : CostedOracleEnv.{uCost, uOracle, uQuery, uResponse, uState} M Spec)
    (state : env.State) (result : ExactRunResult M Spec env.State α)
    (hresult : result ∈ (runExact program sec env state).support) :
    M.instPartialOrder.le result.localCost budget :=
  bound result.value result.localCost result.trace
    (possibleExecution_of_mem_support_runExact program sec env state result hresult)

/-- Every supported exact run respects all certified per-name query bounds. -/
theorem queryCount_le_of_mem_support_runExact
    {budget : Spec.Name → Nat} (bound : QueryBound program budget)
    (sec : CryptoLib.Core.SecPar)
    (env : CostedOracleEnv.{uCost, uOracle, uQuery, uResponse, uState} M Spec)
    (state : env.State) (result : ExactRunResult M Spec env.State α)
    (hresult : result ∈ (runExact program sec env state).support)
    (name : Spec.Name) :
    result.trace.count name ≤ budget name :=
  bound result.value result.localCost result.trace
    (possibleExecution_of_mem_support_runExact program sec env state result hresult) name

/-- Every supported exact run respects a certified total-query bound. -/
theorem totalQueries_le_of_mem_support_runExact
    {budget : Nat} (bound : TotalQueryBound program budget)
    (sec : CryptoLib.Core.SecPar)
    (env : CostedOracleEnv.{uCost, uOracle, uQuery, uResponse, uState} M Spec)
    (state : env.State) (result : ExactRunResult M Spec env.State α)
    (hresult : result ∈ (runExact program sec env state).support) :
    result.trace.total ≤ budget :=
  bound result.value result.localCost result.trace
    (possibleExecution_of_mem_support_runExact program sec env state result hresult)

end Program

end CryptoLib.Oracle

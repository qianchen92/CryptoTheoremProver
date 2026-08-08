import CryptoLib.Oracle.Bounds

namespace CryptoLib.Oracle

open CryptoLib.Core.Infrastructure.Computation.Cost

universe uCost uOracle uQuery uResponse uState uValue

namespace Program

variable {M : CostModel.{uCost}}
variable {Spec : OracleSpec.{uOracle, uQuery, uResponse}}
variable {issueCost : (name : Spec.Name) → Spec.Query name → M.Cost}

/-- Repeated sequential composition using the model's additive monoid. -/
abbrev repeatCost (M : CostModel.{uCost}) (count : Nat) (cost : M.Cost) : M.Cost :=
  M.instAddMonoid.toNatSMul.smul count cost

@[simp] theorem repeatCost_zero (M : CostModel.{uCost}) (cost : M.Cost) :
    repeatCost M 0 cost = M.instAddMonoid.zero := by
  letI := M.instAddMonoid
  exact zero_nsmul cost

@[simp] theorem repeatCost_one (M : CostModel.{uCost}) (cost : M.Cost) :
    repeatCost M 1 cost = cost := by
  letI := M.instAddMonoid
  exact one_nsmul cost

@[simp] theorem repeatCost_add (M : CostModel.{uCost})
    (first second : Nat) (cost : M.Cost) :
    repeatCost M (first + second) cost =
      M.instAddMonoid.add (repeatCost M first cost) (repeatCost M second cost) := by
  letI := M.instAddMonoid
  exact add_nsmul cost first second

@[simp] theorem repeatCost_nat (count cost : Nat) :
    repeatCost CostModel.nat count cost = count * cost :=
  Nat.nsmul_eq_mul count cost

/--
Capability needed to regroup interleaved caller and environment work.

Exact interpretation never requires this property.  It is requested only for
the coarse separated composition theorem.
-/
def CostExchange (M : CostModel.{uCost}) : Prop :=
  ∀ localFirst oracleFirst localSecond oracleSecond,
    M.instPartialOrder.le
      (M.instAddMonoid.add
        (M.instAddMonoid.add localFirst oracleFirst)
        (M.instAddMonoid.add localSecond oracleSecond))
      (M.instAddMonoid.add
        (M.instAddMonoid.add localFirst localSecond)
        (M.instAddMonoid.add oracleFirst oracleSecond))

theorem costExchange_nat : CostExchange CostModel.nat := by
  intro localFirst oracleFirst localSecond oracleSecond
  change (localFirst + oracleFirst) + (localSecond + oracleSecond) ≤
    (localFirst + localSecond) + (oracleFirst + oracleSecond)
  exact Nat.le_of_eq (by omega)

theorem repeatCost_nat_mono (cost : Nat) :
    ∀ {first second : Nat}, first ≤ second →
      CostModel.nat.instPartialOrder.le
        (repeatCost CostModel.nat first cost)
        (repeatCost CostModel.nat second cost) := by
  intro first second hle
  simpa only [repeatCost_nat] using Nat.mul_le_mul_right cost hle

variable {α : Type (max uValue uResponse)}

/-- Exact interleaved cost is bounded by separated local and oracle projections. -/
theorem totalCost_le_separated
    (program : Program issueCost α)
    (sec : CryptoLib.Core.SecPar)
    (env : CostedOracleEnv.{uCost, uOracle, uQuery, uResponse, uState} M Spec)
    (exchange : CostExchange M)
    (state : env.State) (result : ExactRunResult M Spec env.State α)
    (hresult : result ∈ (runExact program sec env state).support) :
    M.instPartialOrder.le result.totalCost
      (M.instAddMonoid.add result.localCost result.oracleCost) := by
  letI := M.instAddMonoid
  letI := M.instPartialOrder
  letI := M.instAddLeftMono
  letI := M.instAddRightMono
  induction program generalizing state with
  | pure value =>
      simp only [runExact] at hresult
      rw [PMF.mem_support_pure_iff] at hresult
      subst result
      change M.instPartialOrder.le M.instAddMonoid.zero
        (M.instAddMonoid.add M.instAddMonoid.zero M.instAddMonoid.zero)
      exact le_of_eq (M.instAddMonoid.zero_add M.instAddMonoid.zero).symm
  | bind first next ihFirst ihNext =>
      simp only [runExact] at hresult
      rw [PMF.mem_support_bind_iff] at hresult
      rcases hresult with ⟨firstResult, hfirstResult, hnextResult⟩
      rw [PMF.mem_support_bind_iff] at hnextResult
      rcases hnextResult with ⟨nextResult, hnextResult, hresult⟩
      rw [PMF.mem_support_pure_iff] at hresult
      subst result
      exact
        (add_le_add
          (ihFirst state firstResult hfirstResult)
          (ihNext firstResult.value firstResult.state nextResult hnextResult)).trans
            (exchange firstResult.localCost firstResult.oracleCost
              nextResult.localCost nextResult.oracleCost)
  | liftCosted dist =>
      simp only [runExact] at hresult
      rw [PMF.mem_support_bind_iff] at hresult
      rcases hresult with ⟨costedResult, _hcostedResult, hresult⟩
      rw [PMF.mem_support_pure_iff] at hresult
      subst result
      change M.instPartialOrder.le costedResult.cost
        (M.instAddMonoid.add costedResult.cost M.instAddMonoid.zero)
      exact le_of_eq (M.instAddMonoid.add_zero costedResult.cost).symm
  | query name oracleQuery =>
      simp only [runExact] at hresult
      rw [PMF.mem_support_bind_iff] at hresult
      rcases hresult with ⟨issueResult, hissueResult, horacleResult⟩
      rw [PMF.mem_support_pure_iff] at horacleResult
      subst result
      exact le_refl (issueCost name oracleQuery + issueResult.cost)

/-- Internal oracle work is bounded by total query count repeated addition. -/
theorem oracleCost_le_totalQueries_nsmul
    (program : Program issueCost α)
    (sec : CryptoLib.Core.SecPar)
    (env : CostedOracleEnv.{uCost, uOracle, uQuery, uResponse, uState} M Spec)
    (budget : M.Cost)
    (envBound : env.QueryCostBoundAt sec budget)
    (state : env.State) (result : ExactRunResult M Spec env.State α)
    (hresult : result ∈ (runExact program sec env state).support) :
    M.instPartialOrder.le result.oracleCost
      (repeatCost M result.trace.total budget) := by
  letI := M.instAddMonoid
  letI := M.instPartialOrder
  letI := M.instAddLeftMono
  letI := M.instAddRightMono
  induction program generalizing state with
  | pure value =>
      simp only [runExact] at hresult
      rw [PMF.mem_support_pure_iff] at hresult
      subst result
      simpa only [QueryTrace.total_empty, repeatCost_zero] using
        (le_refl M.instAddMonoid.zero)
  | bind first next ihFirst ihNext =>
      simp only [runExact] at hresult
      rw [PMF.mem_support_bind_iff] at hresult
      rcases hresult with ⟨firstResult, hfirstResult, hnextResult⟩
      rw [PMF.mem_support_bind_iff] at hnextResult
      rcases hnextResult with ⟨nextResult, hnextResult, hresult⟩
      rw [PMF.mem_support_pure_iff] at hresult
      subst result
      simpa only [QueryTrace.total_append, repeatCost_add] using
        add_le_add
          (ihFirst state firstResult hfirstResult)
          (ihNext firstResult.value firstResult.state nextResult hnextResult)
  | liftCosted dist =>
      simp only [runExact] at hresult
      rw [PMF.mem_support_bind_iff] at hresult
      rcases hresult with ⟨costedResult, _hcostedResult, hresult⟩
      rw [PMF.mem_support_pure_iff] at hresult
      subst result
      simpa only [QueryTrace.total_empty, repeatCost_zero] using
        (le_refl M.instAddMonoid.zero)
  | query name oracleQuery =>
      simp only [runExact] at hresult
      rw [PMF.mem_support_bind_iff] at hresult
      rcases hresult with ⟨issueResult, hissueResult, horacleResult⟩
      rw [PMF.mem_support_pure_iff] at horacleResult
      subst result
      simpa only [QueryTrace.total_singleton, repeatCost_one] using
        envBound name state oracleQuery issueResult hissueResult

/-- Coarse composition from independent local, query-count, and environment bounds. -/
theorem totalCost_le_composedBudget
    (program : Program issueCost α)
    (sec : CryptoLib.Core.SecPar)
    (env : CostedOracleEnv.{uCost, uOracle, uQuery, uResponse, uState} M Spec)
    (localBudget : M.Cost) (totalQueryBudget : Nat)
    (envBudget : M.Cost)
    (nsmulMono : ∀ {first second : Nat}, first ≤ second →
      M.instPartialOrder.le
        (repeatCost M first envBudget)
        (repeatCost M second envBudget))
    (exchange : CostExchange M)
    (programBound : LocalCostBound program localBudget)
    (programQueryBound : TotalQueryBound program totalQueryBudget)
    (envBound : env.QueryCostBoundAt sec envBudget)
    (state : env.State) (result : ExactRunResult M Spec env.State α)
    (hresult : result ∈ (runExact program sec env state).support) :
    M.instPartialOrder.le result.totalCost
      (M.instAddMonoid.add localBudget
        (repeatCost M totalQueryBudget envBudget)) := by
  letI := M.instAddMonoid
  letI := M.instPartialOrder
  letI := M.instAddLeftMono
  letI := M.instAddRightMono
  have possible :=
    possibleExecution_of_mem_support_runExact program sec env state result hresult
  have localCost : result.localCost ≤ localBudget :=
    programBound result.value result.localCost result.trace possible
  have queryCount : result.trace.total ≤ totalQueryBudget :=
    programQueryBound result.value result.localCost result.trace possible
  have oracleCost :
      result.oracleCost ≤ repeatCost M result.trace.total envBudget :=
    oracleCost_le_totalQueries_nsmul
      program sec env envBudget envBound state result hresult
  exact
    (totalCost_le_separated program sec env exchange state result hresult).trans
      (add_le_add localCost (oracleCost.trans (nsmulMono queryCount)))

/-- Every result of the public exact-cost projection satisfies the coarse bound. -/
theorem runCosted_cost_le_composedBudget
    (program : Program issueCost α)
    (sec : CryptoLib.Core.SecPar)
    (env : CostedOracleEnv.{uCost, uOracle, uQuery, uResponse, uState} M Spec)
    (localBudget : M.Cost) (totalQueryBudget : Nat)
    (envBudget : M.Cost)
    (nsmulMono : ∀ {first second : Nat}, first ≤ second →
      M.instPartialOrder.le
        (repeatCost M first envBudget)
        (repeatCost M second envBudget))
    (exchange : CostExchange M)
    (programBound : LocalCostBound program localBudget)
    (programQueryBound : TotalQueryBound program totalQueryBudget)
    (envBound : env.QueryCostBoundAt sec envBudget)
    (result : Costed M α)
    (hresult : result ∈ (runCosted program sec env).support) :
    M.instPartialOrder.le result.cost
      (M.instAddMonoid.add localBudget
        (repeatCost M totalQueryBudget envBudget)) := by
  simp only [runCosted, runExactFromInit] at hresult
  rw [PMF.mem_support_map_iff] at hresult
  rcases hresult with ⟨exactResult, hexactResult, hresult⟩
  subst result
  exact totalCost_le_composedBudget
    program sec env localBudget totalQueryBudget envBudget nsmulMono exchange
      programBound programQueryBound envBound env.init exactResult hexactResult

end Program

end CryptoLib.Oracle

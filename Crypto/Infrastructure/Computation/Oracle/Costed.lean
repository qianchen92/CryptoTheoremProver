import Crypto.Infrastructure.Computation.Oracle.Interface

namespace Crypto.Infrastructure.Computation.Oracle

open Crypto.Infrastructure.Computation.Cost

universe uCost uOracle uQuery uResponse uState uValue

/--
A stateful oracle environment whose internal query implementation carries an
exact cost on every execution path.

The ordinary `OracleEnv` remains the semantic interface used by security
games.  `CostedOracleEnv.erase` forgets these internal costs, while the
composed interpreter below retains them when an oracle is implemented inside a
reduction.
-/
structure CostedOracleEnvT
    (M : CostModel.{uCost})
    (Spec : OracleSpec.{uOracle, uQuery, uResponse}) where
  State : Type uState
  init : State
  query :
    (name : Spec.Name) →
    Crypto.SecPar →
    State →
    Spec.Query name →
    RandCostedT M (Spec.Response name × State)

/-- Natural-number compatibility name for internally costed environments. -/
abbrev CostedOracleEnv
    (Spec : OracleSpec.{uOracle, uQuery, uResponse}) :=
  CostedOracleEnvT natCostModel Spec

namespace CostedOracleEnvT

variable {M : CostModel.{uCost}}
variable {Spec : OracleSpec.{uOracle, uQuery, uResponse}}

/-- Forget all internal costs without changing query value distributions. -/
noncomputable def erase
    (env : CostedOracleEnvT.{uCost, uOracle, uQuery, uResponse, uState} M Spec) :
    OracleEnv.{uOracle, uQuery, uResponse, uState} Spec where
  State := env.State
  init := env.init
  query := fun name sec state query =>
    RandCostedT.valueDist (env.query name sec state query)

/-- A uniform bound on every internal query path in the generic model. -/
def QueryCostBound
    (env : CostedOracleEnvT.{uCost, uOracle, uQuery, uResponse, uState} M Spec)
    (bound : Crypto.SecPar → M.Cost) : Prop :=
  ∀ name sec state query result,
    result ∈ (env.query name sec state query).support →
      M.instPartialOrder.le result.cost (bound sec)

/-- A generic per-query bound at one fixed security parameter. -/
def QueryCostBoundAt
    (env : CostedOracleEnvT.{uCost, uOracle, uQuery, uResponse, uState} M Spec)
    (sec : Crypto.SecPar) (bound : Crypto.SecPar → M.Cost) : Prop :=
  ∀ name state query result,
    result ∈ (env.query name sec state query).support →
      M.instPartialOrder.le result.cost (bound sec)

theorem QueryCostBound.at
    {env : CostedOracleEnvT.{uCost, uOracle, uQuery, uResponse, uState} M Spec}
    {bound : Crypto.SecPar → M.Cost}
    (certificate : env.QueryCostBound bound) (sec : Crypto.SecPar) :
    env.QueryCostBoundAt sec bound :=
  fun name state query result => certificate name sec state query result

end CostedOracleEnvT

namespace CostedOracleEnv

variable {Spec : OracleSpec.{uOracle, uQuery, uResponse}}

/-- Explicit constructor retained for callers of the natural-number API. -/
@[match_pattern] abbrev mk
    (State : Type uState) (init : State)
    (query :
      (name : Spec.Name) → Crypto.SecPar → State → Spec.Query name →
        RandCosted (Spec.Response name × State)) :
    CostedOracleEnv Spec :=
  CostedOracleEnvT.mk State init query

/-- Forget internal query costs and expose the semantic oracle environment. -/
noncomputable def erase
    (env : CostedOracleEnv.{uOracle, uQuery, uResponse, uState} Spec) :
    OracleEnv.{uOracle, uQuery, uResponse, uState} Spec where
  State := env.State
  init := env.init
  query := fun name sec state query =>
    RandCosted.valueDist (env.query name sec state query)

/-- A uniform security-parameter-indexed bound on every internal query path. -/
def QueryCostBound
    (env : CostedOracleEnv.{uOracle, uQuery, uResponse, uState} Spec)
    (bound : Crypto.SecPar → Cost) : Prop :=
  ∀ name sec state query result,
    result ∈ (env.query name sec state query).support →
      result.cost ≤ bound sec

/-- A per-query cost bound at one fixed security parameter. -/
def QueryCostBoundAt
    (env : CostedOracleEnv.{uOracle, uQuery, uResponse, uState} Spec)
    (sec : Crypto.SecPar)
    (bound : Crypto.SecPar → Cost) : Prop :=
  ∀ name state query result,
    result ∈ (env.query name sec state query).support →
      result.cost ≤ bound sec

/-- A uniform query certificate specializes to any fixed security parameter. -/
theorem QueryCostBound.at
    {env : CostedOracleEnv.{uOracle, uQuery, uResponse, uState} Spec}
    {bound : Crypto.SecPar → Cost}
    (certificate : env.QueryCostBound bound)
    (sec : Crypto.SecPar) :
    env.QueryCostBoundAt sec bound :=
  fun name state query result => certificate name sec state query result

end CostedOracleEnv

namespace OracleProgramT

variable {M : CostModel.{uCost}}
variable {Spec : OracleSpec.{uOracle, uQuery, uResponse}}

/-- Repeated sequential composition using the model's own additive monoid. -/
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
    (left right : Nat) (cost : M.Cost) :
    repeatCost M (left + right) cost =
      M.instAddMonoid.add (repeatCost M left cost) (repeatCost M right cost) := by
  letI := M.instAddMonoid
  exact add_nsmul cost left right

@[simp] theorem repeatCost_nat (count cost : Nat) :
    repeatCost natCostModel count cost = count * cost := by
  exact Nat.nsmul_eq_mul count cost

/--
Capability needed to regroup interleaved caller/oracle work for a coarse bound.
Exact interpretation never requires this law.  Commutative additive resource
models satisfy it by equality; genuinely noncommutative models may instead use
the exact `totalCost` without requesting a regrouped bound.
-/
def CostExchange (M : CostModel.{uCost}) : Prop :=
  ∀ localLeft oracleLeft localRight oracleRight,
    M.instPartialOrder.le
      (M.instAddMonoid.add
        (M.instAddMonoid.add localLeft oracleLeft)
        (M.instAddMonoid.add localRight oracleRight))
      (M.instAddMonoid.add
        (M.instAddMonoid.add localLeft localRight)
        (M.instAddMonoid.add oracleLeft oracleRight))

theorem costExchange_nat : CostExchange natCostModel := by
  intro localLeft oracleLeft localRight oracleRight
  change (localLeft + oracleLeft) + (localRight + oracleRight) ≤
    (localLeft + localRight) + (oracleLeft + oracleRight)
  exact Nat.le_of_eq (by omega)

theorem repeatCost_nat_mono (cost : Nat) :
    ∀ {left right : Nat}, left ≤ right →
      natCostModel.instPartialOrder.le
        (repeatCost natCostModel left cost)
        (repeatCost natCostModel right cost) := by
  intro left right hle
  simpa only [repeatCost_nat] using Nat.mul_le_mul_right cost hle

/--
Generic composed interpreter result.  Local work and implemented-oracle work
remain separately auditable; their ordered sum is the coarse composed cost.
-/
structure CostedRunResult
    (M : CostModel.{uCost})
    (Spec : OracleSpec.{uOracle, uQuery, uResponse})
    (State : Type uState) (α : Type (max uValue uResponse)) where
  value : α
  state : State
  profile : OracleProfileT M Spec
  oracleCost : M.Cost
  /-- Exact cost in structural execution order, without regrouping. -/
  totalCost : M.Cost

namespace CostedRunResult

/-- Forget implemented-oracle costs while retaining the generic local profile. -/
def erase
    {State : Type uState} {α : Type (max uValue uResponse)}
    (result : CostedRunResult M Spec State α) :
    RunResult M Spec State α :=
  ⟨result.value, result.state, result.profile⟩

end CostedRunResult

/-- Interpret a generic oracle program against a generic-cost environment. -/
noncomputable def runProfiledWithCostedEnv
    {α : Type (max uValue uResponse)} (program : OracleProgramT M Spec α)
    (sec : Crypto.SecPar)
    (env : CostedOracleEnvT.{uCost, uOracle, uQuery, uResponse, uState} M Spec)
    (state : env.State) :
    PMF (CostedRunResult M Spec env.State α) := by
  letI := M.instAddMonoid
  exact
    match program with
    | OracleProgramT.pure value =>
        PMF.pure ⟨value, state, OracleProfileT.zero M Spec, 0, 0⟩
    | OracleProgramT.bind first next =>
        PMF.bind (runProfiledWithCostedEnv first sec env state) fun firstResult =>
          PMF.bind
            (runProfiledWithCostedEnv
              (next firstResult.value) sec env firstResult.state)
            fun nextResult =>
              PMF.pure
                ⟨nextResult.value, nextResult.state,
                  OracleProfileT.append firstResult.profile nextResult.profile,
                  firstResult.oracleCost + nextResult.oracleCost,
                  firstResult.totalCost + nextResult.totalCost⟩
    | OracleProgramT.liftCosted dist =>
        PMF.bind dist fun result =>
          PMF.pure
            ⟨result.val, state, OracleProfileT.ofCost result.cost, 0, result.cost⟩
    | OracleProgramT.queryWithCost localCost name oracleQuery =>
        PMF.bind (env.query name sec state oracleQuery) fun result =>
          PMF.pure
            ⟨ULift.up result.val.1, result.val.2,
              OracleProfileT.ofQueryWithCost localCost name, result.cost,
              localCost + result.cost⟩

/-- Run the generic composed interpreter from the environment's initial state. -/
noncomputable def runProfiledWithCostedEnvFromInit
    {α : Type (max uValue uResponse)} (program : OracleProgramT M Spec α)
    (sec : Crypto.SecPar)
    (env : CostedOracleEnvT.{uCost, uOracle, uQuery, uResponse, uState} M Spec) :
    PMF (CostedRunResult M Spec env.State α) :=
  runProfiledWithCostedEnv program sec env env.init

/-- Retain the ordered generic composed cost. -/
noncomputable def runCostedWithCostedEnv
    {α : Type (max uValue uResponse)} (program : OracleProgramT M Spec α)
    (sec : Crypto.SecPar)
    (env : CostedOracleEnvT.{uCost, uOracle, uQuery, uResponse, uState} M Spec) :
    RandCostedT M α :=
  PMF.map (fun result => ⟨result.value, result.totalCost⟩)
    (runProfiledWithCostedEnvFromInit program sec env)

/-- Generic cost erasure recovers the ordinary profiled interpreter. -/
theorem map_erase_runProfiledWithCostedEnv
    {α : Type (max uValue uResponse)} (program : OracleProgramT M Spec α)
    (sec : Crypto.SecPar)
    (env : CostedOracleEnvT.{uCost, uOracle, uQuery, uResponse, uState} M Spec)
    (state : env.State) :
    PMF.map CostedRunResult.erase
        (runProfiledWithCostedEnv program sec env state) =
      runProfiled program sec env.erase state := by
  induction program generalizing state with
  | pure value =>
      simp only [runProfiledWithCostedEnv, runProfiled, PMF.pure_map]
      rfl
  | bind first next ihFirst ihNext =>
    simp only [runProfiledWithCostedEnv, runProfiled,
      PMF.map_bind, PMF.pure_map]
    rw [← ihFirst state]
    refine Eq.trans ?_ (PMF.bind_map
      (runProfiledWithCostedEnv first sec env state)
      CostedRunResult.erase
      (fun firstResult =>
        (runProfiled (next firstResult.value) sec env.erase firstResult.state).bind
          fun nextResult =>
            PMF.pure
              ({
                value := nextResult.value
                state := nextResult.state
                profile :=
                  OracleProfileT.append firstResult.profile nextResult.profile
              } : RunResult M Spec env.State _))).symm
    congr 1
    funext firstResult
    simp only [Function.comp_apply, CostedRunResult.erase]
    rw [← ihNext firstResult.value firstResult.state]
    exact
      (PMF.bind_map
        (runProfiledWithCostedEnv
          (next firstResult.value) sec env firstResult.state)
        CostedRunResult.erase
        (fun nextResult =>
          PMF.pure
            ({
              value := nextResult.value
              state := nextResult.state
              profile :=
                OracleProfileT.append firstResult.profile nextResult.profile
            } : RunResult M Spec env.State _))).symm
  | liftCosted dist =>
      simp only [runProfiledWithCostedEnv, runProfiled,
        PMF.map_bind, PMF.pure_map]
      rfl
  | queryWithCost localCost name oracleQuery =>
      simp only [runProfiledWithCostedEnv, runProfiled,
        CostedOracleEnvT.erase, RandCostedT.valueDist,
        PMF.map_bind, PMF.pure_map, PMF.bind_map]
      rfl

/-- Erasing generic composed costs preserves the output distribution. -/
@[simp] theorem valueDist_runCostedWithCostedEnv
    {α : Type (max uValue uResponse)} (program : OracleProgramT M Spec α)
    (sec : Crypto.SecPar)
    (env : CostedOracleEnvT.{uCost, uOracle, uQuery, uResponse, uState} M Spec) :
    RandCostedT.valueDist (runCostedWithCostedEnv program sec env) =
      runWithEnv program sec env.erase := by
  simp only [RandCostedT.valueDist, runCostedWithCostedEnv,
    runProfiledWithCostedEnvFromInit, runWithEnv, PMF.map_comp]
  change
    PMF.map CostedRunResult.value
        (runProfiledWithCostedEnv program sec env env.init) =
      PMF.map RunResult.value (runProfiled program sec env.erase env.init)
  rw [← map_erase_runProfiledWithCostedEnv program sec env env.init]
  exact
    (PMF.map_comp
      (p := runProfiledWithCostedEnv program sec env env.init)
      (f := CostedRunResult.erase) RunResult.value).symm

theorem execution_of_mem_support_runProfiledWithCostedEnv
    {α : Type (max uValue uResponse)} (program : OracleProgramT M Spec α)
    (sec : Crypto.SecPar)
    (env : CostedOracleEnvT.{uCost, uOracle, uQuery, uResponse, uState} M Spec)
    (state : env.State) (result : CostedRunResult M Spec env.State α)
    (hresult :
      result ∈ (runProfiledWithCostedEnv program sec env state).support) :
    Execution program result.value result.profile := by
  induction program generalizing state with
  | pure value =>
      simp only [runProfiledWithCostedEnv] at hresult
      rw [PMF.mem_support_pure_iff] at hresult
      subst result
      exact Execution.pure value
  | bind first next ihFirst ihNext =>
      simp only [runProfiledWithCostedEnv] at hresult
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
      simp only [runProfiledWithCostedEnv] at hresult
      rw [PMF.mem_support_bind_iff] at hresult
      rcases hresult with ⟨costedResult, hcostedResult, hresult⟩
      rw [PMF.mem_support_pure_iff] at hresult
      subst result
      exact Execution.liftCosted hcostedResult
  | queryWithCost localCost name oracleQuery =>
      simp only [runProfiledWithCostedEnv] at hresult
      rw [PMF.mem_support_bind_iff] at hresult
      rcases hresult with ⟨oracleResult, _horacleResult, hresult⟩
      rw [PMF.mem_support_pure_iff] at hresult
      subst result
      exact Execution.queryWithCost localCost name oracleQuery oracleResult.val.1

/-- Under `CostExchange`, exact interleaved work is bounded by grouped work. -/
theorem totalCost_le_separated
    {α : Type (max uValue uResponse)} (program : OracleProgramT M Spec α)
    (sec : Crypto.SecPar)
    (env : CostedOracleEnvT.{uCost, uOracle, uQuery, uResponse, uState} M Spec)
    (exchange : CostExchange M)
    (state : env.State) (result : CostedRunResult M Spec env.State α)
    (hresult :
      result ∈ (runProfiledWithCostedEnv program sec env state).support) :
    M.instPartialOrder.le result.totalCost
      (M.instAddMonoid.add result.profile.cost result.oracleCost) := by
  letI := M.instAddMonoid
  letI := M.instPartialOrder
  letI := M.instAddLeftMono
  letI := M.instAddRightMono
  induction program generalizing state with
  | pure value =>
      simp only [runProfiledWithCostedEnv] at hresult
      rw [PMF.mem_support_pure_iff] at hresult
      subst result
      change M.instPartialOrder.le M.instAddMonoid.zero
        (M.instAddMonoid.add M.instAddMonoid.zero M.instAddMonoid.zero)
      exact le_of_eq (M.instAddMonoid.zero_add M.instAddMonoid.zero).symm
  | bind first next ihFirst ihNext =>
      simp only [runProfiledWithCostedEnv] at hresult
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
            (exchange firstResult.profile.cost firstResult.oracleCost
              nextResult.profile.cost nextResult.oracleCost)
  | liftCosted dist =>
      simp only [runProfiledWithCostedEnv] at hresult
      rw [PMF.mem_support_bind_iff] at hresult
      rcases hresult with ⟨costedResult, _hcostedResult, hresult⟩
      rw [PMF.mem_support_pure_iff] at hresult
      subst result
      change M.instPartialOrder.le costedResult.cost
        (M.instAddMonoid.add costedResult.cost M.instAddMonoid.zero)
      exact le_of_eq (M.instAddMonoid.add_zero costedResult.cost).symm
  | queryWithCost localCost name oracleQuery =>
      simp only [runProfiledWithCostedEnv] at hresult
      rw [PMF.mem_support_bind_iff] at hresult
      rcases hresult with ⟨oracleResult, _horacleResult, hresult⟩
      rw [PMF.mem_support_pure_iff] at hresult
      subst result
      exact le_refl (localCost + oracleResult.cost)

/-- Internal oracle work is bounded by query count repeated addition. -/
theorem oracleCost_le_totalQueries_nsmul
    {α : Type (max uValue uResponse)} (program : OracleProgramT M Spec α)
    (sec : Crypto.SecPar)
    (env : CostedOracleEnvT.{uCost, uOracle, uQuery, uResponse, uState} M Spec)
    (bound : Crypto.SecPar → M.Cost)
    (envBound : env.QueryCostBoundAt sec bound)
    (state : env.State) (result : CostedRunResult M Spec env.State α)
    (hresult :
      result ∈ (runProfiledWithCostedEnv program sec env state).support) :
    M.instPartialOrder.le result.oracleCost
      (repeatCost M result.profile.totalQueries (bound sec)) := by
  letI := M.instAddMonoid
  letI := M.instPartialOrder
  letI := M.instAddLeftMono
  letI := M.instAddRightMono
  induction program generalizing state with
  | pure value =>
      simp only [runProfiledWithCostedEnv] at hresult
      rw [PMF.mem_support_pure_iff] at hresult
      subst result
      simpa only [OracleProfileT.totalQueries_zero, repeatCost_zero] using
        (le_refl M.instAddMonoid.zero)
  | bind first next ihFirst ihNext =>
      simp only [runProfiledWithCostedEnv] at hresult
      rw [PMF.mem_support_bind_iff] at hresult
      rcases hresult with ⟨firstResult, hfirstResult, hnextResult⟩
      rw [PMF.mem_support_bind_iff] at hnextResult
      rcases hnextResult with ⟨nextResult, hnextResult, hresult⟩
      rw [PMF.mem_support_pure_iff] at hresult
      subst result
      simpa only [OracleProfileT.totalQueries_append, repeatCost_add] using
        add_le_add
          (ihFirst state firstResult hfirstResult)
          (ihNext firstResult.value firstResult.state nextResult hnextResult)
  | liftCosted dist =>
      simp only [runProfiledWithCostedEnv] at hresult
      rw [PMF.mem_support_bind_iff] at hresult
      rcases hresult with ⟨costedResult, _hcostedResult, hresult⟩
      rw [PMF.mem_support_pure_iff] at hresult
      subst result
      simpa only [OracleProfileT.totalQueries_ofCost, repeatCost_zero] using
        (le_refl M.instAddMonoid.zero)
  | queryWithCost localCost name oracleQuery =>
      simp only [runProfiledWithCostedEnv] at hresult
      rw [PMF.mem_support_bind_iff] at hresult
      rcases hresult with ⟨oracleResult, horacleResult, hresult⟩
      rw [PMF.mem_support_pure_iff] at hresult
      subst result
      simpa only [OracleProfileT.totalQueries_ofQueryWithCost, repeatCost_one] using
        envBound name state oracleQuery oracleResult horacleResult

/--
Generic coarse composition.  Monotonicity in the query multiplier is explicit:
it does not follow from an arbitrary ordered additive monoid unless the chosen
oracle budget is nonnegative in that model.
-/
theorem totalCost_le_composedBudget
    {α : Type (max uValue uResponse)} (program : OracleProgramT M Spec α)
    (sec : Crypto.SecPar)
    (env : CostedOracleEnvT.{uCost, uOracle, uQuery, uResponse, uState} M Spec)
    (machineBudget : M.Cost) (totalQueryBudget : Nat)
    (envBudget : Crypto.SecPar → M.Cost)
    (nsmulMono : ∀ {left right : Nat}, left ≤ right →
      M.instPartialOrder.le
        (repeatCost M left (envBudget sec))
        (repeatCost M right (envBudget sec)))
    (exchange : CostExchange M)
    (programBound : CostBound program machineBudget)
    (programQueryBound : TotalQueryBound program totalQueryBudget)
    (envBound : env.QueryCostBoundAt sec envBudget)
    (state : env.State) (result : CostedRunResult M Spec env.State α)
    (hresult :
      result ∈ (runProfiledWithCostedEnv program sec env state).support) :
    M.instPartialOrder.le result.totalCost
      (M.instAddMonoid.add machineBudget
        (repeatCost M totalQueryBudget (envBudget sec))) := by
  letI := M.instAddMonoid
  letI := M.instPartialOrder
  letI := M.instAddLeftMono
  letI := M.instAddRightMono
  have execution :=
    execution_of_mem_support_runProfiledWithCostedEnv
      program sec env state result hresult
  have machineCost : result.profile.cost ≤ machineBudget :=
    programBound result.value result.profile execution
  have queryCount : result.profile.totalQueries ≤ totalQueryBudget :=
    programQueryBound result.value result.profile execution
  have oracleCost :
      result.oracleCost ≤
        repeatCost M result.profile.totalQueries (envBudget sec) :=
    oracleCost_le_totalQueries_nsmul
      program sec env envBudget envBound state result hresult
  exact
    (totalCost_le_separated program sec env exchange state result hresult).trans
      (add_le_add machineCost (oracleCost.trans (nsmulMono queryCount)))

/-- Every generic composed execution path satisfies the generic coarse bound. -/
theorem runCostedWithCostedEnv_cost_le
    {α : Type (max uValue uResponse)} (program : OracleProgramT M Spec α)
    (sec : Crypto.SecPar)
    (env : CostedOracleEnvT.{uCost, uOracle, uQuery, uResponse, uState} M Spec)
    (machineBudget : M.Cost) (totalQueryBudget : Nat)
    (envBudget : Crypto.SecPar → M.Cost)
    (nsmulMono : ∀ {left right : Nat}, left ≤ right →
      M.instPartialOrder.le
        (repeatCost M left (envBudget sec))
        (repeatCost M right (envBudget sec)))
    (exchange : CostExchange M)
    (programBound : CostBound program machineBudget)
    (programQueryBound : TotalQueryBound program totalQueryBudget)
    (envBound : env.QueryCostBoundAt sec envBudget)
    (result : CostedT M α)
    (hresult : result ∈ (runCostedWithCostedEnv program sec env).support) :
    M.instPartialOrder.le result.cost
      (M.instAddMonoid.add machineBudget
        (repeatCost M totalQueryBudget (envBudget sec))) := by
  simp only [runCostedWithCostedEnv,
    runProfiledWithCostedEnvFromInit] at hresult
  rw [PMF.mem_support_map_iff] at hresult
  rcases hresult with ⟨profiledResult, hprofiledResult, hresult⟩
  subst result
  exact totalCost_le_composedBudget
    program sec env machineBudget totalQueryBudget envBudget nsmulMono exchange
      programBound programQueryBound envBound
      env.init profiledResult hprofiledResult

end OracleProgramT

namespace OracleProgram

variable {Spec : OracleSpec.{uOracle, uQuery, uResponse}}

/--
Result of interpreting an oracle program against a costed environment.

`profile` records the machine's own local work and oracle-call trace;
`oracleCost` records work performed inside the supplied environment.  Keeping
the components separate lets the ordinary oracle-machine bound remain valid
and makes the reduction overhead explicit.
-/
structure CostedRunResult
    (Spec : OracleSpec.{uOracle, uQuery, uResponse})
    (State : Type uState)
    (α : Type (max uValue uResponse)) where
  value : α
  state : State
  profile : OracleProfile Spec
  oracleCost : Cost

namespace CostedRunResult

/-- Project the authoritative generic natural-cost result to legacy packaging. -/
def ofT
    {State : Type uState} {alpha : Type (max uValue uResponse)}
    (result :
      OracleProgramT.CostedRunResult natCostModel Spec State alpha) :
    CostedRunResult Spec State alpha :=
  ⟨result.value, result.state, OracleProfile.ofT result.profile,
    result.oracleCost⟩

/-- Total composed cost of the machine path and the environment path. -/
def totalCost
    {State : Type uState} {α : Type (max uValue uResponse)}
    (result : CostedRunResult Spec State α) : Cost :=
  result.profile.cost + result.oracleCost

/-- Forget environment costs while retaining the ordinary machine profile. -/
def erase
    {State : Type uState} {α : Type (max uValue uResponse)}
    (result : CostedRunResult Spec State α) : RunResult Spec State α :=
  ⟨result.value, result.state, result.profile⟩

end CostedRunResult

/--
Interpret an oracle program while separately accumulating machine and internal
environment costs.
-/
noncomputable def runProfiledWithCostedEnv
    {α : Type (max uValue uResponse)}
    (program : OracleProgram Spec α)
    (sec : Crypto.SecPar)
    (env : CostedOracleEnv.{uOracle, uQuery, uResponse, uState} Spec)
    (state : env.State) :
    PMF (CostedRunResult Spec env.State α) :=
  PMF.map CostedRunResult.ofT
    (OracleProgramT.runProfiledWithCostedEnv program.toT sec env state)

/-- Run from the initial state and retain both resource components. -/
noncomputable def runProfiledWithCostedEnvFromInit
    {α : Type (max uValue uResponse)}
    (program : OracleProgram Spec α)
    (sec : Crypto.SecPar)
    (env : CostedOracleEnv.{uOracle, uQuery, uResponse, uState} Spec) :
    PMF (CostedRunResult Spec env.State α) :=
  runProfiledWithCostedEnv program sec env env.init

/-- Run against a costed environment and retain the total composed path cost. -/
noncomputable def runCostedWithCostedEnv
    {α : Type (max uValue uResponse)}
    (program : OracleProgram Spec α)
    (sec : Crypto.SecPar)
    (env : CostedOracleEnv.{uOracle, uQuery, uResponse, uState} Spec) :
    RandCosted α :=
  OracleProgramT.runCostedWithCostedEnv program.toT sec env

/-- Erasing internal environment costs recovers the ordinary profiled interpreter. -/
theorem map_erase_runProfiledWithCostedEnv
    {α : Type (max uValue uResponse)}
    (program : OracleProgram Spec α)
    (sec : Crypto.SecPar)
    (env : CostedOracleEnv.{uOracle, uQuery, uResponse, uState} Spec)
    (state : env.State) :
    PMF.map CostedRunResult.erase
        (runProfiledWithCostedEnv program sec env state) =
      runProfiled program sec env.erase state := by
  have bridge := congrArg (PMF.map RunResult.ofT)
    (OracleProgramT.map_erase_runProfiledWithCostedEnv
      program.toT sec env state)
  have projected := bridge.trans
    (OracleProgram.map_ofT_runProfiled_toT
      program sec (CostedOracleEnvT.erase env) state)
  simpa only [runProfiledWithCostedEnv, OracleProgram.runProfiled,
    PMF.map_comp, Function.comp_apply, CostedRunResult.erase,
    CostedRunResult.ofT, RunResult.ofT,
    OracleProgramT.CostedRunResult.erase,
    CostedOracleEnvT.erase, CostedOracleEnv.erase] using projected

/-- Cost erasure of the composed interpreter recovers ordinary oracle semantics. -/
@[simp] theorem valueDist_runCostedWithCostedEnv
    {α : Type (max uValue uResponse)}
    (program : OracleProgram Spec α)
    (sec : Crypto.SecPar)
    (env : CostedOracleEnv.{uOracle, uQuery, uResponse, uState} Spec) :
    RandCosted.valueDist (runCostedWithCostedEnv program sec env) =
      runWithEnv program sec env.erase := by
  change RandCostedT.valueDist
      (OracleProgramT.runCostedWithCostedEnv program.toT sec env) =
    runWithEnv program sec env.erase
  rw [OracleProgramT.valueDist_runCostedWithCostedEnv]
  simp only [OracleProgramT.runWithEnv, OracleProgram.runWithEnv]
  have bridge := congrArg (PMF.map RunResult.value)
    (OracleProgram.map_ofT_runProfiled_toT
      program sec (CostedOracleEnvT.erase env) env.init)
  simpa only [PMF.map_comp, Function.comp_apply, RunResult.ofT,
    CostedOracleEnvT.erase, CostedOracleEnv.erase] using bridge

/-- Every composed interpreter result follows an abstract machine execution. -/
theorem execution_of_mem_support_runProfiledWithCostedEnv
    {α : Type (max uValue uResponse)}
    (program : OracleProgram Spec α)
    (sec : Crypto.SecPar)
    (env : CostedOracleEnv.{uOracle, uQuery, uResponse, uState} Spec)
    (state : env.State)
    (result : CostedRunResult Spec env.State α)
    (hresult : result ∈ (runProfiledWithCostedEnv program sec env state).support) :
    Execution program result.value result.profile := by
  have herased :
      result.erase ∈
        (PMF.map CostedRunResult.erase
          (runProfiledWithCostedEnv program sec env state)).support := by
    rw [PMF.mem_support_map_iff]
    exact ⟨result, hresult, rfl⟩
  rw [map_erase_runProfiledWithCostedEnv program sec env state] at herased
  exact OracleProgram.execution_of_mem_support_runProfiled
    program sec env.erase state result.erase herased

/-- Internal oracle work is bounded by query count times the per-query budget. -/
theorem oracleCost_le_totalQueries_mul
    {α : Type (max uValue uResponse)}
    (program : OracleProgram Spec α)
    (sec : Crypto.SecPar)
    (env : CostedOracleEnv.{uOracle, uQuery, uResponse, uState} Spec)
    (bound : Crypto.SecPar → Cost)
    (envBound : env.QueryCostBoundAt sec bound)
    (state : env.State)
    (result : CostedRunResult Spec env.State α)
    (hresult : result ∈ (runProfiledWithCostedEnv program sec env state).support) :
    result.oracleCost ≤ result.profile.totalQueries * bound sec := by
  simp only [runProfiledWithCostedEnv] at hresult
  rw [PMF.mem_support_map_iff] at hresult
  rcases hresult with ⟨genericResult, hgenericResult, hresult⟩
  subst result
  simpa only [CostedRunResult.ofT, OracleProfile.totalQueries_ofT,
    OracleProgramT.repeatCost_nat] using
    (OracleProgramT.oracleCost_le_totalQueries_nsmul
      program.toT sec env bound envBound state genericResult hgenericResult)

/--
The composed interpreter is bounded by the local machine budget plus the
independent total-query budget times the uniform internal query budget.
-/
theorem totalCost_le_composedBudget
    {α : Type (max uValue uResponse)}
    (program : OracleProgram Spec α)
    (sec : Crypto.SecPar)
    (env : CostedOracleEnv.{uOracle, uQuery, uResponse, uState} Spec)
    (machineBudget : Cost)
    (totalQueryBudget : Nat)
    (envBudget : Crypto.SecPar → Cost)
    (programBound : CostBound program machineBudget)
    (programQueryBound : TotalQueryBound program totalQueryBudget)
    (envBound : env.QueryCostBoundAt sec envBudget)
    (state : env.State)
    (result : CostedRunResult Spec env.State α)
    (hresult : result ∈ (runProfiledWithCostedEnv program sec env state).support) :
    result.totalCost ≤
      machineBudget + totalQueryBudget * envBudget sec := by
  have execution :=
    execution_of_mem_support_runProfiledWithCostedEnv
      program sec env state result hresult
  have machineCost : result.profile.cost ≤ machineBudget :=
    programBound result.value result.profile execution
  have queryCount : result.profile.totalQueries ≤ totalQueryBudget :=
    programQueryBound result.value result.profile execution
  have oracleCost :
      result.oracleCost ≤ result.profile.totalQueries * envBudget sec :=
    oracleCost_le_totalQueries_mul
      program sec env envBudget envBound state result hresult
  exact Nat.add_le_add machineCost
    (oracleCost.trans (Nat.mul_le_mul_right (envBudget sec) queryCount))

/-- Every path of the composed costed interpreter satisfies the composed budget. -/
theorem runCostedWithCostedEnv_cost_le
    {α : Type (max uValue uResponse)}
    (program : OracleProgram Spec α)
    (sec : Crypto.SecPar)
    (env : CostedOracleEnv.{uOracle, uQuery, uResponse, uState} Spec)
    (machineBudget : Cost)
    (totalQueryBudget : Nat)
    (envBudget : Crypto.SecPar → Cost)
    (programBound : CostBound program machineBudget)
    (programQueryBound : TotalQueryBound program totalQueryBudget)
    (envBound : env.QueryCostBoundAt sec envBudget)
    (result : Costed α)
    (hresult : result ∈ (runCostedWithCostedEnv program sec env).support) :
    result.cost ≤ machineBudget + totalQueryBudget * envBudget sec := by
  simp only [runCostedWithCostedEnv,
    OracleProgramT.runCostedWithCostedEnv,
    OracleProgramT.runProfiledWithCostedEnvFromInit] at hresult
  rw [PMF.mem_support_map_iff] at hresult
  rcases hresult with ⟨genericResult, hgenericResult, hresult⟩
  subst result
  have hlegacy :
      CostedRunResult.ofT genericResult ∈
        (runProfiledWithCostedEnv program sec env env.init).support := by
    simp only [runProfiledWithCostedEnv]
    rw [PMF.mem_support_map_iff]
    exact ⟨genericResult, hgenericResult, rfl⟩
  have hseparated :
      genericResult.totalCost ≤
        genericResult.profile.cost + genericResult.oracleCost :=
    OracleProgramT.totalCost_le_separated
      program.toT sec env OracleProgramT.costExchange_nat
      env.init genericResult hgenericResult
  exact hseparated.trans (by
    simpa only [CostedRunResult.totalCost, CostedRunResult.ofT,
      OracleProfile.cost_ofT] using
      totalCost_le_composedBudget
        program sec env machineBudget totalQueryBudget envBudget
        programBound programQueryBound envBound env.init
        (CostedRunResult.ofT genericResult) hlegacy)

end OracleProgram

end Crypto.Infrastructure.Computation.Oracle

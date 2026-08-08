import CryptoLib.Core.Infrastructure.Complexity.Basic
import CryptoLib.Test.Infrastructure.Computation.TraceCost

namespace CryptoLib.Test.Infrastructure.Computation.CostedOracle

open CryptoLib.Core.Infrastructure.Asymptotic
open CryptoLib.Core.Infrastructure.Complexity
open CryptoLib.Core.Infrastructure.Computation
open CryptoLib.Core.Infrastructure.Computation.Cost
open CryptoLib.Oracle
open CryptoLib.Oracle.Complexity

inductive TestOracle where
  | bit
deriving DecidableEq

def testOracleSpec : OracleSpec where
  Name := TestOracle
  Query
    | .bit => Bool
  Response
    | .bit => Bool

/-- Caller-side query issuance has one exact unit of cost. -/
noncomputable def natIssueCost :
    (name : testOracleSpec.Name) → testOracleSpec.Query name → CostModel.nat.Cost :=
  fun _name _query => 1

/-- The exact issuance handler, not query syntax, is the cost source. -/
noncomputable def oneQueryProgram : Oracle.Program natIssueCost (ULift Bool) :=
  Oracle.Program.query TestOracle.bit false

/-- Two adaptive calls; neither query constructor contains a cost annotation. -/
noncomputable def twoQueryProgram : Oracle.Program natIssueCost (ULift Bool) := do
  let first ← Oracle.Program.query TestOracle.bit false
  Oracle.Program.query TestOracle.bit first.down

/-- The implementation negates its query and charges three exact internal units. -/
noncomputable def costedEnv : CostedOracleEnv CostModel.nat testOracleSpec where
  State := Nat
  init := 0
  query := fun name _sec state query =>
    match name with
    | .bit => PMF.pure ⟨(!query, state + 1), 3⟩

theorem costedEnv_queryCostBound :
    costedEnv.QueryCostBound (fun _sec => 3) := by
  intro name sec state query result hresult
  cases name
  change Nat at state
  change Bool at query
  change Costed CostModel.nat (Bool × Nat) at result
  change
    result ∈
      (PMF.pure
        (⟨(!query, state + 1), 3⟩ :
          Costed CostModel.nat (Bool × Nat))).support at hresult
  rw [PMF.mem_support_pure_iff] at hresult
  subst result
  exact Nat.le_refl 3

/-- Erasing the zero-cost lift recovers the original semantic environment. -/
example
    (env : OracleEnv testOracleSpec) (sec : CryptoLib.Core.SecPar)
    (state : env.State) (query : Bool) :
    (env.zeroCost CostModel.nat).erase.query TestOracle.bit sec state query =
      env.query TestOracle.bit sec state query := by
  exact CostedOracleEnv.erase_zeroCost_query env TestOracle.bit sec state query

theorem queryProgram_localBound (oracleQuery : Bool) :
    Oracle.Program.LocalCostBound
      (Oracle.Program.query TestOracle.bit oracleQuery :
        Oracle.Program natIssueCost (ULift Bool)) 1 := by
  intro value cost trace execution
  cases execution
  exact Nat.le_refl 1

theorem oneQueryProgram_localBound :
    Oracle.Program.LocalCostBound oneQueryProgram 1 := by
  exact queryProgram_localBound false

theorem queryProgram_totalQueryBound (oracleQuery : Bool) :
    Oracle.Program.TotalQueryBound
      (Oracle.Program.query TestOracle.bit oracleQuery :
        Oracle.Program natIssueCost (ULift Bool)) 1 := by
  intro value cost trace execution
  cases execution
  exact Nat.le_refl 1

theorem oneQueryProgram_totalQueryBound :
    Oracle.Program.TotalQueryBound oneQueryProgram 1 := by
  exact queryProgram_totalQueryBound false

theorem twoQueryProgram_localBound :
    Oracle.Program.LocalCostBound twoQueryProgram 2 := by
  unfold twoQueryProgram
  simpa using
    (Oracle.Program.LocalCostBound.bind
      (queryProgram_localBound false)
      (fun first => queryProgram_localBound first.down))

theorem twoQueryProgram_totalQueryBound :
    Oracle.Program.TotalQueryBound twoQueryProgram 2 := by
  unfold twoQueryProgram
  simpa using
    (Oracle.Program.TotalQueryBound.bind
      (queryProgram_totalQueryBound false)
      (fun first => queryProgram_totalQueryBound first.down))

theorem twoQueryProgram_queryBound :
    Oracle.Program.QueryBound twoQueryProgram (fun _name => 2) :=
  Oracle.Program.QueryBound.ofTotal twoQueryProgram_totalQueryBound

/-- Trace and cost projections of the one authoritative exact run. -/
def expectedTrace : QueryTrace testOracleSpec :=
  ⟨[TestOracle.bit, TestOracle.bit]⟩

def expectedExactResult :
    ExactRunResult CostModel.nat testOracleSpec Nat (ULift Bool) :=
  ⟨ULift.up false, 2, expectedTrace, 2, 6, 8⟩

theorem runExact_eq_expected :
    Oracle.Program.runExactFromInit twoQueryProgram 0 costedEnv =
      PMF.pure expectedExactResult := by
  simp only [Oracle.Program.runExactFromInit, twoQueryProgram,
    Oracle.Program.runExact, natIssueCost, costedEnv, PMF.pure_bind,
    Bool.not_false, Bool.not_true]
  change PMF.bind (PMF.pure _) _ = PMF.pure expectedExactResult
  rw [PMF.pure_bind]
  rfl

example : expectedTrace.count TestOracle.bit = 2 := by
  simp [expectedTrace, QueryTrace.count]

example : expectedTrace.total = 2 := by
  rfl

/-- Exact composition is two caller units plus two three-unit oracle calls. -/
example
    (result : Costed CostModel.nat (ULift Bool))
    (hresult :
      result ∈
        (Oracle.Program.runCosted twoQueryProgram 0 costedEnv).support) :
    result.cost ≤ 8 := by
  simpa only [Oracle.Program.repeatCost_nat] using
    Oracle.Program.runCosted_cost_le_composedBudget
      twoQueryProgram 0 costedEnv 2 2 3
      (Oracle.Program.repeatCost_nat_mono 3)
      Oracle.Program.costExchange_nat
      twoQueryProgram_localBound twoQueryProgram_totalQueryBound
      (costedEnv_queryCostBound.at 0) result hresult

/-- Cost erasure recovers the semantic environment without a second interpreter. -/
example :
    RandCosted.valueDist
        (Oracle.Program.runCosted twoQueryProgram 0 costedEnv) =
      Oracle.Program.runWithEnv twoQueryProgram 0 costedEnv.erase :=
  Oracle.Program.valueDist_runCosted_eq_runWithEnv_erase
    twoQueryProgram 0 costedEnv

/-! ## Input-dependent machine and implementation certificates -/

noncomputable def inputProgram (twice : Bool) : Oracle.Program natIssueCost (ULift Bool) :=
  if twice then twoQueryProgram else oneQueryProgram

theorem inputProgram_localBound (twice : Bool) :
    Oracle.Program.LocalCostBound (inputProgram twice) (if twice then 2 else 1) := by
  cases twice <;> simp [inputProgram, oneQueryProgram_localBound,
    twoQueryProgram_localBound]

theorem inputProgram_totalQueryBound (twice : Bool) :
    Oracle.Program.TotalQueryBound (inputProgram twice) (if twice then 2 else 1) := by
  cases twice <;> simp [inputProgram, oneQueryProgram_totalQueryBound,
    twoQueryProgram_totalQueryBound]

/-- Budgets depend on input; runtimes are uniform in input. -/
noncomputable def inputTimedMachine :
    TimedOracleMachine CostModel.nat NatMeasure.nat
      (fun _sec => Bool) (fun _sec _input => Bool)
      (fun _sec _input => testOracleSpec) where
  issueCost := fun _sec _input => natIssueCost
  program := fun _sec input => inputProgram input
  localBudget := fun _sec input => if input then 2 else 1
  queryBudget := fun _sec input _name => if input then 2 else 1
  totalQueryBudget := fun _sec input => if input then 2 else 1
  localRuntime := fun _sec => 2
  totalQueryRuntime := fun _sec => 2
  localBudget_sound := fun _sec input => inputProgram_localBound input
  queryBudget_sound := fun _sec input =>
    Oracle.Program.QueryBound.ofTotal (inputProgram_totalQueryBound input)
  totalQueryBudget_sound := fun _sec input => inputProgram_totalQueryBound input
  localBudget_le_runtime := by
    intro sec input
    cases input <;> decide
  totalQueryBudget_le_runtime := by
    intro sec input
    cases input <;> decide

/--
Polynomial annotations become a `PPTOracleMachine` only with an independent
admission for the exact caller program and its two claimed runtimes.
-/
noncomputable def inputPPTMachine
    (admission : PPTOracleAdmissible inputTimedMachine.toOracleMachine
      inputTimedMachine.localRuntime inputTimedMachine.totalQueryRuntime) :
    PPTOracleMachine CostModel.nat NatMeasure.nat
      (fun _sec => Bool) (fun _sec _input => Bool)
      (fun _sec _input => testOracleSpec) where
  toTimedOracleMachine := inputTimedMachine
  localRuntime_isPoly := IsPolyBounded.const 2
  totalQueryRuntime_isPoly := IsPolyBounded.const 2
  admission := admission

noncomputable def pptImplementation :
    PPTOracleImplementation CostModel.nat NatMeasure.nat
      (fun _sec => Bool) (fun _sec _input => testOracleSpec) where
  env := fun _sec _input => costedEnv
  queryBudget := fun _sec _input => 3
  queryRuntime := fun _sec => 3
  queryBudget_sound := fun sec input => costedEnv_queryCostBound.at sec
  queryBudget_le_runtime := by
    intro sec input
    exact Nat.le_refl 3
  repeatBudgetMono := by
    intro sec input first second hle
    exact Oracle.Program.repeatCost_nat_mono 3 hle
  queryRuntime_isPoly := IsPolyBounded.const 3

/-- The exact generic composition theorem is exposed by the machine layer. -/
example
    (result : Costed CostModel.nat Bool)
    (hresult :
      result ∈
        (inputTimedMachine.toOracleMachine.runWithImplementation
          pptImplementation.toOracleImplementation 0 true).support) :
    result.cost ≤ 8 := by
  simpa only [Oracle.Program.repeatCost_nat] using
    inputTimedMachine.runWithImplementation_cost_le
      pptImplementation.toTimedOracleImplementation
      Oracle.Program.costExchange_nat 0 true result hresult

/-- `NatMeasure` maps repeated exact query cost additively. -/
example :
    NatMeasure.nat
        (Oracle.Program.repeatCost CostModel.nat 2 3) = 6 := by
  change NatMeasure.nat (2 • (3 : Nat)) = 6
  rw [NatMeasure.map_nsmul]
  rfl

/-- Exact-to-measured composition has the expected uniform runtime. -/
example
    (callerAdmission : PPTOracleAdmissible inputTimedMachine.toOracleMachine
      inputTimedMachine.localRuntime inputTimedMachine.totalQueryRuntime)
    (closedAdmission : PPTAdmissible CostModel.nat NatMeasure.nat
      ((inputPPTMachine callerAdmission).toTimedOracleMachine.compose
        pptImplementation.toTimedOracleImplementation
        Oracle.Program.costExchange_nat).run
      (fun _sec => 8)) :
    ((inputPPTMachine callerAdmission).compose pptImplementation
      Oracle.Program.costExchange_nat closedAdmission).runtime =
      fun _sec => 8 := by
  rfl

/-- The composed runtime is certified polynomial through generic add/mul closure. -/
example
    (callerAdmission : PPTOracleAdmissible inputTimedMachine.toOracleMachine
      inputTimedMachine.localRuntime inputTimedMachine.totalQueryRuntime) :
    IsPolyBounded
      (fun sec =>
        (inputPPTMachine callerAdmission).localRuntime sec +
          (inputPPTMachine callerAdmission).totalQueryRuntime sec *
            pptImplementation.queryRuntime sec) :=
  (inputPPTMachine callerAdmission).composedRuntime_isPoly pptImplementation

/-! ## Noncommutative exact-order regression -/

inductive TraceEvent where
  | localFirst
  | oracleFirst
  | localSecond
  | oracleSecond
deriving DecidableEq, Repr

abbrev TraceCost :=
  CryptoLib.Test.Infrastructure.Computation.TraceCost TraceEvent

abbrev traceCostModel :=
  CryptoLib.Test.Infrastructure.Computation.TraceCost.costModel TraceEvent

def traceCost (event : TraceEvent) : TraceCost :=
  CryptoLib.Test.Infrastructure.Computation.TraceCost.singleton event

noncomputable def traceIssueCost :
    (name : testOracleSpec.Name) → testOracleSpec.Query name → traceCostModel.Cost :=
  fun name query =>
    match name with
    | .bit =>
        match query with
        | true => traceCost .localSecond
        | false => traceCost .localFirst

noncomputable def orderedTwoQueryProgram : Oracle.Program traceIssueCost (ULift Bool) := do
  let first ← Oracle.Program.query TestOracle.bit false
  Oracle.Program.query TestOracle.bit first.down

noncomputable def orderedCostedEnv :
    CostedOracleEnv traceCostModel testOracleSpec where
  State := Bool
  init := false
  query := fun name _sec seenSecond query =>
    match name with
    | .bit =>
        PMF.pure
          ⟨(!query, true),
            traceCost (if seenSecond then .oracleSecond else .oracleFirst)⟩

/-- Exact total cost records true execution order, never regrouped projections. -/
example :
    Oracle.Program.runCosted orderedTwoQueryProgram 0 orderedCostedEnv =
      PMF.pure
        ⟨ULift.up false,
          ⟨[.localFirst, .oracleFirst, .localSecond, .oracleSecond]⟩⟩ := by
  simp only [Oracle.Program.runCosted, Oracle.Program.runExactFromInit,
    orderedTwoQueryProgram, Oracle.Program.runExact, traceIssueCost,
    orderedCostedEnv, traceCost, PMF.pure_bind,
    Bool.not_false, Bool.not_true, Bool.false_eq_true,
    if_false, if_true]
  change PMF.map _ (PMF.bind (PMF.pure _) _) = _
  rw [PMF.pure_bind, PMF.pure_map]
  rfl

example :
    (⟨[.localFirst, .oracleFirst, .localSecond, .oracleSecond]⟩ : TraceCost) ≠
      ⟨[.localFirst, .localSecond, .oracleFirst, .oracleSecond]⟩ := by
  decide

end CryptoLib.Test.Infrastructure.Computation.CostedOracle

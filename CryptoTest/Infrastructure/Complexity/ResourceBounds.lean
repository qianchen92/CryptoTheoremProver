import Crypto.Infrastructure.Complexity.Basic

namespace CryptoTest.Infrastructure.Complexity.ResourceBounds

open Crypto.Infrastructure.Complexity
open Crypto.Infrastructure.Computation
open Crypto.Infrastructure.Computation.Algebra
open Crypto.Infrastructure.Computation.Cost
open Crypto.Infrastructure.Computation.Oracle

/-- A one-step machine used to ensure runtime bounds cover actual path annotations. -/
noncomputable def oneStepMachine :
    TimedMachine CostModel.nat NatMeasure.nat
      (fun _sec => Unit) (fun _sec _input => Bool) where
  toProbabilisticMachine :=
    { run := fun _sec _input => PMF.pure ⟨true, 1⟩ }
  certificate :=
    { toExactCostCertificate :=
        { budget := fun _sec _input => 1
          sound := by
            intro sec input result hresult
            rw [PMF.mem_support_pure_iff] at hresult
            subst result
            exact Nat.le_refl 1 }
      runtime := fun _sec => 1
      budget_le_runtime := by
        intro sec input
        exact Nat.le_refl 1 }

/-- The same costed computation cannot satisfy a zero runtime bound. -/
theorem oneStepMachine_not_zeroRuntime :
    ¬ RandCosted.CostBound (oneStepMachine.run 0 ()) 0 := by
  intro hzero
  have hbound := hzero ⟨true, 1⟩ (by
    change
      Costed.mk (M := CostModel.nat) true 1 ∈
        (PMF.pure
          (Costed.mk (M := CostModel.nat) true 1)).support
    rw [PMF.mem_support_pure_iff])
  exact Nat.not_succ_le_zero 0 hbound

/-- Erasing exact costs exposes only the machine's value distribution. -/
@[simp] theorem oneStepMachine_runDist
    (sec : Crypto.SecPar) :
    oneStepMachine.runDist sec () = PMF.pure true := by
  simp [oneStepMachine, ProbabilisticMachine.runDist,
    RandomizedComputation.valueDist]

/-! ## PPT admission boundary regressions -/

/-- Arbitrary host functions no longer have an automatic PPT constructor. -/
example : True := by
  fail_if_success
    have _machine :
        PPTMachine CostModel.nat NatMeasure.nat
          (fun _sec => Unit) (fun _sec _input => Bool) :=
      PPTMachine.ofFunction CostModel.nat NatMeasure.nat
        (fun _sec _input => true)
  trivial

/-- Arbitrary host-level value maps no longer preserve PPT admission. -/
example : True := by
  fail_if_success
    have _map :
        PPTMachine CostModel.nat NatMeasure.nat
            (fun _sec => Unit) (fun _sec _input => Unit) →
          PPTMachine CostModel.nat NatMeasure.nat
            (fun _sec => Unit) (fun _sec _input => Bool) :=
      fun machine => machine.map (fun _sec _input _value => true)
  trivial

/-- Polynomial annotation fields alone cannot construct a public PPT record. -/
example : True := by
  fail_if_success
    have _machine :
        PPTMachine CostModel.nat NatMeasure.nat
          (fun _sec => Unit) (fun _sec _input => Bool) :=
      { toTimedMachine := oneStepMachine
        runtime_poly :=
          Crypto.Infrastructure.Asymptotic.IsPolyBounded.const 1 }
  trivial

/-! ## Structural oracle resource certificates -/

inductive TestOracle where
  | query
deriving DecidableEq

def testOracleSpec : OracleSpec where
  Name := TestOracle
  Query
    | .query => Unit
  Response
    | .query => Unit

noncomputable def issueAlgebra :
    CostedAlgebra CostModel.nat (QueryIssue.signature testOracleSpec) :=
  QueryIssue.costAlgebra CostModel.nat testOracleSpec (fun _name _query => 1)

noncomputable def oneQueryProgram : Oracle.Program issueAlgebra (ULift Unit) :=
  Oracle.Program.query TestOracle.query ()

theorem oneQueryProgram_localBound :
    Oracle.Program.LocalCostBound oneQueryProgram 1 := by
  intro value cost trace execution
  unfold oneQueryProgram at execution
  cases execution with
  | query _ _ issueResult issueResult_mem _response =>
      simp only [issueAlgebra, QueryIssue.costAlgebra,
        RandCosted.liftCosted, PMF.mem_support_pure_iff] at issueResult_mem
      subst issueResult
      exact Nat.le_refl 1

theorem oneQueryProgram_totalQueryBound :
    Oracle.Program.TotalQueryBound oneQueryProgram 1 := by
  intro value cost trace execution
  unfold oneQueryProgram at execution
  cases execution
  exact Nat.le_refl 1

/-- The exact structural relation, not metadata, rules out a zero local bound. -/
theorem oneQueryProgram_not_zeroLocalBudget :
    ¬ Oracle.Program.LocalCostBound oneQueryProgram 0 := by
  intro hzero
  have issue_mem :
      (⟨(), 1⟩ : Costed CostModel.nat Unit) ∈
        (issueAlgebra.exec (.issue TestOracle.query ())).support := by
    change
      (⟨(), 1⟩ : Costed CostModel.nat Unit) ∈
        (PMF.pure (⟨(), 1⟩ : Costed CostModel.nat Unit)).support
    rw [PMF.mem_support_pure_iff]
  have execution :
      Oracle.Program.PossibleExecution oneQueryProgram
        (ULift.up ()) 1 (QueryTrace.singleton TestOracle.query) := by
    exact
      Oracle.Program.PossibleExecution.query
        (issueAlgebra := issueAlgebra)
        TestOracle.query () (⟨(), 1⟩ : Costed CostModel.nat Unit)
        issue_mem ()
  have hbound :=
    hzero (ULift.up ()) 1 (QueryTrace.singleton TestOracle.query) execution
  exact Nat.not_succ_le_zero 0 hbound

theorem oneQueryProgram_queryBound :
    Oracle.Program.QueryBound oneQueryProgram (fun _name => 1) :=
  Oracle.Program.QueryBound.ofTotal oneQueryProgram_totalQueryBound

/-! ## Adaptive exact-run projections -/

inductive AdaptiveOracle where
  | bit
deriving DecidableEq

def adaptiveOracleSpec : OracleSpec where
  Name := AdaptiveOracle
  Query
    | .bit => Bool
  Response
    | .bit => Bool

noncomputable def adaptiveIssueAlgebra :
    CostedAlgebra CostModel.nat (QueryIssue.signature adaptiveOracleSpec) :=
  QueryIssue.costAlgebra CostModel.nat adaptiveOracleSpec
    (fun _name _query => 1)

noncomputable def adaptiveTwoQueryProgram :
    Oracle.Program adaptiveIssueAlgebra (ULift Bool) := do
  let first ← Oracle.Program.query AdaptiveOracle.bit false
  Oracle.Program.query AdaptiveOracle.bit first.down

noncomputable def adaptiveOracleEnv : OracleEnv adaptiveOracleSpec where
  State := Nat
  init := 0
  query := fun name _sec state oracleQuery =>
    match name with
    | .bit => PMF.pure (!oracleQuery, state + 1)

theorem adaptiveQuery_localBound (oracleQuery : Bool) :
    Oracle.Program.LocalCostBound
      (Oracle.Program.query AdaptiveOracle.bit oracleQuery :
        Oracle.Program adaptiveIssueAlgebra (ULift Bool)) 1 := by
  intro value cost trace execution
  cases execution with
  | query _ _ issueResult issueResult_mem _response =>
      simp only [adaptiveIssueAlgebra, QueryIssue.costAlgebra,
        RandCosted.liftCosted, PMF.mem_support_pure_iff] at issueResult_mem
      subst issueResult
      exact Nat.le_refl 1

theorem adaptiveQuery_totalBound (oracleQuery : Bool) :
    Oracle.Program.TotalQueryBound
      (Oracle.Program.query AdaptiveOracle.bit oracleQuery :
        Oracle.Program adaptiveIssueAlgebra (ULift Bool)) 1 := by
  intro value cost trace execution
  cases execution
  exact Nat.le_refl 1

theorem adaptiveTwoQueryProgram_localBound :
    Oracle.Program.LocalCostBound adaptiveTwoQueryProgram 2 := by
  unfold adaptiveTwoQueryProgram
  simpa using
    (Oracle.Program.LocalCostBound.bind
      (adaptiveQuery_localBound false)
      (fun first => adaptiveQuery_localBound first.down))

theorem adaptiveTwoQueryProgram_totalBound :
    Oracle.Program.TotalQueryBound adaptiveTwoQueryProgram 2 := by
  unfold adaptiveTwoQueryProgram
  simpa using
    (Oracle.Program.TotalQueryBound.bind
      (adaptiveQuery_totalBound false)
      (fun first => adaptiveQuery_totalBound first.down))

/-- All machine certificates reference the same adaptive program. -/
noncomputable def adaptiveTimedMachine :
    TimedOracleMachine CostModel.nat NatMeasure.nat
      (fun _sec => Unit) (fun _sec _input => Bool)
      (fun _sec _input => adaptiveOracleSpec) where
  issueAlgebra := fun _sec _input => adaptiveIssueAlgebra
  program := fun _sec _input => adaptiveTwoQueryProgram
  localBudget := fun _sec _input => 2
  queryBudget := fun _sec _input _name => 2
  totalQueryBudget := fun _sec _input => 2
  localRuntime := fun _sec => 2
  totalQueryRuntime := fun _sec => 2
  localBudget_sound := fun _sec _input => adaptiveTwoQueryProgram_localBound
  queryBudget_sound := fun _sec _input =>
    Oracle.Program.QueryBound.ofTotal adaptiveTwoQueryProgram_totalBound
  totalQueryBudget_sound := fun _sec _input => adaptiveTwoQueryProgram_totalBound
  localBudget_le_runtime := fun _sec _input => Nat.le_refl 2
  totalQueryBudget_le_runtime := fun _sec _input => Nat.le_refl 2

def adaptiveExpectedTrace : QueryTrace adaptiveOracleSpec :=
  ⟨[AdaptiveOracle.bit, AdaptiveOracle.bit]⟩

def adaptiveExpectedResult :
    ExactRunResult CostModel.nat adaptiveOracleSpec Nat (ULift Bool) :=
  ⟨ULift.up false, 2, adaptiveExpectedTrace, 2, 0, 2⟩

theorem adaptiveRunExact_eq_expected :
    adaptiveTimedMachine.toOracleMachine.runExact
        0 () (adaptiveOracleEnv.zeroCost CostModel.nat) =
      PMF.pure adaptiveExpectedResult := by
  simp only [OracleMachine.runExact, Oracle.Program.runExactFromInit,
    adaptiveTimedMachine, adaptiveTwoQueryProgram, Oracle.Program.runExact,
    adaptiveIssueAlgebra, QueryIssue.costAlgebra, OracleEnv.zeroCost,
    adaptiveOracleEnv, RandCosted.sampleZeroCost,
    RandCosted.sampleWithCost, PMF.pure_bind, PMF.pure_map,
    Bool.not_false, Bool.not_true]
  change PMF.bind (PMF.pure _) _ = PMF.pure adaptiveExpectedResult
  rw [PMF.pure_bind]
  rfl

theorem adaptiveExpectedResult_mem_support :
    adaptiveExpectedResult ∈
      (adaptiveTimedMachine.toOracleMachine.runExact
        0 () (adaptiveOracleEnv.zeroCost CostModel.nat)).support := by
  rw [adaptiveRunExact_eq_expected]
  exact
    (PMF.mem_support_pure_iff adaptiveExpectedResult adaptiveExpectedResult).2 rfl

/-- The local projection is bounded through the machine certificate. -/
theorem adaptiveExpectedResult_localCost_le_runtime :
    NatMeasure.nat adaptiveExpectedResult.localCost ≤
      adaptiveTimedMachine.localRuntime 0 :=
  adaptiveTimedMachine.measuredLocalCost_le_runtime
    0 () (adaptiveOracleEnv.zeroCost CostModel.nat)
    adaptiveExpectedResult adaptiveExpectedResult_mem_support

/-- The independent total-query runtime bounds the exact trace. -/
theorem adaptiveExpectedResult_totalQueries_le_runtime :
    adaptiveExpectedResult.trace.total ≤
      adaptiveTimedMachine.totalQueryRuntime 0 :=
  adaptiveTimedMachine.totalQueries_le_runtime
    0 () (adaptiveOracleEnv.zeroCost CostModel.nat)
    adaptiveExpectedResult adaptiveExpectedResult_mem_support

/-- Total-query certification bounds each named endpoint count. -/
theorem adaptiveExpectedResult_queryCount_le_totalRuntime :
    adaptiveExpectedResult.trace.count AdaptiveOracle.bit ≤
      adaptiveTimedMachine.totalQueryRuntime 0 :=
  adaptiveTimedMachine.queryCount_le_totalQueryRuntime
    0 () (adaptiveOracleEnv.zeroCost CostModel.nat)
    adaptiveExpectedResult adaptiveExpectedResult_mem_support AdaptiveOracle.bit

/-- The separate per-name certificate is checked on the same exact result. -/
theorem adaptiveExpectedResult_queryCount_le_budget :
    adaptiveExpectedResult.trace.count AdaptiveOracle.bit ≤
      adaptiveTimedMachine.queryBudget 0 () AdaptiveOracle.bit :=
  adaptiveTimedMachine.queryCount_le_budget
    0 () (adaptiveOracleEnv.zeroCost CostModel.nat)
    adaptiveExpectedResult adaptiveExpectedResult_mem_support AdaptiveOracle.bit

end CryptoTest.Infrastructure.Complexity.ResourceBounds

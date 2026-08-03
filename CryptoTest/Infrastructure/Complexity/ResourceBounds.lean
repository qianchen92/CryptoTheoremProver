import Crypto.Infrastructure.Complexity.Machine

namespace CryptoTest.Infrastructure.Complexity.ResourceBounds

open Crypto.Infrastructure.Complexity
open Crypto.Infrastructure.Computation
open Crypto.Infrastructure.Computation.Oracle

/-- A one-step machine used to ensure runtime bounds cover actual path annotations. -/
noncomputable def oneStepMachine : TimedMachine Unit Bool where
  run := fun _sec _input => PMF.pure ⟨true, 1⟩
  runtime := fun _sec => 1
  runtime_sound := by
    intro sec input result hresult
    rw [PMF.mem_support_pure_iff] at hresult
    subst result
    exact Nat.le_refl 1

/-- The same costed computation cannot satisfy a zero runtime bound. -/
theorem oneStepMachine_not_zeroRuntime :
    ¬ RandomizedComputation.CostBound oneStepMachine.run (fun _sec => 0) := by
  intro hzero
  have hbound := hzero 0 () ⟨true, 1⟩ (by
    change
      Crypto.Infrastructure.Computation.Cost.Costed.mk true 1 ∈
        (PMF.pure
          (Crypto.Infrastructure.Computation.Cost.Costed.mk true 1)).support
    rw [PMF.mem_support_pure_iff])
  exact Nat.not_succ_le_zero 0 hbound

/-- Deterministic machines expose the cost produced by their computation itself. -/
def deterministicOneStep : DeterministicMachine Unit Bool where
  run := fun _sec _input => ⟨true, 1⟩
  runtime := fun _sec => 1
  runtime_sound := by
    intro sec input
    exact Nat.le_refl 1

@[simp] theorem deterministicOneStep_runDist
    (sec : Crypto.SecPar) :
    deterministicOneStep.toProbabilisticMachine.runDist sec () = PMF.pure true := by
  exact DeterministicMachine.toProbabilisticMachine_runDist
    deterministicOneStep sec ()

inductive TestOracle where
  | query

def testOracleSpec : OracleSpec where
  Name := TestOracle
  Query
    | TestOracle.query => Unit
  Response
    | TestOracle.query => Unit

def oneQueryProgram : OracleProgram testOracleSpec (ULift Unit) :=
  OracleProgram.query TestOracle.query ()

/-- One query has exactly one unit of profiled local cost. -/
theorem oneQueryProgram_costBound :
    OracleProgram.CostBound oneQueryProgram 1 := by
  intro value profile hexecution
  cases hexecution
  exact Nat.le_refl 1

/-- The structural execution relation rules out a zero cost bound for one query. -/
theorem oneQueryProgram_not_zeroCost :
    ¬ OracleProgram.CostBound oneQueryProgram 0 := by
  intro hzero
  have hexecution :
      OracleProgram.Execution oneQueryProgram
        (ULift.up ()) (OracleProfile.ofUnitCostQuery TestOracle.query) := by
    unfold oneQueryProgram
    exact
      OracleProgram.Execution.query
        (Spec := testOracleSpec) TestOracle.query () ()
  have hbound :=
    hzero (ULift.up ()) (OracleProfile.ofUnitCostQuery TestOracle.query)
    hexecution
  exact Nat.not_succ_le_zero 0 hbound

/-- The per-name query bound is derived from the structural query trace. -/
theorem oneQueryProgram_queryBound :
    OracleProgram.QueryBound oneQueryProgram (fun _name => 1) := by
  classical
  intro value profile hexecution name
  apply le_trans (OracleProfile.queryCount_le_totalQueries profile name)
  cases hexecution
  exact Nat.le_refl 1

inductive AdaptiveOracle where
  | bit
deriving DecidableEq

def adaptiveOracleSpec : OracleSpec where
  Name := AdaptiveOracle
  Query
    | AdaptiveOracle.bit => Bool
  Response
    | AdaptiveOracle.bit => Bool

/-- The second query is chosen from the response to the first query. -/
def adaptiveTwoQueryProgram : OracleProgram adaptiveOracleSpec (ULift Bool) :=
  OracleProgram.bind (OracleProgram.query AdaptiveOracle.bit false) fun first =>
    OracleProgram.query AdaptiveOracle.bit first.down

/-- A deterministic stateful environment that negates each queried bit. -/
noncomputable def adaptiveOracleEnv : OracleEnv adaptiveOracleSpec where
  State := Nat
  init := 0
  query := fun name _sec state oracleQuery =>
    match name with
    | AdaptiveOracle.bit => PMF.pure (!oracleQuery, state + 1)

/-- A timed machine whose structural path consists of exactly two adaptive queries. -/
noncomputable def adaptiveTimedMachine :
    TimedOracleMachine
      (fun _sec => Unit)
      (fun _sec => Bool)
      (fun _sec _input => adaptiveOracleSpec) where
  run := fun _sec _input => adaptiveTwoQueryProgram
  runtime := fun _sec => 2
  queryBound := fun _sec _input _name => 2
  runtime_sound := by
    intro sec input value profile execution
    change OracleProgram.Execution adaptiveTwoQueryProgram value profile at execution
    unfold adaptiveTwoQueryProgram at execution
    cases execution with
    | bind firstExecution secondExecution =>
        cases firstExecution
        cases secondExecution
        exact Nat.le_refl 2
  queryBound_sound := by
    classical
    intro sec input value profile execution name
    change OracleProgram.Execution adaptiveTwoQueryProgram value profile at execution
    unfold adaptiveTwoQueryProgram at execution
    cases execution with
    | bind firstExecution secondExecution =>
        cases firstExecution
        cases secondExecution
        cases name
        simp [OracleProfile.queryCount, OracleProfile.append]

/-- Total-query evidence is optional analysis data, not part of the machine type. -/
noncomputable def adaptiveTotalQueryCertificate :
    TotalQueryBoundCertificate adaptiveTimedMachine where
  totalQueryBound := fun _sec => 2
  totalQueryBound_sound := by
    intro sec input value profile execution
    change OracleProgram.Execution adaptiveTwoQueryProgram value profile at execution
    unfold adaptiveTwoQueryProgram at execution
    cases execution with
    | bind firstExecution secondExecution =>
        cases firstExecution
        cases secondExecution
        exact Nat.le_refl 2

def adaptiveExpectedProfile : OracleProfile adaptiveOracleSpec :=
  OracleProfile.append
    (OracleProfile.ofUnitCostQuery AdaptiveOracle.bit)
    (OracleProfile.ofUnitCostQuery AdaptiveOracle.bit)

def adaptiveExpectedResult :
    OracleProgram.RunResult adaptiveOracleSpec Nat (ULift Bool) :=
  ⟨ULift.up false, 2, adaptiveExpectedProfile⟩

theorem adaptiveExpectedResult_mem_support :
    adaptiveExpectedResult ∈
      (OracleProgram.runProfiledWithEnv
        (adaptiveTimedMachine.run 0 ()) 0 adaptiveOracleEnv).support := by
  have hrun :
      OracleProgram.runProfiledWithEnv
          (adaptiveTimedMachine.run 0 ()) 0 adaptiveOracleEnv =
        PMF.pure adaptiveExpectedResult := by
    simp only [
      adaptiveExpectedResult, adaptiveExpectedProfile, adaptiveTimedMachine,
      adaptiveTwoQueryProgram, adaptiveOracleEnv, OracleProgram.runProfiledWithEnv,
      OracleProgram.runProfiled, OracleProfile.append,
      OracleProfile.ofUnitCostQuery, PMF.pure_bind,
      Bool.not_false, Bool.not_true]
    change PMF.bind (PMF.pure _) _ = _
    rw [PMF.pure_bind]
    rfl
  rw [hrun]
  exact (PMF.mem_support_pure_iff adaptiveExpectedResult adaptiveExpectedResult).2 rfl

/--
The generic support-to-`Execution` bridge transfers the machine runtime
certificate to this concrete profiled interpreter result.
-/
theorem adaptiveExpectedResult_cost_le_runtime :
    adaptiveExpectedResult.profile.cost ≤ adaptiveTimedMachine.runtime 0 :=
  adaptiveTimedMachine.runProfiled_cost_le_runtime
    0 () adaptiveOracleEnv adaptiveExpectedResult adaptiveExpectedResult_mem_support

/-- The legacy runtime again bounds total queries unconditionally. -/
theorem adaptiveExpectedResult_totalQueries_le_runtime :
    adaptiveExpectedResult.profile.totalQueries ≤
      adaptiveTimedMachine.runtime 0 :=
  adaptiveTimedMachine.runProfiled_totalQueries_le_runtime
    0 () adaptiveOracleEnv adaptiveExpectedResult adaptiveExpectedResult_mem_support

/-- The legacy runtime also bounds each named query count unconditionally. -/
theorem adaptiveExpectedResult_queryCount_le_runtime :
    adaptiveExpectedResult.profile.queryCount AdaptiveOracle.bit ≤
      adaptiveTimedMachine.runtime 0 :=
  adaptiveTimedMachine.runProfiled_queryCount_le_runtime
    0 () adaptiveOracleEnv adaptiveExpectedResult
    adaptiveExpectedResult_mem_support AdaptiveOracle.bit

/--
The same concrete interpreter result satisfies the machine's per-oracle query
certificate.
-/
theorem adaptiveExpectedResult_queryCount_le :
    adaptiveExpectedResult.profile.queryCount AdaptiveOracle.bit ≤
      adaptiveTimedMachine.queryBound 0 () AdaptiveOracle.bit :=
  adaptiveTimedMachine.runProfiled_queryCount_le
    0 () adaptiveOracleEnv adaptiveExpectedResult adaptiveExpectedResult_mem_support
      AdaptiveOracle.bit

end CryptoTest.Infrastructure.Complexity.ResourceBounds

import Crypto.Infrastructure.Complexity.Machine
import Crypto.Infrastructure.Complexity.OracleImplementation

namespace Crypto.Infrastructure.Complexity

open Crypto.Infrastructure.Asymptotic
open Crypto.Infrastructure.Computation
open Crypto.Infrastructure.Computation.Algebra
open Crypto.Infrastructure.Computation.Cost
open Crypto.Infrastructure.Computation.Oracle

universe uCost uIn uOut uOracle uQuery uResponse uState

/--
An adaptive oracle machine over one exact caller-side cost model.

The machine stores a typed query-issuance algebra and one program.  Exact cost,
ordinary probability, final-state, and trace semantics are all projections of
`Oracle.Program.runExact`.
-/
structure OracleMachine
    (M : CostModel.{uCost})
    (Input : Crypto.SecPar → Type uIn)
    (Output : (sec : Crypto.SecPar) → Input sec → Type uOut)
    (Spec :
      (sec : Crypto.SecPar) → Input sec →
        OracleSpec.{uOracle, uQuery, uResponse}) where
  issueAlgebra :
    (sec : Crypto.SecPar) → (input : Input sec) →
      CostedAlgebra M (QueryIssue.signature (Spec sec input))
  program :
    (sec : Crypto.SecPar) → (input : Input sec) →
      Oracle.Program (issueAlgebra sec input)
        (ULift.{uResponse} (Output sec input))

namespace OracleMachine

variable
    {M : CostModel.{uCost}}
    {Input : Crypto.SecPar → Type uIn}
    {Output : (sec : Crypto.SecPar) → Input sec → Type uOut}
    {Spec :
      (sec : Crypto.SecPar) → Input sec →
        OracleSpec.{uOracle, uQuery, uResponse}}

/-- Run the machine through the sole exact oracle interpreter. -/
noncomputable def runExact
    (machine : OracleMachine M Input Output Spec)
    (sec : Crypto.SecPar) (input : Input sec)
    (env :
      CostedOracleEnv.{uCost, uOracle, uQuery, uResponse, uState}
        M (Spec sec input)) :
    PMF
      (ExactRunResult M (Spec sec input) env.State
        (ULift.{uResponse} (Output sec input))) :=
  Oracle.Program.runExactFromInit (machine.program sec input) sec env

/-- Retain the returned value and exact ordered composition cost. -/
noncomputable def runCosted
    (machine : OracleMachine M Input Output Spec)
    (sec : Crypto.SecPar) (input : Input sec)
    (env :
      CostedOracleEnv.{uCost, uOracle, uQuery, uResponse, uState}
        M (Spec sec input)) :
    RandCosted M (Output sec input) :=
  RandCosted.map ULift.down
    (Oracle.Program.runCosted (machine.program sec input) sec env)

/-- Ordinary value semantics against a cost-erased environment. -/
noncomputable def runWithEnv
    (machine : OracleMachine M Input Output Spec)
    (sec : Crypto.SecPar) (input : Input sec)
    (env : OracleEnv.{uOracle, uQuery, uResponse, uState} (Spec sec input)) :
    PMF (Output sec input) :=
  PMF.map ULift.down
    (Oracle.Program.runWithEnv (machine.program sec input) sec env)

/-- Exact composition with the authoritative implementation environment. -/
noncomputable def runWithImplementation
    (machine : OracleMachine M Input Output Spec)
    (implementation :
      OracleImplementation.{uCost, uIn, uOracle, uQuery, uResponse, uState}
        M Input Spec)
    (sec : Crypto.SecPar) (input : Input sec) :
    RandCosted M (Output sec input) :=
  machine.runCosted sec input (implementation.env sec input)

/-- Exact composition erases to the ordinary semantics of the same environment. -/
@[simp] theorem valueDist_runCosted
    (machine : OracleMachine M Input Output Spec)
    (sec : Crypto.SecPar) (input : Input sec)
    (env :
      CostedOracleEnv.{uCost, uOracle, uQuery, uResponse, uState}
        M (Spec sec input)) :
    RandCosted.valueDist (machine.runCosted sec input env) =
      machine.runWithEnv sec input env.erase := by
  simp only [runCosted, runWithEnv, RandCosted.valueDist_map]
  rw [Oracle.Program.valueDist_runCosted_eq_runWithEnv_erase]

/-- The implementation wrapper introduces no new probability semantics. -/
@[simp] theorem valueDist_runWithImplementation
    (machine : OracleMachine M Input Output Spec)
    (implementation :
      OracleImplementation.{uCost, uIn, uOracle, uQuery, uResponse, uState}
        M Input Spec)
    (sec : Crypto.SecPar) (input : Input sec) :
    RandCosted.valueDist
        (machine.runWithImplementation implementation sec input) =
      machine.runWithEnv sec input
        (implementation.env sec input).erase := by
  exact machine.valueDist_runCosted sec input (implementation.env sec input)

end OracleMachine

/--
An oracle machine with input-dependent path bounds and uniform measured local
and total-query runtimes.

All certificates refer to `program`; none stores a second executable body.
-/
structure TimedOracleMachine
    (M : CostModel.{uCost}) (measure : NatMeasure M)
    (Input : Crypto.SecPar → Type uIn)
    (Output : (sec : Crypto.SecPar) → Input sec → Type uOut)
    (Spec :
      (sec : Crypto.SecPar) → Input sec →
        OracleSpec.{uOracle, uQuery, uResponse})
    extends OracleMachine M Input Output Spec where
  localBudget : (sec : Crypto.SecPar) → Input sec → M.Cost
  queryBudget :
    (sec : Crypto.SecPar) → (input : Input sec) → (Spec sec input).Name → Nat
  totalQueryBudget : (sec : Crypto.SecPar) → Input sec → Nat
  localRuntime : Crypto.SecPar → Nat
  totalQueryRuntime : Crypto.SecPar → Nat
  localBudget_sound : ∀ sec input,
    Oracle.Program.LocalCostBound
      (program sec input) (localBudget sec input)
  queryBudget_sound : ∀ sec input,
    Oracle.Program.QueryBound
      (program sec input) (queryBudget sec input)
  totalQueryBudget_sound : ∀ sec input,
    Oracle.Program.TotalQueryBound
      (program sec input) (totalQueryBudget sec input)
  localBudget_le_runtime : ∀ sec input,
    measure (localBudget sec input) ≤ localRuntime sec
  totalQueryBudget_le_runtime : ∀ sec input,
    totalQueryBudget sec input ≤ totalQueryRuntime sec

/--
Operational realization of one exact oracle caller and its claimed local and
total-query runtimes.  The realization exposes a host-independent model, its
code object, and the equations identifying that code with this caller and
runtime pair.  Structural local-cost and query-count bounds do not validate
the code because oracle programs retain higher-order Lean boundaries.
-/
abbrev PPTOracleAdmissible
    {M : CostModel.{uCost}}
    {Input : Crypto.SecPar → Type uIn}
    {Output : (sec : Crypto.SecPar) → Input sec → Type uOut}
    {Spec :
      (sec : Crypto.SecPar) → Input sec →
        OracleSpec.{uOracle, uQuery, uResponse}}
    (machine : OracleMachine M Input Output Spec)
    (localRuntime totalQueryRuntime : Crypto.SecPar → Nat) : Prop :=
  OperationalRealization machine (localRuntime, totalQueryRuntime)

/--
Polynomial local and total-query runtimes over the same certified program,
together with independent host-level PPT admission.
-/
structure PPTOracleMachine
    (M : CostModel.{uCost}) (measure : NatMeasure M)
    (Input : Crypto.SecPar → Type uIn)
    (Output : (sec : Crypto.SecPar) → Input sec → Type uOut)
    (Spec :
      (sec : Crypto.SecPar) → Input sec →
        OracleSpec.{uOracle, uQuery, uResponse})
    extends TimedOracleMachine M measure Input Output Spec where
  localRuntime_isPoly : IsPolyBounded localRuntime
  totalQueryRuntime_isPoly : IsPolyBounded totalQueryRuntime
  admission : PPTOracleAdmissible toOracleMachine localRuntime totalQueryRuntime

namespace TimedOracleMachine

variable
    {M : CostModel.{uCost}} {measure : NatMeasure M}
    {Input : Crypto.SecPar → Type uIn}
    {Output : (sec : Crypto.SecPar) → Input sec → Type uOut}
    {Spec :
      (sec : Crypto.SecPar) → Input sec →
        OracleSpec.{uOracle, uQuery, uResponse}}

/-- A supported exact run respects the certified caller-local budget. -/
theorem localCost_le_budget
    (machine : TimedOracleMachine M measure Input Output Spec)
    (sec : Crypto.SecPar) (input : Input sec)
    (env :
      CostedOracleEnv.{uCost, uOracle, uQuery, uResponse, uState}
        M (Spec sec input))
    (result :
      ExactRunResult M (Spec sec input) env.State
        (ULift.{uResponse} (Output sec input)))
    (hresult : result ∈ (machine.runExact sec input env).support) :
    M.instPartialOrder.le result.localCost (machine.localBudget sec input) := by
  exact
    Oracle.Program.localCost_le_of_mem_support_runExact
      (machine.localBudget_sound sec input) sec env env.init result hresult

/-- Measuring a supported local path cost yields at most the uniform runtime. -/
theorem measuredLocalCost_le_runtime
    (machine : TimedOracleMachine M measure Input Output Spec)
    (sec : Crypto.SecPar) (input : Input sec)
    (env :
      CostedOracleEnv.{uCost, uOracle, uQuery, uResponse, uState}
        M (Spec sec input))
    (result :
      ExactRunResult M (Spec sec input) env.State
        (ULift.{uResponse} (Output sec input)))
    (hresult : result ∈ (machine.runExact sec input env).support) :
    measure result.localCost ≤ machine.localRuntime sec :=
  le_trans
    (measure.monotone_toNat
      (machine.localCost_le_budget sec input env result hresult))
    (machine.localBudget_le_runtime sec input)

/-- A supported exact run respects the certified per-name query budget. -/
theorem queryCount_le_budget
    (machine : TimedOracleMachine M measure Input Output Spec)
    (sec : Crypto.SecPar) (input : Input sec)
    (env :
      CostedOracleEnv.{uCost, uOracle, uQuery, uResponse, uState}
        M (Spec sec input))
    (result :
      ExactRunResult M (Spec sec input) env.State
        (ULift.{uResponse} (Output sec input)))
    (hresult : result ∈ (machine.runExact sec input env).support)
    (name : (Spec sec input).Name) :
    result.trace.count name ≤ machine.queryBudget sec input name := by
  exact
    Oracle.Program.queryCount_le_of_mem_support_runExact
      (machine.queryBudget_sound sec input) sec env env.init result hresult name

/-- A supported exact run respects the input-dependent total-query budget. -/
theorem totalQueries_le_budget
    (machine : TimedOracleMachine M measure Input Output Spec)
    (sec : Crypto.SecPar) (input : Input sec)
    (env :
      CostedOracleEnv.{uCost, uOracle, uQuery, uResponse, uState}
        M (Spec sec input))
    (result :
      ExactRunResult M (Spec sec input) env.State
        (ULift.{uResponse} (Output sec input)))
    (hresult : result ∈ (machine.runExact sec input env).support) :
    result.trace.total ≤ machine.totalQueryBudget sec input := by
  exact
    Oracle.Program.totalQueries_le_of_mem_support_runExact
      (machine.totalQueryBudget_sound sec input) sec env env.init result hresult

/-- The uniform total-query runtime bounds every supported execution. -/
theorem totalQueries_le_runtime
    (machine : TimedOracleMachine M measure Input Output Spec)
    (sec : Crypto.SecPar) (input : Input sec)
    (env :
      CostedOracleEnv.{uCost, uOracle, uQuery, uResponse, uState}
        M (Spec sec input))
    (result :
      ExactRunResult M (Spec sec input) env.State
        (ULift.{uResponse} (Output sec input)))
    (hresult : result ∈ (machine.runExact sec input env).support) :
    result.trace.total ≤ machine.totalQueryRuntime sec :=
  (machine.totalQueries_le_budget sec input env result hresult).trans
    (machine.totalQueryBudget_le_runtime sec input)

/-- Total-query certification also bounds every individual endpoint count. -/
theorem queryCount_le_totalQueryRuntime
    (machine : TimedOracleMachine M measure Input Output Spec)
    (sec : Crypto.SecPar) (input : Input sec)
    (env :
      CostedOracleEnv.{uCost, uOracle, uQuery, uResponse, uState}
        M (Spec sec input))
    (result :
      ExactRunResult M (Spec sec input) env.State
        (ULift.{uResponse} (Output sec input)))
    (hresult : result ∈ (machine.runExact sec input env).support)
    (name : (Spec sec input).Name) :
    result.trace.count name ≤ machine.totalQueryRuntime sec :=
  (result.trace.count_le_total name).trans
    (machine.totalQueries_le_runtime sec input env result hresult)

/--
Exact composition with a bounded implementation satisfies the generic coarse
bound from the sole oracle interpreter.
-/
theorem runWithImplementation_cost_le
    (machine : TimedOracleMachine M measure Input Output Spec)
    (implementation :
      TimedOracleImplementation.{uCost, uIn, uOracle, uQuery, uResponse, uState}
        M measure Input Spec)
    (exchange : Oracle.Program.CostExchange M)
    (sec : Crypto.SecPar) (input : Input sec)
    (result : Costed M (Output sec input))
    (hresult :
      result ∈
        (machine.toOracleMachine.runWithImplementation
          implementation.toOracleImplementation sec input).support) :
    M.instPartialOrder.le result.cost
      (M.instAddMonoid.add
        (machine.localBudget sec input)
        (Oracle.Program.repeatCost M
          (machine.totalQueryBudget sec input)
          (implementation.queryBudget sec input))) := by
  simp only [OracleMachine.runWithImplementation, OracleMachine.runCosted,
    RandCosted.map] at hresult
  rw [PMF.mem_support_map_iff] at hresult
  rcases hresult with ⟨liftedResult, hliftedResult, hresult⟩
  subst result
  exact
    Oracle.Program.runCosted_cost_le_composedBudget
      (machine.program sec input) sec (implementation.env sec input)
      (machine.localBudget sec input) (machine.totalQueryBudget sec input)
      (implementation.queryBudget sec input)
      (implementation.repeatBudgetMono sec input) exchange
      (machine.localBudget_sound sec input)
      (machine.totalQueryBudget_sound sec input)
      (implementation.queryBudget_sound sec input) liftedResult hliftedResult

/--
Compose the certified caller and implementation into an ordinary timed machine.

The resulting machine runs the same exact oracle execution; `NatMeasure` is
used only to certify the uniform natural runtime.
-/
noncomputable def compose
    (machine : TimedOracleMachine M measure Input Output Spec)
    (implementation :
      TimedOracleImplementation.{uCost, uIn, uOracle, uQuery, uResponse, uState}
        M measure Input Spec)
    (exchange : Oracle.Program.CostExchange M) :
    TimedMachine M measure Input Output where
  toProbabilisticMachine :=
    { run := fun sec input =>
        machine.toOracleMachine.runWithImplementation
          implementation.toOracleImplementation sec input }
  certificate :=
    { toExactCostCertificate :=
        { budget := fun sec input =>
            M.instAddMonoid.add
              (machine.localBudget sec input)
              (Oracle.Program.repeatCost M
                (machine.totalQueryBudget sec input)
                (implementation.queryBudget sec input))
          sound := fun sec input result hresult =>
            machine.runWithImplementation_cost_le
              implementation exchange sec input result hresult }
      runtime := fun sec =>
        machine.localRuntime sec +
          machine.totalQueryRuntime sec * implementation.queryRuntime sec
      budget_le_runtime := by
        intro sec input
        rw [NatMeasure.map_add]
        have repeatedCost :
            measure
                (Oracle.Program.repeatCost M
                  (machine.totalQueryBudget sec input)
                  (implementation.queryBudget sec input)) =
              machine.totalQueryBudget sec input *
                measure (implementation.queryBudget sec input) := by
          simpa only [Oracle.Program.repeatCost, Nat.nsmul_eq_mul] using
            measure.map_nsmul
              (machine.totalQueryBudget sec input)
              (implementation.queryBudget sec input)
        rw [repeatedCost]
        exact Nat.add_le_add
          (machine.localBudget_le_runtime sec input)
          (Nat.mul_le_mul
            (machine.totalQueryBudget_le_runtime sec input)
            (implementation.queryBudget_le_runtime sec input)) }

@[simp] theorem compose_runtime
    (machine : TimedOracleMachine M measure Input Output Spec)
    (implementation :
      TimedOracleImplementation.{uCost, uIn, uOracle, uQuery, uResponse, uState}
        M measure Input Spec)
    (exchange : Oracle.Program.CostExchange M) :
    (machine.compose implementation exchange).runtime =
      fun sec =>
        machine.localRuntime sec +
          machine.totalQueryRuntime sec * implementation.queryRuntime sec :=
  rfl

/-- Cost projection of the composition leaves its value distribution unchanged. -/
@[simp] theorem compose_runDist
    (machine : TimedOracleMachine M measure Input Output Spec)
    (implementation :
      TimedOracleImplementation.{uCost, uIn, uOracle, uQuery, uResponse, uState}
        M measure Input Spec)
    (exchange : Oracle.Program.CostExchange M)
    (sec : Crypto.SecPar) (input : Input sec) :
    (machine.compose implementation exchange).toProbabilisticMachine.runDist
        sec input =
      machine.toOracleMachine.runWithEnv sec input
        (implementation.env sec input).erase := by
  exact
    machine.toOracleMachine.valueDist_runWithImplementation
      implementation.toOracleImplementation sec input

end TimedOracleMachine

namespace PPTOracleMachine

variable
    {M : CostModel.{uCost}} {measure : NatMeasure M}
    {Input : Crypto.SecPar → Type uIn}
    {Output : (sec : Crypto.SecPar) → Input sec → Type uOut}
    {Spec :
      (sec : Crypto.SecPar) → Input sec →
        OracleSpec.{uOracle, uQuery, uResponse}}

/-- The standard caller/query/implementation runtime is polynomial. -/
theorem composedRuntime_isPoly
    (machine : PPTOracleMachine M measure Input Output Spec)
    (implementation :
      PPTOracleImplementation.{uCost, uIn, uOracle, uQuery, uResponse, uState}
        M measure Input Spec) :
    IsPolyBounded
      (fun sec =>
        machine.localRuntime sec +
          machine.totalQueryRuntime sec * implementation.queryRuntime sec) :=
  IsPolyBounded.add machine.localRuntime_isPoly
    (IsPolyBounded.mul machine.totalQueryRuntime_isPoly
      implementation.queryRuntime_isPoly)

/--
Compose exact PPT caller and implementation certificates into the ordinary PPT
machine hierarchy without changing their shared exact run.  Admission of the
closed run and composed runtime is an independent argument.
-/
noncomputable def compose
    (machine : PPTOracleMachine M measure Input Output Spec)
    (implementation :
      PPTOracleImplementation.{uCost, uIn, uOracle, uQuery, uResponse, uState}
        M measure Input Spec)
    (exchange : Oracle.Program.CostExchange M)
    (admission : PPTAdmissible
      (machine.toTimedOracleMachine.compose
        implementation.toTimedOracleImplementation exchange).run
      (fun sec =>
        machine.localRuntime sec +
          machine.totalQueryRuntime sec * implementation.queryRuntime sec)) :
    PPTMachine M measure Input Output :=
  PPTMachine.ofAdmittedTimedMachine
    (machine.toTimedOracleMachine.compose
      implementation.toTimedOracleImplementation exchange)
    (by
      simpa only [TimedOracleMachine.compose_runtime] using
        machine.composedRuntime_isPoly implementation)
    admission

@[simp] theorem compose_runtime
    (machine : PPTOracleMachine M measure Input Output Spec)
    (implementation :
      PPTOracleImplementation.{uCost, uIn, uOracle, uQuery, uResponse, uState}
        M measure Input Spec)
    (exchange : Oracle.Program.CostExchange M)
    (admission : PPTAdmissible
      (machine.toTimedOracleMachine.compose
        implementation.toTimedOracleImplementation exchange).run
      (fun sec =>
        machine.localRuntime sec +
          machine.totalQueryRuntime sec * implementation.queryRuntime sec)) :
    (machine.compose implementation exchange admission).runtime =
      fun sec =>
        machine.localRuntime sec +
          machine.totalQueryRuntime sec * implementation.queryRuntime sec :=
  rfl

/-- PPT composition has exactly the cost-erased value semantics of its timed core. -/
@[simp] theorem compose_runDist
    (machine : PPTOracleMachine M measure Input Output Spec)
    (implementation :
      PPTOracleImplementation.{uCost, uIn, uOracle, uQuery, uResponse, uState}
        M measure Input Spec)
    (exchange : Oracle.Program.CostExchange M)
    (admission : PPTAdmissible
      (machine.toTimedOracleMachine.compose
        implementation.toTimedOracleImplementation exchange).run
      (fun sec =>
        machine.localRuntime sec +
          machine.totalQueryRuntime sec * implementation.queryRuntime sec))
    (sec : Crypto.SecPar) (input : Input sec) :
    (machine.compose implementation exchange admission).toProbabilisticMachine.runDist
        sec input =
      machine.toOracleMachine.runWithEnv sec input
        (implementation.env sec input).erase := by
  exact
    machine.toTimedOracleMachine.compose_runDist
      implementation.toTimedOracleImplementation exchange sec input

end PPTOracleMachine

end Crypto.Infrastructure.Complexity

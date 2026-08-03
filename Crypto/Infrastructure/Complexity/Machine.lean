import Crypto.Infrastructure.Asymptotic.Bounds
import Crypto.Infrastructure.Complexity.CostBound
import Crypto.Infrastructure.Computation.Oracle.Costed
import Crypto.Infrastructure.Computation.Oracle.Interface
import Crypto.Infrastructure.Computation.Cost.Projection
import Mathlib.Probability.ProbabilityMassFunction.Monad

namespace Crypto.Infrastructure.Complexity

open Crypto.Infrastructure.Asymptotic

universe uCost uIn uOut uOracle uQuery uResponse uState

/-- A probabilistic machine with an explicit cost on every execution path.

The cost annotation is the complexity boundary of this semantic model: it is
checked by timed-machine bounds below, but it is not derived from Lean's host
evaluation or from a tape-level transition system. -/
structure ProbabilisticMachine (Input : Type uIn) (Output : Type uOut) where
  run : Crypto.Infrastructure.Computation.RandomizedComputationT
    Crypto.Infrastructure.Computation.Cost.CostModel.nat Input Output

namespace ProbabilisticMachine

/-- Forget path costs and expose the ordinary output distribution of a machine. -/
noncomputable def runDist
    {Input : Type uIn} {Output : Type uOut}
    (M : ProbabilisticMachine Input Output)
    (sec : Crypto.SecPar) (input : Input) :
    PMF Output :=
  Crypto.Infrastructure.Computation.RandomizedComputationT.valueDist M.run sec input

end ProbabilisticMachine

/-- A probabilistic machine equipped with a sound uniform path-cost bound. -/
structure TimedMachine (Input : Type uIn) (Output : Type uOut)
    extends ProbabilisticMachine Input Output where
  runtime : Crypto.SecPar → Nat
  runtime_sound :
    Crypto.Infrastructure.Computation.RandomizedComputationT.CostBound run runtime

/--
A probabilistic polynomial-time machine in the explicit path-cost model.

The `runtime_sound` field ties the polynomial bound to every execution path of
`run`.  The remaining trusted boundary is the cost annotation attached by the
computation itself; this interface does not attempt to measure Lean host
evaluation.
-/
structure PPTMachine (Input : Type uIn) (Output : Type uOut)
    extends TimedMachine Input Output where
  runtime_isPoly : IsPolyBounded runtime

namespace PPTMachine

/-- A PPT machine has polynomially bounded annotated path cost. -/
theorem isPolyCost
    {Input : Type uIn} {Output : Type uOut}
    (M : PPTMachine Input Output) :
    IsPolyCost M.run :=
  ⟨M.runtime, M.runtime_sound, M.runtime_isPoly⟩

end PPTMachine

/-- A path-costed probabilistic machine whose output type may depend on its input. -/
structure ProbabilisticDependentMachine
    (Input : Type uIn) (Output : Input → Type uOut) where
  run : Crypto.Infrastructure.Computation.DependentRandomizedComputationT
    Crypto.Infrastructure.Computation.Cost.CostModel.nat Input Output

namespace ProbabilisticDependentMachine

/-- Forget path costs and expose the dependent output distribution of a machine. -/
noncomputable def runDist
    {Input : Type uIn} {Output : Input → Type uOut}
    (M : ProbabilisticDependentMachine Input Output)
    (sec : Crypto.SecPar) (input : Input) :
    PMF (Output input) :=
  Crypto.Infrastructure.Computation.DependentRandomizedComputationT.valueDist M.run sec input

end ProbabilisticDependentMachine

/-- A dependent-output machine equipped with a sound uniform path-cost bound. -/
structure TimedDependentMachine
    (Input : Type uIn) (Output : Input → Type uOut)
    extends ProbabilisticDependentMachine Input Output where
  runtime : Crypto.SecPar → Nat
  runtime_sound :
    Crypto.Infrastructure.Computation.DependentRandomizedComputationT.CostBound run runtime

/--
A dependent-output probabilistic polynomial-time machine in the path-cost model.

As with `PPTMachine`, `runtime_sound` constrains every costed execution path.
-/
structure PPTDependentMachine
    (Input : Type uIn) (Output : Input → Type uOut)
    extends TimedDependentMachine Input Output where
  runtime_isPoly : IsPolyBounded runtime

namespace PPTDependentMachine

/-- A dependent PPT machine has polynomially bounded annotated path cost. -/
theorem isPolyCost
    {Input : Type uIn} {Output : Input → Type uOut}
    (M : PPTDependentMachine Input Output) :
    IsPolyDependentCost M.run :=
  ⟨M.runtime, M.runtime_sound, M.runtime_isPoly⟩

end PPTDependentMachine


/-- A probabilistic machine that builds an adaptive, exactly costed oracle program. -/
structure ProbabilisticOracleMachine
    (C : Crypto.Infrastructure.Computation.Cost.CostModel.{uCost})
    (Input : Crypto.SecPar → Type uIn) (Output : Crypto.SecPar → Type uOut)
    (Spec :
      (sec : Crypto.SecPar) →
      Input sec →
      Crypto.Infrastructure.Computation.Oracle.OracleSpec.{uOracle, uQuery, uResponse}) where
  run :
    (sec : Crypto.SecPar) →
    (input : Input sec) →
    Crypto.Infrastructure.Computation.Oracle.OracleProgram
      C (Spec sec input) (ULift.{uResponse} (Output sec))

/--
An oracle machine with exact local-resource, projected runtime, per-name query,
and total-query certificates.
-/
structure TimedOracleMachine
    (C : Crypto.Infrastructure.Computation.Cost.CostModel.{uCost})
    (measure : Crypto.Infrastructure.Computation.Cost.NatMeasure C)
    (Input : Crypto.SecPar → Type uIn) (Output : Crypto.SecPar → Type uOut)
    (Spec :
      (sec : Crypto.SecPar) →
      Input sec →
      Crypto.Infrastructure.Computation.Oracle.OracleSpec.{uOracle, uQuery, uResponse})
    extends ProbabilisticOracleMachine C Input Output Spec where
  costBound : (sec : Crypto.SecPar) → Input sec → C.Cost
  runtime : Crypto.SecPar → Nat
  queryBound :
    (sec : Crypto.SecPar) → (input : Input sec) → (Spec sec input).Name → Nat
  totalQueryBound : Crypto.SecPar → Nat
  costBound_sound :
    ∀ sec input,
      Crypto.Infrastructure.Computation.Oracle.OracleProgram.CostBound
        (run sec input) (costBound sec input)
  costBound_le_runtime :
    ∀ sec input, measure (costBound sec input) ≤ runtime sec
  queryBound_sound :
    ∀ sec input,
      Crypto.Infrastructure.Computation.Oracle.OracleProgram.QueryBound
        (run sec input) (queryBound sec input)
  totalQueryBound_sound :
    ∀ sec input,
      Crypto.Infrastructure.Computation.Oracle.OracleProgram.TotalQueryBound
        (run sec input) (totalQueryBound sec)

/--
A polynomial-time oracle machine. Polynomial local runtime and polynomial total
query count are independent requirements because exact query costs may be zero.
-/
structure PPTOracleMachine
    (C : Crypto.Infrastructure.Computation.Cost.CostModel.{uCost})
    (measure : Crypto.Infrastructure.Computation.Cost.NatMeasure C)
    (Input : Crypto.SecPar → Type uIn) (Output : Crypto.SecPar → Type uOut)
    (Spec :
      (sec : Crypto.SecPar) →
      Input sec →
      Crypto.Infrastructure.Computation.Oracle.OracleSpec.{uOracle, uQuery, uResponse})
    extends TimedOracleMachine C measure Input Output Spec where
  runtime_isPoly : IsPolyBounded runtime
  totalQueryBound_isPoly : IsPolyBounded totalQueryBound

namespace ProbabilisticOracleMachine

variable
    {C : Crypto.Infrastructure.Computation.Cost.CostModel.{uCost}}
    {Input : Crypto.SecPar → Type uIn} {Output : Crypto.SecPar → Type uOut}
    {Spec :
      (sec : Crypto.SecPar) →
      Input sec →
      Crypto.Infrastructure.Computation.Oracle.OracleSpec.{uOracle, uQuery, uResponse}}

/-- Interpret an oracle machine and discard the final oracle state and exact cost. -/
noncomputable def runWithEnv
    (machine : ProbabilisticOracleMachine C Input Output Spec)
    (sec : Crypto.SecPar)
    (input : Input sec)
    (env :
      Crypto.Infrastructure.Computation.Oracle.OracleEnv.{uOracle, uQuery, uResponse, uState}
        (Spec sec input)) :
    PMF (Output sec) :=
  PMF.map ULift.down
    (Crypto.Infrastructure.Computation.Oracle.OracleProgram.runWithEnv
      (machine.run sec input) sec env)

/-- Interpret a machine against an exact-cost oracle environment. -/
noncomputable def runCostedWithCostedEnv
    (machine : ProbabilisticOracleMachine C Input Output Spec)
    (sec : Crypto.SecPar)
    (input : Input sec)
    (env :
      Crypto.Infrastructure.Computation.Oracle.CostedOracleEnv.{uCost, uOracle, uQuery, uResponse, uState} C (Spec sec input)) :
    Crypto.Infrastructure.Computation.Cost.RandCostedT C (Output sec) :=
  Crypto.Infrastructure.Computation.Cost.RandCostedT.map ULift.down
    (Crypto.Infrastructure.Computation.Oracle.OracleProgram.runCostedWithCostedEnv
      (machine.run sec input) sec env)

/-- Erasing exact composed costs recovers the ordinary machine/environment semantics. -/
@[simp] theorem valueDist_runCostedWithCostedEnv
    (machine : ProbabilisticOracleMachine C Input Output Spec)
    (sec : Crypto.SecPar)
    (input : Input sec)
    (env :
      Crypto.Infrastructure.Computation.Oracle.CostedOracleEnv.{uCost, uOracle, uQuery, uResponse, uState} C (Spec sec input)) :
    Crypto.Infrastructure.Computation.Cost.RandCostedT.valueDist
        (machine.runCostedWithCostedEnv sec input env) =
      machine.runWithEnv sec input env.erase := by
  simp [runCostedWithCostedEnv, runWithEnv]

end ProbabilisticOracleMachine

namespace TimedOracleMachine

variable
    {C : Crypto.Infrastructure.Computation.Cost.CostModel.{uCost}}
    {measure : Crypto.Infrastructure.Computation.Cost.NatMeasure C}
    {Input : Crypto.SecPar → Type uIn} {Output : Crypto.SecPar → Type uOut}
    {Spec :
      (sec : Crypto.SecPar) →
      Input sec →
      Crypto.Infrastructure.Computation.Oracle.OracleSpec.{uOracle, uQuery, uResponse}}

/-- A profiled interpreter result follows an abstract path of the machine. -/
theorem execution_of_mem_support_runProfiled
    (machine : TimedOracleMachine C measure Input Output Spec)
    (sec : Crypto.SecPar)
    (input : Input sec)
    (env :
      Crypto.Infrastructure.Computation.Oracle.OracleEnv.{uOracle, uQuery, uResponse, uState} (Spec sec input))
    (result :
      Crypto.Infrastructure.Computation.Oracle.OracleProgram.RunResult
        C (Spec sec input) env.State (ULift.{uResponse} (Output sec)))
    (hresult :
      result ∈
        (Crypto.Infrastructure.Computation.Oracle.OracleProgram.runProfiledWithEnv
          (machine.run sec input) sec env).support) :
    Crypto.Infrastructure.Computation.Oracle.OracleProgram.Execution
      (machine.run sec input) result.value result.profile :=
  Crypto.Infrastructure.Computation.Oracle.OracleProgram.execution_of_mem_support_runProfiled
    (machine.run sec input) sec env env.init result hresult

/-- Every profiled result respects the machine's exact local-resource bound. -/
theorem runProfiled_cost_le_bound
    (machine : TimedOracleMachine C measure Input Output Spec)
    (sec : Crypto.SecPar)
    (input : Input sec)
    (env :
      Crypto.Infrastructure.Computation.Oracle.OracleEnv.{uOracle, uQuery, uResponse, uState} (Spec sec input))
    (result :
      Crypto.Infrastructure.Computation.Oracle.OracleProgram.RunResult
        C (Spec sec input) env.State (ULift.{uResponse} (Output sec)))
    (hresult :
      result ∈
        (Crypto.Infrastructure.Computation.Oracle.OracleProgram.runProfiledWithEnv
          (machine.run sec input) sec env).support) :
    C.instPartialOrder.le result.profile.cost (machine.costBound sec input) :=
  machine.costBound_sound sec input result.value result.profile
    (machine.execution_of_mem_support_runProfiled sec input env result hresult)

/-- Measuring an exact local cost yields the declared natural-number runtime. -/
theorem runProfiled_measuredCost_le_runtime
    (machine : TimedOracleMachine C measure Input Output Spec)
    (sec : Crypto.SecPar)
    (input : Input sec)
    (env :
      Crypto.Infrastructure.Computation.Oracle.OracleEnv.{uOracle, uQuery, uResponse, uState} (Spec sec input))
    (result :
      Crypto.Infrastructure.Computation.Oracle.OracleProgram.RunResult
        C (Spec sec input) env.State (ULift.{uResponse} (Output sec)))
    (hresult :
      result ∈
        (Crypto.Infrastructure.Computation.Oracle.OracleProgram.runProfiledWithEnv
          (machine.run sec input) sec env).support) :
    measure result.profile.cost ≤ machine.runtime sec :=
  le_trans
    (measure.monotone_toNat
      (machine.runProfiled_cost_le_bound sec input env result hresult))
    (machine.costBound_le_runtime sec input)

/-- Every profiled result respects all per-oracle query bounds. -/
theorem runProfiled_queryCount_le
    (machine : TimedOracleMachine C measure Input Output Spec)
    (sec : Crypto.SecPar)
    (input : Input sec)
    (env :
      Crypto.Infrastructure.Computation.Oracle.OracleEnv.{uOracle, uQuery, uResponse, uState} (Spec sec input))
    (result :
      Crypto.Infrastructure.Computation.Oracle.OracleProgram.RunResult
        C (Spec sec input) env.State (ULift.{uResponse} (Output sec)))
    (hresult :
      result ∈
        (Crypto.Infrastructure.Computation.Oracle.OracleProgram.runProfiledWithEnv
          (machine.run sec input) sec env).support)
    (name : (Spec sec input).Name) :
    result.profile.queryCount name ≤ machine.queryBound sec input name :=
  machine.queryBound_sound sec input result.value result.profile
    (machine.execution_of_mem_support_runProfiled sec input env result hresult) name

/-- Every profiled result respects the mandatory total-query bound. -/
theorem runProfiled_totalQueries_le
    (machine : TimedOracleMachine C measure Input Output Spec)
    (sec : Crypto.SecPar)
    (input : Input sec)
    (env :
      Crypto.Infrastructure.Computation.Oracle.OracleEnv.{uOracle, uQuery, uResponse, uState} (Spec sec input))
    (result :
      Crypto.Infrastructure.Computation.Oracle.OracleProgram.RunResult
        C (Spec sec input) env.State (ULift.{uResponse} (Output sec)))
    (hresult :
      result ∈
        (Crypto.Infrastructure.Computation.Oracle.OracleProgram.runProfiledWithEnv
          (machine.run sec input) sec env).support) :
    result.profile.totalQueries ≤ machine.totalQueryBound sec :=
  machine.totalQueryBound_sound sec input result.value result.profile
    (machine.execution_of_mem_support_runProfiled sec input env result hresult)

/-- The total-query certificate bounds every individual oracle count. -/
theorem runProfiled_queryCount_le_totalQueryBound
    (machine : TimedOracleMachine C measure Input Output Spec)
    (sec : Crypto.SecPar)
    (input : Input sec)
    (env :
      Crypto.Infrastructure.Computation.Oracle.OracleEnv.{uOracle, uQuery, uResponse, uState} (Spec sec input))
    (result :
      Crypto.Infrastructure.Computation.Oracle.OracleProgram.RunResult
        C (Spec sec input) env.State (ULift.{uResponse} (Output sec)))
    (hresult :
      result ∈
        (Crypto.Infrastructure.Computation.Oracle.OracleProgram.runProfiledWithEnv
          (machine.run sec input) sec env).support)
    (name : (Spec sec input).Name) :
    result.profile.queryCount name ≤ machine.totalQueryBound sec :=
  le_trans (result.profile.queryCount_le_totalQueries name)
    (machine.runProfiled_totalQueries_le sec input env result hresult)

/-- Exact cost of composition with a bounded costed oracle environment. -/
theorem runCostedWithCostedEnv_cost_le_composed
    (machine : TimedOracleMachine C measure Input Output Spec)
    (sec : Crypto.SecPar)
    (input : Input sec)
    (env :
      Crypto.Infrastructure.Computation.Oracle.CostedOracleEnv.{uCost, uOracle, uQuery, uResponse, uState} C (Spec sec input))
    (envBudget : Crypto.SecPar → C.Cost)
    (nsmulMono : ∀ {left right : Nat}, left ≤ right →
      C.instPartialOrder.le
        (Crypto.Infrastructure.Computation.Oracle.OracleProgram.repeatCost
          C left (envBudget sec))
        (Crypto.Infrastructure.Computation.Oracle.OracleProgram.repeatCost
          C right (envBudget sec)))
    (exchange : Crypto.Infrastructure.Computation.Oracle.OracleProgram.CostExchange C)
    (envBound : env.QueryCostBoundAt sec envBudget)
    (result : Crypto.Infrastructure.Computation.Cost.CostedT C (Output sec))
    (hresult :
      result ∈
        (machine.toProbabilisticOracleMachine.runCostedWithCostedEnv
          sec input env).support) :
    C.instPartialOrder.le result.cost
      (C.instAddMonoid.add
        (machine.costBound sec input)
        (Crypto.Infrastructure.Computation.Oracle.OracleProgram.repeatCost
          C (machine.totalQueryBound sec) (envBudget sec))) := by
  simp only [ProbabilisticOracleMachine.runCostedWithCostedEnv,
    Crypto.Infrastructure.Computation.Cost.RandCostedT.map] at hresult
  rw [PMF.mem_support_map_iff] at hresult
  rcases hresult with ⟨liftedResult, hliftedResult, hresult⟩
  subst result
  exact
    Crypto.Infrastructure.Computation.Oracle.OracleProgram.runCostedWithCostedEnv_cost_le
      (machine.run sec input) sec env (machine.costBound sec input)
      (machine.totalQueryBound sec) envBudget nsmulMono exchange
      (machine.costBound_sound sec input)
      (machine.totalQueryBound_sound sec input) envBound liftedResult hliftedResult

end TimedOracleMachine

namespace PPTOracleMachine

variable
    {C : Crypto.Infrastructure.Computation.Cost.CostModel.{uCost}}
    {measure : Crypto.Infrastructure.Computation.Cost.NatMeasure C}
    {Input : Crypto.SecPar → Type uIn} {Output : Crypto.SecPar → Type uOut}
    {Spec :
      (sec : Crypto.SecPar) →
      Input sec →
      Crypto.Infrastructure.Computation.Oracle.OracleSpec.{uOracle, uQuery, uResponse}}

/-- Every individual oracle count has the machine's polynomial total-query bound. -/
theorem runProfiled_queryCount_le_totalQueryBound
    (machine : PPTOracleMachine C measure Input Output Spec)
    (sec : Crypto.SecPar)
    (input : Input sec)
    (env :
      Crypto.Infrastructure.Computation.Oracle.OracleEnv.{uOracle, uQuery, uResponse, uState} (Spec sec input))
    (result :
      Crypto.Infrastructure.Computation.Oracle.OracleProgram.RunResult
        C (Spec sec input) env.State (ULift.{uResponse} (Output sec)))
    (hresult :
      result ∈
        (Crypto.Infrastructure.Computation.Oracle.OracleProgram.runProfiledWithEnv
          (machine.run sec input) sec env).support)
    (name : (Spec sec input).Name) :
    result.profile.queryCount name ≤ machine.totalQueryBound sec :=
  machine.toTimedOracleMachine.runProfiled_queryCount_le_totalQueryBound
    sec input env result hresult name

/-- Projected composition of a PPT machine and polynomial-cost oracle is polynomial. -/
theorem composedRuntime_isPoly
    (machine : PPTOracleMachine C measure Input Output Spec)
    (oracleRuntime : Crypto.SecPar → Nat)
    (oracleRuntime_isPoly : IsPolyBounded oracleRuntime) :
    IsPolyBounded
      (fun sec =>
        machine.runtime sec + machine.totalQueryBound sec * oracleRuntime sec) :=
  IsPolyBounded.composedOracle
    machine.runtime_isPoly machine.totalQueryBound_isPoly oracleRuntime_isPoly

end PPTOracleMachine

/--
A deterministic machine whose execution directly produces a costed result.

Execution produces its value and exact cost together. The generic interface
still trusts construction of that pair; concrete algebraic machines should use
`Program` when the cost must be generated compositionally from primitive
operations.
-/
structure DeterministicMachine (Input : Type uIn) (Output : Type uOut) where
  run :
    Crypto.SecPar → Input →
      Crypto.Infrastructure.Computation.Cost.CostedT
        Crypto.Infrastructure.Computation.Cost.CostModel.nat Output
  runtime : Crypto.SecPar → Nat
  runtime_sound : ∀ sec input, (run sec input).cost ≤ runtime sec

namespace DeterministicMachine

variable {Input : Type uIn} {Output : Type uOut}

/-- Forget the cost of a deterministic execution. -/
def runValue (M : DeterministicMachine Input Output)
    (sec : Crypto.SecPar) (input : Input) : Output :=
  (M.run sec input).val

/-- View a deterministic machine as a probabilistic machine concentrated on its output. -/
noncomputable def toProbabilisticMachine (M : DeterministicMachine Input Output) :
    ProbabilisticMachine Input Output where
  run sec input := PMF.pure (M.run sec input)

/-- View a deterministic timed machine as a timed probabilistic machine. -/
noncomputable def toTimedMachine (M : DeterministicMachine Input Output) :
    TimedMachine Input Output where
  run sec input := PMF.pure (M.run sec input)
  runtime := M.runtime
  runtime_sound := by
    intro sec input result hresult
    rw [PMF.mem_support_pure_iff] at hresult
    subst result
    exact M.runtime_sound sec input

/-- Promote a deterministic machine with a polynomial runtime bound to a PPT machine. -/
noncomputable def toPPTMachine (M : DeterministicMachine Input Output)
    (runtime_isPoly : IsPolyBounded M.runtime) : PPTMachine Input Output :=
  { M.toTimedMachine with runtime_isPoly := runtime_isPoly }

@[simp] theorem toProbabilisticMachine_run (M : DeterministicMachine Input Output)
    (sec : Crypto.SecPar) (input : Input) :
    M.toProbabilisticMachine.run sec input =
      PMF.pure (M.run sec input) :=
  rfl

@[simp] theorem toProbabilisticMachine_runDist (M : DeterministicMachine Input Output)
    (sec : Crypto.SecPar) (input : Input) :
    M.toProbabilisticMachine.runDist sec input = PMF.pure (M.runValue sec input) := by
  exact PMF.pure_map (f := Crypto.Infrastructure.Computation.Cost.CostedT.val)
    (M.run sec input)

@[simp] theorem toTimedMachine_runtime (M : DeterministicMachine Input Output) :
    M.toTimedMachine.runtime = M.runtime :=
  rfl

@[simp] theorem toPPTMachine_runtime (M : DeterministicMachine Input Output)
    (runtime_isPoly : IsPolyBounded M.runtime) :
    (M.toPPTMachine runtime_isPoly).runtime = M.runtime :=
  rfl

end DeterministicMachine

abbrev DeciderMachine (Input : Type uIn) := PPTMachine Input Bool

end Crypto.Infrastructure.Complexity

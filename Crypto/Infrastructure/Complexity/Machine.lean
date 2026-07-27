import Crypto.Infrastructure.Asymptotic.Bounds
import Crypto.Infrastructure.Complexity.CostBound
import Crypto.Infrastructure.Computation.Oracle.Interface
import Mathlib.Probability.ProbabilityMassFunction.Monad

namespace Crypto.Infrastructure.Complexity

open Crypto.Infrastructure.Asymptotic

universe uIn uOut uOracle uQuery uResponse uState

/-- A probabilistic machine with an explicit cost on every execution path.

The cost annotation is the complexity boundary of this semantic model: it is
checked by timed-machine bounds below, but it is not derived from Lean's host
evaluation or from a tape-level transition system. -/
structure ProbabilisticMachine (Input : Type uIn) (Output : Type uOut) where
  run : Crypto.Infrastructure.Computation.RandomizedComputation Input Output

namespace ProbabilisticMachine

/-- Forget path costs and expose the ordinary output distribution of a machine. -/
noncomputable def runDist
    {Input : Type uIn} {Output : Type uOut}
    (M : ProbabilisticMachine Input Output)
    (sec : Crypto.SecPar) (input : Input) :
    PMF Output :=
  Crypto.Infrastructure.Computation.RandomizedComputation.valueDist M.run sec input

end ProbabilisticMachine

/-- A probabilistic machine equipped with a sound uniform path-cost bound. -/
structure TimedMachine (Input : Type uIn) (Output : Type uOut)
    extends ProbabilisticMachine Input Output where
  runtime : Crypto.SecPar → Nat
  runtime_sound :
    Crypto.Infrastructure.Computation.RandomizedComputation.CostBound run runtime

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
  run : Crypto.Infrastructure.Computation.DependentRandomizedComputation Input Output

namespace ProbabilisticDependentMachine

/-- Forget path costs and expose the dependent output distribution of a machine. -/
noncomputable def runDist
    {Input : Type uIn} {Output : Input → Type uOut}
    (M : ProbabilisticDependentMachine Input Output)
    (sec : Crypto.SecPar) (input : Input) :
    PMF (Output input) :=
  Crypto.Infrastructure.Computation.DependentRandomizedComputation.valueDist M.run sec input

end ProbabilisticDependentMachine

/-- A dependent-output machine equipped with a sound uniform path-cost bound. -/
structure TimedDependentMachine
    (Input : Type uIn) (Output : Input → Type uOut)
    extends ProbabilisticDependentMachine Input Output where
  runtime : Crypto.SecPar → Nat
  runtime_sound :
    Crypto.Infrastructure.Computation.DependentRandomizedComputation.CostBound run runtime

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

/-- A probabilistic machine that builds an adaptive oracle program. -/
structure ProbabilisticOracleMachine
    (Input : Crypto.SecPar → Type uIn) (Output : Crypto.SecPar → Type uOut)
    (Spec :
      (sec : Crypto.SecPar) →
      Input sec →
      Crypto.Infrastructure.Computation.Oracle.OracleSpec.{uOracle, uQuery, uResponse}) where
  run :
    (sec : Crypto.SecPar) →
    (input : Input sec) →
    Crypto.Infrastructure.Computation.Oracle.OracleProgram.{
      uOracle, uQuery, uResponse, uOut} (Spec sec input) (ULift.{uResponse} (Output sec))

/--
An oracle machine with a sound uniform runtime and explicit per-oracle query
bounds, which may depend on the input.

Both bounds must hold for every structural execution path of the machine's
adaptive oracle program.
-/
structure TimedOracleMachine
    (Input : Crypto.SecPar → Type uIn) (Output : Crypto.SecPar → Type uOut)
    (Spec :
      (sec : Crypto.SecPar) →
      Input sec →
      Crypto.Infrastructure.Computation.Oracle.OracleSpec.{uOracle, uQuery, uResponse})
    extends ProbabilisticOracleMachine Input Output Spec where
  runtime : Crypto.SecPar → Nat
  queryBound : (sec : Crypto.SecPar) → (input : Input sec) → (Spec sec input).Name → Nat
  runtime_sound :
    ∀ sec input,
      Crypto.Infrastructure.Computation.Oracle.OracleProgram.CostBound
        (run sec input) (runtime sec)
  queryBound_sound :
    ∀ sec input,
      Crypto.Infrastructure.Computation.Oracle.OracleProgram.QueryBound
        (run sec input) (queryBound sec input)

/--
A probabilistic polynomial-time oracle machine in the profiled path-cost model.

`runtime_sound` and `queryBound_sound` connect the declared bounds to `run`;
`runtime_isPoly` provides a uniform polynomial bound on both path cost and
query count because each oracle query contributes one unit of cost.
`queryBound` can record a tighter, per-oracle certificate.  As for
ordinary machines, local cost annotations remain the trusted boundary of this
model.
-/
structure PPTOracleMachine
    (Input : Crypto.SecPar → Type uIn) (Output : Crypto.SecPar → Type uOut)
    (Spec :
      (sec : Crypto.SecPar) →
      Input sec →
      Crypto.Infrastructure.Computation.Oracle.OracleSpec.{uOracle, uQuery, uResponse})
    extends TimedOracleMachine Input Output Spec where
  runtime_isPoly : IsPolyBounded runtime

namespace ProbabilisticOracleMachine

variable
    {Input : Crypto.SecPar → Type uIn} {Output : Crypto.SecPar → Type uOut}
    {Spec :
      (sec : Crypto.SecPar) →
      Input sec →
      Crypto.Infrastructure.Computation.Oracle.OracleSpec.{uOracle, uQuery, uResponse}}

/-- Interpret an oracle machine against an environment and discard the final oracle state. -/
noncomputable def runWithEnv
    (M : ProbabilisticOracleMachine Input Output Spec)
    (sec : Crypto.SecPar)
    (input : Input sec)
    (env :
      Crypto.Infrastructure.Computation.Oracle.OracleEnv.{uOracle, uQuery, uResponse, uState}
        (Spec sec input)) :
    PMF (Output sec) :=
  PMF.map ULift.down
    (Crypto.Infrastructure.Computation.Oracle.OracleProgram.runWithEnv
      (M.run sec input) sec env)

end ProbabilisticOracleMachine

namespace TimedOracleMachine

variable
    {Input : Crypto.SecPar → Type uIn} {Output : Crypto.SecPar → Type uOut}
    {Spec :
      (sec : Crypto.SecPar) →
      Input sec →
      Crypto.Infrastructure.Computation.Oracle.OracleSpec.{uOracle, uQuery, uResponse}}

/-- A profiled interpreter result follows an abstract path of the machine. -/
theorem execution_of_mem_support_runProfiled
    (M : TimedOracleMachine Input Output Spec)
    (sec : Crypto.SecPar)
    (input : Input sec)
    (env :
      Crypto.Infrastructure.Computation.Oracle.OracleEnv.{uOracle,
        uQuery, uResponse, uState} (Spec sec input))
    (result :
      Crypto.Infrastructure.Computation.Oracle.OracleProgram.RunResult
        (Spec sec input) env.State (ULift.{uResponse} (Output sec)))
    (hresult :
      result ∈
        (Crypto.Infrastructure.Computation.Oracle.OracleProgram.runProfiledWithEnv
          (M.run sec input) sec env).support) :
    Crypto.Infrastructure.Computation.Oracle.OracleProgram.Execution
      (M.run sec input) result.value result.profile :=
  Crypto.Infrastructure.Computation.Oracle.OracleProgram.execution_of_mem_support_runProfiled
    (M.run sec input) sec env env.init result hresult

/-- Every profiled interpreter result respects the machine's runtime bound. -/
theorem runProfiled_cost_le_runtime
    (M : TimedOracleMachine Input Output Spec)
    (sec : Crypto.SecPar)
    (input : Input sec)
    (env :
      Crypto.Infrastructure.Computation.Oracle.OracleEnv.{uOracle,
        uQuery, uResponse, uState} (Spec sec input))
    (result :
      Crypto.Infrastructure.Computation.Oracle.OracleProgram.RunResult
        (Spec sec input) env.State (ULift.{uResponse} (Output sec)))
    (hresult :
      result ∈
        (Crypto.Infrastructure.Computation.Oracle.OracleProgram.runProfiledWithEnv
          (M.run sec input) sec env).support) :
    result.profile.cost ≤ M.runtime sec :=
  M.runtime_sound sec input result.value result.profile
    (M.execution_of_mem_support_runProfiled sec input env result hresult)

/-- Every profiled interpreter result respects all per-oracle query bounds. -/
theorem runProfiled_queryCount_le
    (M : TimedOracleMachine Input Output Spec)
    (sec : Crypto.SecPar)
    (input : Input sec)
    (env :
      Crypto.Infrastructure.Computation.Oracle.OracleEnv.{uOracle,
        uQuery, uResponse, uState} (Spec sec input))
    (result :
      Crypto.Infrastructure.Computation.Oracle.OracleProgram.RunResult
        (Spec sec input) env.State (ULift.{uResponse} (Output sec)))
    (hresult :
      result ∈
        (Crypto.Infrastructure.Computation.Oracle.OracleProgram.runProfiledWithEnv
          (M.run sec input) sec env).support)
    (name : (Spec sec input).Name) :
    result.profile.queryCount name ≤ M.queryBound sec input name :=
  M.queryBound_sound sec input result.value result.profile
    (M.execution_of_mem_support_runProfiled sec input env result hresult) name

/-- The runtime bound also bounds the total number of oracle calls. -/
theorem runProfiled_totalQueries_le_runtime
    (M : TimedOracleMachine Input Output Spec)
    (sec : Crypto.SecPar)
    (input : Input sec)
    (env :
      Crypto.Infrastructure.Computation.Oracle.OracleEnv.{uOracle,
        uQuery, uResponse, uState} (Spec sec input))
    (result :
      Crypto.Infrastructure.Computation.Oracle.OracleProgram.RunResult
        (Spec sec input) env.State (ULift.{uResponse} (Output sec)))
    (hresult :
      result ∈
        (Crypto.Infrastructure.Computation.Oracle.OracleProgram.runProfiledWithEnv
          (M.run sec input) sec env).support) :
    result.profile.totalQueries ≤ M.runtime sec := by
  have hexecution :=
    M.execution_of_mem_support_runProfiled sec input env result hresult
  exact le_trans hexecution.totalQueries_le_cost
    (M.runProfiled_cost_le_runtime sec input env result hresult)

/-- The runtime bound also bounds the number of calls to each oracle. -/
theorem runProfiled_queryCount_le_runtime
    (M : TimedOracleMachine Input Output Spec)
    (sec : Crypto.SecPar)
    (input : Input sec)
    (env :
      Crypto.Infrastructure.Computation.Oracle.OracleEnv.{uOracle,
        uQuery, uResponse, uState} (Spec sec input))
    (result :
      Crypto.Infrastructure.Computation.Oracle.OracleProgram.RunResult
        (Spec sec input) env.State (ULift.{uResponse} (Output sec)))
    (hresult :
      result ∈
        (Crypto.Infrastructure.Computation.Oracle.OracleProgram.runProfiledWithEnv
          (M.run sec input) sec env).support)
    (name : (Spec sec input).Name) :
    result.profile.queryCount name ≤ M.runtime sec :=
  le_trans (result.profile.queryCount_le_totalQueries name)
    (M.runProfiled_totalQueries_le_runtime sec input env result hresult)

end TimedOracleMachine

namespace PPTOracleMachine

variable
    {Input : Crypto.SecPar → Type uIn} {Output : Crypto.SecPar → Type uOut}
    {Spec :
      (sec : Crypto.SecPar) →
      Input sec →
      Crypto.Infrastructure.Computation.Oracle.OracleSpec.{uOracle, uQuery, uResponse}}

/--
Every per-oracle query count is bounded by the machine's polynomial runtime.

Together with `runtime_isPoly`, this makes `runtime` the uniform polynomial
query bound; the inherited `queryBound` may record a tighter bound.
-/
theorem runProfiled_queryCount_le_runtime
    (M : PPTOracleMachine Input Output Spec)
    (sec : Crypto.SecPar)
    (input : Input sec)
    (env :
      Crypto.Infrastructure.Computation.Oracle.OracleEnv.{uOracle,
        uQuery, uResponse, uState} (Spec sec input))
    (result :
      Crypto.Infrastructure.Computation.Oracle.OracleProgram.RunResult
        (Spec sec input) env.State (ULift.{uResponse} (Output sec)))
    (hresult :
      result ∈
        (Crypto.Infrastructure.Computation.Oracle.OracleProgram.runProfiledWithEnv
          (M.run sec input) sec env).support)
    (name : (Spec sec input).Name) :
    result.profile.queryCount name ≤ M.runtime sec :=
  M.toTimedOracleMachine.runProfiled_queryCount_le_runtime
    sec input env result hresult name

end PPTOracleMachine

/--
A deterministic machine whose execution directly produces a costed result.

This removes the older split between an uncosted result and an unrelated
top-level cost function.  The generic interface still trusts construction of
the `Costed` result; concrete algebraic machines should use `Program` when the
cost must be generated compositionally from primitive operations.
-/
structure DeterministicMachine (Input : Type uIn) (Output : Type uOut) where
  run :
    Crypto.SecPar → Input →
      Crypto.Infrastructure.Computation.Cost.Costed Output
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
  exact PMF.pure_map (f := Crypto.Infrastructure.Computation.Cost.Costed.val)
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

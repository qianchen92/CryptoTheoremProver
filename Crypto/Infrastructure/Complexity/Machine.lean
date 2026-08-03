import Crypto.Infrastructure.Asymptotic.Bounds
import Crypto.Infrastructure.Complexity.CostBound
import Crypto.Infrastructure.Computation.Oracle.Costed
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
An oracle machine with sound bounds for local work and per-oracle queries.

This is the legacy public adversary interface used by security definitions.
Its unit-cost query syntax makes `runtime` a sound total-query bound.  Optional
independent total-query information is attached separately below for
compositional oracle-cost analyses without changing this adversary class.
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

The inherited soundness fields connect the declared bounds to `run`;
the unit-cost query syntax and `runtime_isPoly` retain the original polynomial
query guarantee and public adversary domain.  A separate certificate can
record a different polynomial total-query bound for composition analyses.
-/
structure PPTOracleMachine
    (Input : Crypto.SecPar → Type uIn) (Output : Crypto.SecPar → Type uOut)
    (Spec :
      (sec : Crypto.SecPar) →
      Input sec →
      Crypto.Infrastructure.Computation.Oracle.OracleSpec.{uOracle, uQuery, uResponse})
    extends TimedOracleMachine Input Output Spec where
  runtime_isPoly : IsPolyBounded runtime

/--
An optional total-query certificate for an existing timed oracle machine.

Keeping this certificate separate is semantically important: it can provide a
dedicated or tighter bound for composed-oracle accounting without adding a
required field to the legacy machine type quantified by security notions.
-/
structure TotalQueryBoundCertificate
    {Input : Crypto.SecPar → Type uIn} {Output : Crypto.SecPar → Type uOut}
    {Spec :
      (sec : Crypto.SecPar) →
      Input sec →
      Crypto.Infrastructure.Computation.Oracle.OracleSpec.{uOracle, uQuery, uResponse}}
    (M : TimedOracleMachine Input Output Spec) where
  totalQueryBound : Crypto.SecPar → Nat
  totalQueryBound_sound :
    ∀ sec input,
      Crypto.Infrastructure.Computation.Oracle.OracleProgram.TotalQueryBound
        (M.run sec input) (totalQueryBound sec)

/-- A polynomial total-query certificate for an existing PPT oracle machine. -/
structure PolyTotalQueryBoundCertificate
    {Input : Crypto.SecPar → Type uIn} {Output : Crypto.SecPar → Type uOut}
    {Spec :
      (sec : Crypto.SecPar) →
      Input sec →
      Crypto.Infrastructure.Computation.Oracle.OracleSpec.{uOracle, uQuery, uResponse}}
    (M : PPTOracleMachine Input Output Spec)
    extends TotalQueryBoundCertificate M.toTimedOracleMachine where
  totalQueryBound_isPoly : IsPolyBounded totalQueryBound

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

/--
Interpret an oracle machine against an implemented, internally costed oracle.
The resulting path cost includes both the machine profile and oracle work.
-/
noncomputable def runCostedWithCostedEnv
    (M : ProbabilisticOracleMachine Input Output Spec)
    (sec : Crypto.SecPar)
    (input : Input sec)
    (env :
      Crypto.Infrastructure.Computation.Oracle.CostedOracleEnv.{uOracle,
        uQuery, uResponse, uState} (Spec sec input)) :
    Crypto.Infrastructure.Computation.Cost.RandCosted (Output sec) :=
  Crypto.Infrastructure.Computation.Cost.RandCosted.map ULift.down
    (Crypto.Infrastructure.Computation.Oracle.OracleProgram.runCostedWithCostedEnv
      (M.run sec input) sec env)

/-- Erasing composed costs recovers the ordinary machine/environment semantics. -/
@[simp] theorem valueDist_runCostedWithCostedEnv
    (M : ProbabilisticOracleMachine Input Output Spec)
    (sec : Crypto.SecPar)
    (input : Input sec)
    (env :
      Crypto.Infrastructure.Computation.Oracle.CostedOracleEnv.{uOracle,
        uQuery, uResponse, uState} (Spec sec input)) :
    Crypto.Infrastructure.Computation.Cost.RandCosted.valueDist
        (M.runCostedWithCostedEnv sec input env) =
      M.runWithEnv sec input env.erase := by
  simp [runCostedWithCostedEnv, runWithEnv]

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

/-- The runtime bound also bounds the total number of legacy oracle calls. -/
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
  exact le_trans
    (M.execution_of_mem_support_runProfiled sec input env result hresult
      |>.totalQueries_le_cost)
    (M.runProfiled_cost_le_runtime sec input env result hresult)

/-- The runtime bound also bounds the number of calls to each legacy oracle. -/
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

/-- Every profiled interpreter result respects the total-query bound. -/
theorem runProfiled_totalQueries_le
    (M : TimedOracleMachine Input Output Spec)
    (certificate : TotalQueryBoundCertificate M)
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
    result.profile.totalQueries ≤ certificate.totalQueryBound sec :=
  certificate.totalQueryBound_sound sec input result.value result.profile
    (M.execution_of_mem_support_runProfiled sec input env result hresult)

/--
Running a timed oracle machine with a uniformly bounded costed oracle has the
composed path bound `runtime + totalQueryBound * oracleBudget`.
-/
theorem runCostedWithCostedEnv_cost_le_composed
    (M : TimedOracleMachine Input Output Spec)
    (certificate : TotalQueryBoundCertificate M)
    (sec : Crypto.SecPar)
    (input : Input sec)
    (env :
      Crypto.Infrastructure.Computation.Oracle.CostedOracleEnv.{uOracle,
        uQuery, uResponse, uState} (Spec sec input))
    (oracleBudget : Crypto.SecPar → Nat)
    (envBound : env.QueryCostBoundAt sec oracleBudget)
    (result : Crypto.Infrastructure.Computation.Cost.Costed (Output sec))
    (hresult :
      result ∈
        (M.toProbabilisticOracleMachine.runCostedWithCostedEnv
          sec input env).support) :
    result.cost ≤
      M.runtime sec + certificate.totalQueryBound sec * oracleBudget sec := by
  simp only [ProbabilisticOracleMachine.runCostedWithCostedEnv,
    Crypto.Infrastructure.Computation.Cost.RandCosted.map,
    Crypto.Infrastructure.Computation.Cost.RandCostedT.map] at hresult
  rw [PMF.mem_support_map_iff] at hresult
  rcases hresult with ⟨liftedResult, hliftedResult, hresult⟩
  subst result
  exact
    Crypto.Infrastructure.Computation.Oracle.OracleProgram.runCostedWithCostedEnv_cost_le
      (M.run sec input) sec env (M.runtime sec) (certificate.totalQueryBound sec)
      oracleBudget (M.runtime_sound sec input)
      (certificate.totalQueryBound_sound sec input) envBound liftedResult hliftedResult

/-- The total-query bound also bounds the number of calls to each oracle. -/
theorem runProfiled_queryCount_le_totalQueryBound
    (M : TimedOracleMachine Input Output Spec)
    (certificate : TotalQueryBoundCertificate M)
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
    result.profile.queryCount name ≤ certificate.totalQueryBound sec :=
  le_trans (result.profile.queryCount_le_totalQueries name)
    (M.runProfiled_totalQueries_le certificate sec input env result hresult)

end TimedOracleMachine

namespace PPTOracleMachine

variable
    {Input : Crypto.SecPar → Type uIn} {Output : Crypto.SecPar → Type uOut}
    {Spec :
      (sec : Crypto.SecPar) →
      Input sec →
      Crypto.Infrastructure.Computation.Oracle.OracleSpec.{uOracle, uQuery, uResponse}}

/-- Every per-oracle query count is bounded by the machine's polynomial runtime. -/
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

/--
Every per-oracle query count is bounded by the machine's polynomial total-query
bound.

The inherited `queryBound` may record a tighter bound for a particular oracle.
-/
theorem runProfiled_queryCount_le_totalQueryBound
    (M : PPTOracleMachine Input Output Spec)
    (certificate : PolyTotalQueryBoundCertificate M)
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
    result.profile.queryCount name ≤ certificate.totalQueryBound sec :=
  M.toTimedOracleMachine.runProfiled_queryCount_le_totalQueryBound
    certificate.toTotalQueryBoundCertificate sec input env result hresult name

/-- The composed runtime of a PPT machine and a polynomial-cost oracle is polynomial. -/
theorem composedRuntime_isPoly
    (M : PPTOracleMachine Input Output Spec)
    (certificate : PolyTotalQueryBoundCertificate M)
    (oracleBudget : Crypto.SecPar → Nat)
    (oracleBudget_isPoly : IsPolyBounded oracleBudget) :
    IsPolyBounded
      (fun sec =>
        M.runtime sec + certificate.totalQueryBound sec * oracleBudget sec) :=
  IsPolyBounded.composedOracle
    M.runtime_isPoly certificate.totalQueryBound_isPoly oracleBudget_isPoly

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

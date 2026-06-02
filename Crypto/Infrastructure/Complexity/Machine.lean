import Crypto.Infrastructure.Asymptotic.Bounds
import Crypto.Infrastructure.Computation.Oracle.Interface
import Mathlib.Probability.ProbabilityMassFunction.Monad

namespace Crypto.Infrastructure.Complexity

open Crypto.Infrastructure.Asymptotic

universe uIn uOut uOracle uQuery uResponse uState

/-- A semantic probabilistic machine.

The machine is represented by its input/output behavior at a security parameter,
without exposing a tape-level transition system. -/
structure ProbabilisticMachine (Input : Type uIn) (Output : Type uOut) where
  run : Crypto.SecPar → Input → PMF Output

/-- A semantic probabilistic machine equipped with a uniform running-time bound. -/
structure TimedMachine (Input : Type uIn) (Output : Type uOut)
    extends ProbabilisticMachine Input Output where
  runtime : Crypto.SecPar → Nat

/--
A semantic probabilistic polynomial-time machine.

The `runtime` field records the claimed uniform time bound for this semantic
input/output behavior.  It is not yet tied to a transition-system semantics or
to the costed-computation layer.
-/
structure PPTMachine (Input : Type uIn) (Output : Type uOut)
    extends TimedMachine Input Output where
  runtime_isPoly : IsPolyBounded runtime

/-- A semantic probabilistic machine whose output type may depend on its input. -/
structure ProbabilisticDependentMachine
    (Input : Type uIn) (Output : Input → Type uOut) where
  run : (sec : Crypto.SecPar) → (input : Input) → PMF (Output input)

/-- A dependent-output probabilistic machine equipped with a uniform running-time bound. -/
structure TimedDependentMachine
    (Input : Type uIn) (Output : Input → Type uOut)
    extends ProbabilisticDependentMachine Input Output where
  runtime : Crypto.SecPar → Nat

/--
A semantic dependent-output probabilistic polynomial-time machine.

As with `PPTMachine`, the runtime certificate is a semantic bound attached to
the machine interface rather than a derived bound on an executable trace.
-/
structure PPTDependentMachine
    (Input : Type uIn) (Output : Input → Type uOut)
    extends TimedDependentMachine Input Output where
  runtime_isPoly : IsPolyBounded runtime

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

/-- An oracle machine equipped with uniform runtime and per-oracle query bounds. -/
structure TimedOracleMachine
    (Input : Crypto.SecPar → Type uIn) (Output : Crypto.SecPar → Type uOut)
    (Spec :
      (sec : Crypto.SecPar) →
      Input sec →
      Crypto.Infrastructure.Computation.Oracle.OracleSpec.{uOracle, uQuery, uResponse})
    extends ProbabilisticOracleMachine Input Output Spec where
  runtime : Crypto.SecPar → Nat
  queryBound : (sec : Crypto.SecPar) → (input : Input sec) → (Spec sec input).Name → Nat

/--
A semantic probabilistic polynomial-time oracle machine.

The runtime and query-bound fields are part of the machine interface.  The
oracle program syntax enforces linear state threading during interpretation,
but query bounds are not yet derived from the `run` program.
-/
structure PPTOracleMachine
    (Input : Crypto.SecPar → Type uIn) (Output : Crypto.SecPar → Type uOut)
    (Spec :
      (sec : Crypto.SecPar) →
      Input sec →
      Crypto.Infrastructure.Computation.Oracle.OracleSpec.{uOracle, uQuery, uResponse})
    extends TimedOracleMachine Input Output Spec where
  runtime_isPoly : IsPolyBounded runtime
  queryBound_polyBound : Crypto.SecPar → Nat
  queryBound_polyBound_isPoly : IsPolyBounded queryBound_polyBound
  queryBound_le_polyBound :
    ∀ sec input name, queryBound sec input name ≤ queryBound_polyBound sec

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
  PMF.bind
    (Crypto.Infrastructure.Computation.Oracle.OracleProgram.runWithEnv
      (M.run sec input) sec env) fun output =>
      PMF.pure output.down

end ProbabilisticOracleMachine

/-- A semantic deterministic machine with a uniform running-time bound. -/
structure DeterministicMachine (Input : Type uIn) (Output : Type uOut) where
  run : Crypto.SecPar → Input → Output
  runtime : Crypto.SecPar → Nat

namespace DeterministicMachine

variable {Input : Type uIn} {Output : Type uOut}

/-- View a deterministic machine as a probabilistic machine concentrated on its output. -/
noncomputable def toProbabilisticMachine (M : DeterministicMachine Input Output) :
    ProbabilisticMachine Input Output where
  run sec input := PMF.pure (M.run sec input)

/-- View a deterministic timed machine as a timed probabilistic machine. -/
noncomputable def toTimedMachine (M : DeterministicMachine Input Output) :
    TimedMachine Input Output where
  run sec input := PMF.pure (M.run sec input)
  runtime := M.runtime

/-- Promote a deterministic machine with a polynomial runtime bound to a PPT machine. -/
noncomputable def toPPTMachine (M : DeterministicMachine Input Output)
    (runtime_isPoly : IsPolyBounded M.runtime) : PPTMachine Input Output where
  run sec input := PMF.pure (M.run sec input)
  runtime := M.runtime
  runtime_isPoly := runtime_isPoly

@[simp] theorem toProbabilisticMachine_run (M : DeterministicMachine Input Output)
    (sec : Crypto.SecPar) (input : Input) :
    M.toProbabilisticMachine.run sec input = PMF.pure (M.run sec input) :=
  rfl

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

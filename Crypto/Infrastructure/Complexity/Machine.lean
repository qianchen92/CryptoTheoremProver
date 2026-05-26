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

/-- A probabilistic polynomial-time machine. -/
structure PPTMachine (Input : Type uIn) (Output : Type uOut)
    extends TimedMachine Input Output where
  runtime_isPoly : IsPolyBounded runtime

/-- A probabilistic machine with adaptive access to an oracle environment. -/
structure ProbabilisticOracleMachine
    (Input : Crypto.SecPar → Type uIn) (Output : Crypto.SecPar → Type uOut)
    (Spec :
      (sec : Crypto.SecPar) →
      Input sec →
      Crypto.Infrastructure.Computation.Oracle.OracleSpec.{uOracle, uQuery, uResponse}) where
  run :
    (sec : Crypto.SecPar) →
    (input : Input sec) →
    Crypto.Infrastructure.Computation.Oracle.OracleEnv.{uOracle, uQuery, uResponse, uState}
      (Spec sec input) →
    PMF (Output sec)

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

/-- A probabilistic polynomial-time oracle machine. -/
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

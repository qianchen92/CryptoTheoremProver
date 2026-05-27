import Crypto.Infrastructure.Asymptotic.Bounds
import Crypto.Infrastructure.Complexity.Machine
import Crypto.Infrastructure.GameBased.Advantage
import Mathlib.Probability.ProbabilityMassFunction.Monad

namespace Crypto.Infrastructure.GameBased

universe uChallenge uIn uOracle uQuery uResponse uState

/-- Two boolean games are indistinguishable when their advantage is negligible. -/
def Indistinguishable (G₀ G₁ : Crypto.Infrastructure.Computation.Game Bool) : Prop :=
  Crypto.Infrastructure.Asymptotic.IsNegligible (Advantage G₀ G₁)

namespace Distinguishing

/-- A distinguishing problem is a pair of challenge distributions. -/
structure Problem (Challenge : Type uChallenge) where
  left : Crypto.SecPar → PMF Challenge
  right : Crypto.SecPar → PMF Challenge

/-- Run a boolean machine on samples from a challenge distribution. -/
noncomputable def game
    {Challenge : Type uChallenge}
    (sample : Crypto.SecPar → PMF Challenge)
    (A : Crypto.Infrastructure.Complexity.ProbabilisticMachine Challenge Bool) :
    Crypto.Infrastructure.Computation.Game Bool :=
  fun sec =>
    PMF.bind (sample sec) fun challenge =>
      A.run sec challenge

/-- A distinguishing problem is hard if every PPT machine sees negligible advantage. -/
def Hard {Challenge : Type uChallenge} (P : Problem Challenge) : Prop :=
  ∀ A : Crypto.Infrastructure.Complexity.PPTMachine Challenge Bool,
    Indistinguishable
      (game P.left A.toProbabilisticMachine)
      (game P.right A.toProbabilisticMachine)

end Distinguishing

namespace OracleDistinguishing

/-- An oracle distinguishing problem is a setup distribution and two oracle environments. -/
structure Problem
    (Input : Crypto.SecPar → Type uIn)
    (Spec :
      (sec : Crypto.SecPar) →
      Input sec →
      Crypto.Infrastructure.Computation.Oracle.OracleSpec.{uOracle, uQuery, uResponse}) where
  setup : (sec : Crypto.SecPar) → PMF (Input sec)
  leftEnv :
    (sec : Crypto.SecPar) →
    (input : Input sec) →
    Crypto.Infrastructure.Computation.Oracle.OracleEnv.{uOracle, uQuery, uResponse, uState}
      (Spec sec input)
  rightEnv :
    (sec : Crypto.SecPar) →
    (input : Input sec) →
    Crypto.Infrastructure.Computation.Oracle.OracleEnv.{uOracle, uQuery, uResponse, uState}
      (Spec sec input)

/-- Run an oracle machine against one side of an oracle distinguishing problem. -/
noncomputable def game
    {Input : Crypto.SecPar → Type uIn}
    {Spec :
      (sec : Crypto.SecPar) →
      Input sec →
      Crypto.Infrastructure.Computation.Oracle.OracleSpec.{uOracle, uQuery, uResponse}}
    (P : Problem.{uIn, uOracle, uQuery, uResponse, uState} Input Spec)
    (env :
      (sec : Crypto.SecPar) →
      (input : Input sec) →
      Crypto.Infrastructure.Computation.Oracle.OracleEnv.{uOracle, uQuery, uResponse, uState}
        (Spec sec input))
    (A : Crypto.Infrastructure.Complexity.ProbabilisticOracleMachine
      Input (fun _ => Bool) Spec) :
    Crypto.Infrastructure.Computation.Game Bool :=
  fun sec =>
    PMF.bind (P.setup sec) fun input => do
      let output ← A.run sec input (env sec input)
      return output

/-- The left-side oracle distinguishing game. -/
noncomputable def leftGame
    {Input : Crypto.SecPar → Type uIn}
    {Spec :
      (sec : Crypto.SecPar) →
      Input sec →
      Crypto.Infrastructure.Computation.Oracle.OracleSpec.{uOracle, uQuery, uResponse}}
    (P : Problem.{uIn, uOracle, uQuery, uResponse, uState} Input Spec)
    (A : Crypto.Infrastructure.Complexity.ProbabilisticOracleMachine
      Input (fun _ => Bool) Spec) :
    Crypto.Infrastructure.Computation.Game Bool :=
  game P P.leftEnv A

/-- The right-side oracle distinguishing game. -/
noncomputable def rightGame
    {Input : Crypto.SecPar → Type uIn}
    {Spec :
      (sec : Crypto.SecPar) →
      Input sec →
      Crypto.Infrastructure.Computation.Oracle.OracleSpec.{uOracle, uQuery, uResponse}}
    (P : Problem.{uIn, uOracle, uQuery, uResponse, uState} Input Spec)
    (A : Crypto.Infrastructure.Complexity.ProbabilisticOracleMachine
      Input (fun _ => Bool) Spec) :
    Crypto.Infrastructure.Computation.Game Bool :=
  game P P.rightEnv A

/-- An oracle distinguishing problem is hard if every PPT oracle machine has negligible advantage. -/
def Hard
    {Input : Crypto.SecPar → Type uIn}
    {Spec :
      (sec : Crypto.SecPar) →
      Input sec →
      Crypto.Infrastructure.Computation.Oracle.OracleSpec.{uOracle, uQuery, uResponse}}
    (P : Problem.{uIn, uOracle, uQuery, uResponse, uState} Input Spec) : Prop :=
  ∀ A : Crypto.Infrastructure.Complexity.PPTOracleMachine Input (fun _ => Bool) Spec,
    Indistinguishable
      (leftGame P A.toProbabilisticOracleMachine)
      (rightGame P A.toProbabilisticOracleMachine)

end OracleDistinguishing

end Crypto.Infrastructure.GameBased

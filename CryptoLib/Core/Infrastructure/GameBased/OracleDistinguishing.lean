import CryptoLib.Core.Infrastructure.Complexity.OracleMachine
import CryptoLib.Core.Infrastructure.GameBased.Indistinguishability
import Mathlib.Probability.ProbabilityMassFunction.Monad

namespace CryptoLib.Core.Infrastructure.GameBased.OracleDistinguishing

open CryptoLib.Core.Infrastructure.Computation.Cost
open CryptoLib.Core.Infrastructure.Computation.Oracle

universe uCost uIn uOracle uQuery uResponse uState

variable
    {M : CostModel.{uCost}}
    {Input : CryptoLib.Core.SecPar → Type uIn}
    {Spec :
      (sec : CryptoLib.Core.SecPar) → Input sec →
        OracleSpec.{uOracle, uQuery, uResponse}}

/-- An oracle distinguishing problem is setup plus two semantic environments. -/
structure Problem
    (Input : CryptoLib.Core.SecPar → Type uIn)
    (Spec :
      (sec : CryptoLib.Core.SecPar) → Input sec →
        OracleSpec.{uOracle, uQuery, uResponse}) where
  setup : (sec : CryptoLib.Core.SecPar) → PMF (Input sec)
  leftEnv :
    (sec : CryptoLib.Core.SecPar) → (input : Input sec) →
      OracleEnv.{uOracle, uQuery, uResponse, uState} (Spec sec input)
  rightEnv :
    (sec : CryptoLib.Core.SecPar) → (input : Input sec) →
      OracleEnv.{uOracle, uQuery, uResponse, uState} (Spec sec input)

/-- Run one exact-program adversary against a selected semantic environment. -/
noncomputable def securityGame
    (problem : Problem.{uIn, uOracle, uQuery, uResponse, uState} Input Spec)
    (env :
      (sec : CryptoLib.Core.SecPar) → (input : Input sec) →
        OracleEnv.{uOracle, uQuery, uResponse, uState} (Spec sec input))
    (adversary : CryptoLib.Core.Infrastructure.Complexity.OracleMachine M Input
      (fun _sec _input => Bool) Spec) :
    CryptoLib.Core.Infrastructure.Computation.Game Bool :=
  fun sec =>
    PMF.bind (problem.setup sec) fun input =>
      adversary.runWithEnv sec input (env sec input)

/-- The left-side oracle distinguishing game. -/
noncomputable def leftSecurityGame
    (problem : Problem.{uIn, uOracle, uQuery, uResponse, uState} Input Spec)
    (adversary : CryptoLib.Core.Infrastructure.Complexity.OracleMachine M Input
      (fun _sec _input => Bool) Spec) :
    CryptoLib.Core.Infrastructure.Computation.Game Bool :=
  securityGame problem problem.leftEnv adversary

/-- The right-side oracle distinguishing game. -/
noncomputable def rightSecurityGame
    (problem : Problem.{uIn, uOracle, uQuery, uResponse, uState} Input Spec)
    (adversary : CryptoLib.Core.Infrastructure.Complexity.OracleMachine M Input
      (fun _sec _input => Bool) Spec) :
    CryptoLib.Core.Infrastructure.Computation.Game Bool :=
  securityGame problem problem.rightEnv adversary

/--
Hardness is quantified over all polynomially annotated, operationally admitted
oracle machines for an explicit exact cost model and natural-number observation.
-/
def Hard
    (adversaryModel : CostModel.{uCost})
    (measure : NatMeasure adversaryModel)
    {Input : CryptoLib.Core.SecPar → Type uIn}
    {Spec :
      (sec : CryptoLib.Core.SecPar) → Input sec →
        OracleSpec.{uOracle, uQuery, uResponse}}
    (problem : Problem.{uIn, uOracle, uQuery, uResponse, uState} Input Spec) :
    Prop :=
  ∀ adversary : CryptoLib.Core.Infrastructure.Complexity.PPTOracleMachine
      adversaryModel measure Input (fun _sec _input => Bool) Spec,
    CryptoLib.Core.Infrastructure.GameBased.Indistinguishable
      (leftSecurityGame problem adversary.toOracleMachine)
      (rightSecurityGame problem adversary.toOracleMachine)

end CryptoLib.Core.Infrastructure.GameBased.OracleDistinguishing

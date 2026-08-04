import Crypto.Infrastructure.Complexity.OracleMachine
import Crypto.Infrastructure.GameBased.Indistinguishability
import Mathlib.Probability.ProbabilityMassFunction.Monad

namespace Crypto.Infrastructure.GameBased.OracleDistinguishing

open Crypto.Infrastructure.Computation.Cost
open Crypto.Infrastructure.Computation.Oracle

universe uCost uIn uOracle uQuery uResponse uState

/-- An oracle distinguishing problem is setup plus two semantic environments. -/
structure Problem
    (Input : Crypto.SecPar → Type uIn)
    (Spec :
      (sec : Crypto.SecPar) → Input sec →
        OracleSpec.{uOracle, uQuery, uResponse}) where
  setup : (sec : Crypto.SecPar) → PMF (Input sec)
  leftEnv :
    (sec : Crypto.SecPar) → (input : Input sec) →
      OracleEnv.{uOracle, uQuery, uResponse, uState} (Spec sec input)
  rightEnv :
    (sec : Crypto.SecPar) → (input : Input sec) →
      OracleEnv.{uOracle, uQuery, uResponse, uState} (Spec sec input)

/-- Run one exact-program adversary against a selected semantic environment. -/
noncomputable def securityGame
    {M : CostModel.{uCost}}
    {Input : Crypto.SecPar → Type uIn}
    {Spec :
      (sec : Crypto.SecPar) → Input sec →
        OracleSpec.{uOracle, uQuery, uResponse}}
    (problem : Problem.{uIn, uOracle, uQuery, uResponse, uState} Input Spec)
    (env :
      (sec : Crypto.SecPar) → (input : Input sec) →
        OracleEnv.{uOracle, uQuery, uResponse, uState} (Spec sec input))
    (adversary : Crypto.Infrastructure.Complexity.OracleMachine M Input
      (fun _sec _input => Bool) Spec) :
    Crypto.Infrastructure.Computation.Game Bool :=
  fun sec =>
    PMF.bind (problem.setup sec) fun input =>
      adversary.runWithEnv sec input (env sec input)

/-- The left-side oracle distinguishing game. -/
noncomputable def leftSecurityGame
    {M : CostModel.{uCost}}
    {Input : Crypto.SecPar → Type uIn}
    {Spec :
      (sec : Crypto.SecPar) → Input sec →
        OracleSpec.{uOracle, uQuery, uResponse}}
    (problem : Problem.{uIn, uOracle, uQuery, uResponse, uState} Input Spec)
    (adversary : Crypto.Infrastructure.Complexity.OracleMachine M Input
      (fun _sec _input => Bool) Spec) :
    Crypto.Infrastructure.Computation.Game Bool :=
  securityGame problem problem.leftEnv adversary

/-- The right-side oracle distinguishing game. -/
noncomputable def rightSecurityGame
    {M : CostModel.{uCost}}
    {Input : Crypto.SecPar → Type uIn}
    {Spec :
      (sec : Crypto.SecPar) → Input sec →
        OracleSpec.{uOracle, uQuery, uResponse}}
    (problem : Problem.{uIn, uOracle, uQuery, uResponse, uState} Input Spec)
    (adversary : Crypto.Infrastructure.Complexity.OracleMachine M Input
      (fun _sec _input => Bool) Spec) :
    Crypto.Infrastructure.Computation.Game Bool :=
  securityGame problem problem.rightEnv adversary

/--
Hardness is quantified over all polynomially annotated, operationally admitted
oracle machines for an explicit exact cost model and natural-number observation.
-/
def Hard
    (adversaryModel : CostModel.{uCost})
    (measure : NatMeasure adversaryModel)
    {Input : Crypto.SecPar → Type uIn}
    {Spec :
      (sec : Crypto.SecPar) → Input sec →
        OracleSpec.{uOracle, uQuery, uResponse}}
    (problem : Problem.{uIn, uOracle, uQuery, uResponse, uState} Input Spec) :
    Prop :=
  ∀ adversary : Crypto.Infrastructure.Complexity.PPTOracleMachine
      adversaryModel measure Input (fun _sec _input => Bool) Spec,
    Crypto.Infrastructure.GameBased.Indistinguishable
      (leftSecurityGame problem adversary.toOracleMachine)
      (rightSecurityGame problem adversary.toOracleMachine)

end Crypto.Infrastructure.GameBased.OracleDistinguishing

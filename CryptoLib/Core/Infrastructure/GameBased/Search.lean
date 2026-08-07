import CryptoLib.Core.Infrastructure.Complexity.Machine
import CryptoLib.Core.Infrastructure.GameBased.Advantage
import Mathlib.Probability.ProbabilityMassFunction.Monad

namespace CryptoLib.Core.Infrastructure.GameBased

open CryptoLib.Core.Infrastructure.Computation.Cost

universe uCost uInstance uWitness

namespace Search

variable
    {M : CostModel.{uCost}}
    {Instance : Type uInstance}

/-- A search problem consists of an instance generator and a valid-witness relation. -/
structure Problem (Instance : Type uInstance) where
  Witness : Instance → Type uWitness
  sample : CryptoLib.Core.SecPar → PMF Instance
  relation : (input : Instance) → Witness input → Prop
  decidableRelation : (input : Instance) → (witness : Witness input) →
    Decidable (relation input witness)

/--
The canonical search game samples an instance and accepts exactly when the
machine returns a valid dependent witness.
-/
noncomputable def securityGame
    (problem : Problem.{uInstance, uWitness} Instance)
    (adversary : CryptoLib.Core.Infrastructure.Complexity.ProbabilisticMachine M
      (fun _sec => Instance)
      (fun _sec input => problem.Witness input)) :
    CryptoLib.Core.Infrastructure.Computation.Game Bool :=
  fun sec =>
    PMF.bind (problem.sample sec) fun input =>
      PMF.bind (adversary.runDist sec input) fun output =>
        letI := problem.decidableRelation input output
        PMF.pure (decide (problem.relation input output))

/-- Success probability of a machine in a search security game. -/
noncomputable def SuccessProbability
    (problem : Problem.{uInstance, uWitness} Instance)
    (adversary : CryptoLib.Core.Infrastructure.Complexity.ProbabilisticMachine M
      (fun _sec => Instance)
      (fun _sec input => problem.Witness input)) :
    CryptoLib.Core.SecPar → Real :=
  CryptoLib.Core.Infrastructure.GameBased.AcceptProb (securityGame problem adversary)

/--
A search problem is hard relative to an explicit cost model and observation if
every polynomially annotated and operationally admitted machine succeeds with
negligible probability.
-/
def Hard
    (adversaryModel : CostModel.{uCost})
    (measure : NatMeasure adversaryModel)
    {Instance : Type uInstance}
    (problem : Problem.{uInstance, uWitness} Instance) : Prop :=
  ∀ adversary : CryptoLib.Core.Infrastructure.Complexity.PPTMachine
      adversaryModel measure
      (fun _sec => Instance)
      (fun _sec input => problem.Witness input),
    CryptoLib.Core.Infrastructure.Asymptotic.IsNegligible
      (SuccessProbability problem adversary.toProbabilisticMachine)

end Search

end CryptoLib.Core.Infrastructure.GameBased

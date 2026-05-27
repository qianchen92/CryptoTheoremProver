import Crypto.Infrastructure.Asymptotic.Bounds
import Crypto.Infrastructure.Complexity.Machine
import Crypto.Infrastructure.GameBased.Advantage
import Mathlib.Probability.ProbabilityMassFunction.Monad

namespace Crypto.Infrastructure.GameBased

universe uInstance uWitness

namespace Search

/-- A search problem consists of an instance generator and a valid-witness relation. -/
structure Problem (Instance : Type uInstance) where
  Witness : Instance → Type uWitness
  sample : Crypto.SecPar → PMF Instance
  relation : (input : Instance) → Witness input → Prop
  decidableRelation : (input : Instance) → (witness : Witness input) →
    Decidable (relation input witness)

/-- The canonical search security game: sample an instance and accept iff the machine returns a witness. -/
noncomputable def securityGame
    {Instance : Type uInstance}
    (P : Problem.{uInstance, uWitness} Instance)
    (A : Crypto.Infrastructure.Complexity.ProbabilisticDependentMachine Instance P.Witness) :
    Crypto.Infrastructure.Computation.Game Bool :=
  fun sec =>
    PMF.bind (P.sample sec) fun input =>
      PMF.bind (A.run sec input) fun output =>
        letI := P.decidableRelation input output
        PMF.pure (decide (P.relation input output))

/-- Success probability of a machine in a search security game. -/
noncomputable def SuccessProbability
    {Instance : Type uInstance}
    (P : Problem.{uInstance, uWitness} Instance)
    (A : Crypto.Infrastructure.Complexity.ProbabilisticDependentMachine Instance P.Witness) :
    Crypto.SecPar → Real :=
  Crypto.Infrastructure.GameBased.AcceptProb (securityGame P A)

/-- A search problem is hard if every PPT machine succeeds with negligible probability. -/
def Hard
    {Instance : Type uInstance}
    (P : Problem.{uInstance, uWitness} Instance) : Prop :=
  ∀ A : Crypto.Infrastructure.Complexity.PPTDependentMachine Instance P.Witness,
    Crypto.Infrastructure.Asymptotic.IsNegligible
      (SuccessProbability P A.toProbabilisticDependentMachine)

end Search

end Crypto.Infrastructure.GameBased

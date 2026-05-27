import Crypto.Infrastructure.Asymptotic.Bounds
import Crypto.Infrastructure.Complexity.Machine
import Crypto.Infrastructure.GameBased.Advantage
import Mathlib.Probability.ProbabilityMassFunction.Monad

namespace Crypto.Infrastructure.GameBased

universe uInstance uWitness

namespace Search

/-- A search problem consists of an instance generator and a valid-witness relation. -/
structure Problem (Instance : Type uInstance) (Witness : Type uWitness) where
  sample : Crypto.SecPar → PMF Instance
  relation : Instance → Witness → Prop
  decidableRelation : DecidableRel relation

attribute [instance] Problem.decidableRelation

/-- The canonical search game: sample an instance and accept iff the machine returns a witness. -/
noncomputable def game
    {Instance : Type uInstance} {Witness : Type uWitness}
    (P : Problem Instance Witness)
    (A : Crypto.Infrastructure.Complexity.ProbabilisticMachine Instance Witness) :
    Crypto.Infrastructure.Computation.Game Bool :=
  fun sec =>
    PMF.bind (P.sample sec) fun input =>
      PMF.bind (A.run sec input) fun output =>
        letI := P.decidableRelation
        PMF.pure (decide (P.relation input output))

/-- Success probability of a machine in a search game. -/
noncomputable def SuccessProbability
    {Instance : Type uInstance} {Witness : Type uWitness}
    (P : Problem Instance Witness)
    (A : Crypto.Infrastructure.Complexity.ProbabilisticMachine Instance Witness) :
    Crypto.SecPar → Real :=
  Crypto.Infrastructure.GameBased.AcceptProb (game P A)

/-- A search problem is hard if every PPT machine succeeds with negligible probability. -/
def Hard
    {Instance : Type uInstance} {Witness : Type uWitness}
    (P : Problem Instance Witness) : Prop :=
  ∀ A : Crypto.Infrastructure.Complexity.PPTMachine Instance Witness,
    Crypto.Infrastructure.Asymptotic.IsNegligible
      (SuccessProbability P A.toProbabilisticMachine)

end Search

end Crypto.Infrastructure.GameBased

import Crypto.Foundation.SecurityParameter
import Mathlib.Probability.ProbabilityMassFunction.Basic
import Mathlib.Probability.ProbabilityMassFunction.Constructions

namespace Crypto.Core

universe uOutcome uMapped

/-- A security experiment indexed by the security parameter. -/
abbrev Game (Outcome : Type uOutcome) :=
  Crypto.SecPar → PMF Outcome

namespace Game

/-- Boolean games are the standard shape of accept/reject security experiments. -/
abbrev BoolGame :=
  Game Bool

/-- Map the outcome of a game. -/
noncomputable def map {Outcome : Type uOutcome} {Mapped : Type uMapped}
    (f : Outcome → Mapped) (G : Game Outcome) : Game Mapped :=
  fun sec => PMF.map f (G sec)

end Game

end Crypto.Core

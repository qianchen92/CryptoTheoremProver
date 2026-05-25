import Crypto.Core.Cost.Costed
import Mathlib.Probability.ProbabilityMassFunction.Basic
import Mathlib.Probability.ProbabilityMassFunction.Constructions
import Mathlib.Probability.ProbabilityMassFunction.Monad

namespace Crypto.Core.Cost

universe uValue

/-- A randomized computation whose paths carry accumulated costs. -/
abbrev RandCosted (α : Type uValue) := PMF (Costed α)

namespace RandCosted

/-- Lift a distribution over values to a zero-cost distribution over costed values. -/
noncomputable def sample {α : Type uValue} (dist : PMF α) : RandCosted α :=
  PMF.map Costed.ofValue dist

/-- Forget costs from a randomized costed computation. -/
noncomputable def valueDist {α : Type uValue} (dist : RandCosted α) : PMF α :=
  PMF.map Costed.val dist

/-- Keep only costs from a randomized costed computation. -/
noncomputable def costDist {α : Type uValue} (dist : RandCosted α) : PMF Cost :=
  PMF.map Costed.cost dist

end RandCosted

end Crypto.Core.Cost

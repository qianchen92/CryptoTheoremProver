import Crypto.Infrastructure.Computation.Game
import Mathlib.Data.Real.Basic

namespace Crypto.Infrastructure.GameBased

/-- Acceptance probability of a boolean game. -/
noncomputable def AcceptProb
    (G : Crypto.Infrastructure.Computation.Game Bool) (sec : Crypto.SecPar) : Real :=
  (G sec true).toReal

/-- Absolute difference between two boolean games' acceptance probabilities. -/
noncomputable def Advantage
    (G₀ G₁ : Crypto.Infrastructure.Computation.Game Bool) (sec : Crypto.SecPar) : Real :=
  |AcceptProb G₀ sec - AcceptProb G₁ sec|

namespace Advantage

variable {G₀ G₁ G₂ : Crypto.Infrastructure.Computation.Game Bool}

/-- Distinguishing advantage is nonnegative. -/
theorem nonneg (sec : Crypto.SecPar) :
    0 ≤ Advantage G₀ G₁ sec :=
  abs_nonneg _

/-- A game has zero distinguishing advantage from itself. -/
@[simp] theorem self (G : Crypto.Infrastructure.Computation.Game Bool) :
    Advantage G G = fun _ => 0 := by
  funext sec
  simp [Advantage]

/-- Distinguishing advantage is symmetric. -/
theorem symm :
    Advantage G₀ G₁ = Advantage G₁ G₀ := by
  funext sec
  exact abs_sub_comm _ _

/-- Distinguishing advantage satisfies the pointwise triangle inequality. -/
theorem triangle (sec : Crypto.SecPar) :
    Advantage G₀ G₂ sec ≤ Advantage G₀ G₁ sec + Advantage G₁ G₂ sec := by
  exact abs_sub_le _ _ _

end Advantage

end Crypto.Infrastructure.GameBased

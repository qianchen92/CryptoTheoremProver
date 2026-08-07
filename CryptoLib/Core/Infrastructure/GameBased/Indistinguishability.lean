import CryptoLib.Core.Infrastructure.Asymptotic.Bounds
import CryptoLib.Core.Infrastructure.GameBased.Advantage

namespace CryptoLib.Core.Infrastructure.GameBased

/-- Two boolean games are indistinguishable when their advantage is negligible. -/
def Indistinguishable
    (left right : CryptoLib.Core.Infrastructure.Computation.Game Bool) : Prop :=
  CryptoLib.Core.Infrastructure.Asymptotic.IsNegligible (Advantage left right)

namespace Indistinguishable

variable {left middle right : CryptoLib.Core.Infrastructure.Computation.Game Bool}

/-- Equality of games implies indistinguishability. -/
theorem of_eq (h : left = right) : Indistinguishable left right := by
  subst right
  unfold Indistinguishable
  rw [Advantage.self]
  exact CryptoLib.Core.Infrastructure.Asymptotic.isNegligible_zero

/-- Indistinguishability is reflexive. -/
theorem refl (game : CryptoLib.Core.Infrastructure.Computation.Game Bool) :
    Indistinguishable game game :=
  of_eq rfl

/-- Indistinguishability is symmetric. -/
theorem symm (h : Indistinguishable left right) :
    Indistinguishable right left := by
  unfold Indistinguishable at h ⊢
  rw [Advantage.symm]
  exact h

/-- Indistinguishability is transitive through the advantage triangle inequality. -/
theorem trans
    (hleft : Indistinguishable left middle)
    (hright : Indistinguishable middle right) :
    Indistinguishable left right := by
  unfold Indistinguishable at hleft hright ⊢
  apply CryptoLib.Core.Infrastructure.Asymptotic.IsNegligible.mono (hleft.add hright)
  intro sec
  rw [abs_of_nonneg (Advantage.nonneg sec)]
  rw [abs_of_nonneg
    (add_nonneg (Advantage.nonneg sec) (Advantage.nonneg sec))]
  exact Advantage.triangle sec

end Indistinguishable

end CryptoLib.Core.Infrastructure.GameBased

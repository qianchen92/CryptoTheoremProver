import Mathlib.Data.ENNReal.Basic
import Mathlib.Probability.ProbabilityMassFunction.Constructions

namespace Crypto.Infrastructure.Computation.Distribution

universe uValue

/-- The uniform probability mass function over a finite nonempty type. -/
noncomputable def uniformPMF (α : Type uValue) [Fintype α] [Nonempty α] : PMF α :=
  PMF.ofFintype (fun _ : α => ((Fintype.card α : ENNReal)⁻¹)) (by
    rw [Finset.sum_const]
    simp only [nsmul_eq_mul]
    exact ENNReal.mul_inv_cancel
      (by exact_mod_cast (ne_of_gt (Fintype.card_pos : 0 < Fintype.card α)))
      (ENNReal.natCast_ne_top _))

end Crypto.Infrastructure.Computation.Distribution

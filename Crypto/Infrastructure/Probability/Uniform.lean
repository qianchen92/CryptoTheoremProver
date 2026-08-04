import Mathlib.Data.ENNReal.Basic
import Mathlib.Probability.ProbabilityMassFunction.Constructions

namespace Crypto.Infrastructure.Probability

universe uValue

/-- The uniform probability mass function over a finite nonempty type. -/
noncomputable def uniformPMF
    (Value : Type uValue) [Fintype Value] [Nonempty Value] : PMF Value :=
  PMF.ofFintype
    (fun _value : Value => ((Fintype.card Value : ENNReal)⁻¹))
    (by
      rw [Finset.sum_const]
      simp only [nsmul_eq_mul]
      exact ENNReal.mul_inv_cancel
        (by
          exact_mod_cast
            (ne_of_gt (Fintype.card_pos : 0 < Fintype.card Value)))
        (ENNReal.natCast_ne_top _))

end Crypto.Infrastructure.Probability

import Mathlib.Data.ENNReal.Basic
import Mathlib.Probability.ProbabilityMassFunction.Constructions
import Mathlib.Probability.ProbabilityMassFunction.Monad

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

/-- Left translation preserves the uniform distribution on a finite group. -/
theorem map_add_left_uniformPMF
    (Value : Type uValue) [AddGroup Value] [Fintype Value] [Nonempty Value]
    (message : Value) :
    PMF.map (fun mask => message + mask) (uniformPMF Value) =
      uniformPMF Value := by
  classical
  ext output
  rw [← PMF.bind_pure_comp]
  have hcard :
      (Finset.univ.filter
        (fun mask : Value => message + mask = output)).card = 1 := by
    rw [Finset.card_eq_one]
    refine ⟨-message + output, ?_⟩
    ext mask
    simp [eq_comm, eq_neg_add_iff_add_eq]
  have hcard' :
      (Finset.univ.filter
        (fun mask : Value => output = message + mask)).card = 1 := by
    simpa [eq_comm] using hcard
  calc
    (PMF.bind (uniformPMF Value)
        (PMF.pure ∘ fun mask => message + mask)) output =
        ∑ mask : Value,
          if output = message + mask then
            ((Fintype.card Value : ENNReal)⁻¹) else 0 := by
      simp [uniformPMF, PMF.bind_apply, Function.comp_apply]
    _ = ((Fintype.card Value : ENNReal)⁻¹) := by
      rw [← Finset.sum_filter]
      simp [Finset.sum_const, nsmul_eq_mul, hcard']
    _ = uniformPMF Value output := by
      simp [uniformPMF]

end Crypto.Infrastructure.Probability

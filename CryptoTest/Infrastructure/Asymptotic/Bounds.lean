import Crypto.Infrastructure.Asymptotic.Basic
import Mathlib.Tactic

namespace CryptoTest.Infrastructure.Asymptotic.Bounds

open Crypto.Infrastructure.Asymptotic

/-- Taking absolute values prevents a negative constant from becoming negligible. -/
theorem negativeOne_not_negligible :
    ¬ IsNegligible (fun _sec : Crypto.SecPar => (-1 : Real)) := by
  intro negligible
  obtain ⟨threshold, bound⟩ := negligible 1 (by omega)
  let sec : Crypto.SecPar := max threshold 1
  have threshold_le : threshold ≤ sec := Nat.le_max_left _ _
  have one_le : 1 ≤ sec := Nat.le_max_right _ _
  have claimed := bound sec threshold_le
  have one_le_real : (1 : Real) ≤ sec := by
    exact_mod_cast one_le
  have reciprocal_le_one : (1 : Real) / sec ≤ 1 := by
    exact (div_le_one (by positivity : (0 : Real) < sec)).2 one_le_real
  norm_num at claimed
  have inverse_le_one : (sec : Real)⁻¹ ≤ 1 := by
    simpa only [one_div] using reciprocal_le_one
  exact (not_lt_of_ge inverse_le_one) claimed

end CryptoTest.Infrastructure.Asymptotic.Bounds

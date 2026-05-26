import Crypto.Infrastructure.Asymptotic.SecurityParameter
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Data.Real.Basic

namespace Crypto.Infrastructure.Asymptotic

/-- A natural-valued function bounded by a polynomial in the security parameter. -/
def IsPolyBounded (f : Crypto.SecPar → Nat) : Prop :=
  ∃ p : Polynomial Nat, ∀ n : Crypto.SecPar, f n ≤ p.eval n

/-- A real-valued function negligible in the security parameter. -/
def IsNegligible (f : Crypto.SecPar → Real) : Prop :=
  ∀ c : Nat, c > 0 → ∃ N : Crypto.SecPar, ∀ n ≥ N, f n < (1 : Real) / (n ^ c : Real)

/-- The zero function is negligible. -/
theorem isNegligible_zero : IsNegligible (fun _ : Crypto.SecPar => (0 : Real)) := by
  intro c _hc
  refine ⟨1, ?_⟩
  intro n hn
  have hnposNat : 0 < n := lt_of_lt_of_le Nat.zero_lt_one hn
  have hnpos : (0 : Real) < (n : Real) := by exact_mod_cast hnposNat
  have hpowpos : (0 : Real) < (n ^ c : Real) := pow_pos hnpos c
  exact one_div_pos.mpr hpowpos

end Crypto.Infrastructure.Asymptotic

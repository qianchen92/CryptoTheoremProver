import Crypto.Foundation.SecurityParameter
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Data.Real.Basic

namespace Crypto.Complexity

/-- A natural-valued function bounded by a polynomial in the security parameter. -/
def IsPolyBounded (f : Crypto.SecPar → Nat) : Prop :=
  ∃ p : Polynomial Nat, ∀ n : Crypto.SecPar, f n ≤ p.eval n

/-- A real-valued function negligible in the security parameter. -/
def IsNegligible (f : Crypto.SecPar → Real) : Prop :=
  ∀ c : Nat, c > 0 → ∃ N : Crypto.SecPar, ∀ n ≥ N, f n < (1 : Real) / (n ^ c : Real)

end Crypto.Complexity

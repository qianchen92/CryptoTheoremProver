import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Data.Real.Basic

namespace Crypto.SecModel

abbrev SecPar := Nat

def IsPolyBounded (f : SecPar → Nat) : Prop :=
  ∃ p : Polynomial Nat, ∀ n : SecPar, f n ≤ p.eval n

def IsNegligible (f : SecPar → Real) : Prop :=
  ∀ c : Nat, c > 0 → ∃ N : SecPar, ∀ n ≥ N, f n < (1 : Real) / (n ^ c : Real)

end Crypto.SecModel

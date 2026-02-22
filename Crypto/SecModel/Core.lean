import Mathlib.Algebra.Polynomial.Eval.Defs

namespace Crypto.SecModel

abbrev SecPar := Nat

def IsPolyBounded (f : SecPar → Nat) : Prop :=
  ∃ p : Polynomial Nat, ∀ n : SecPar, f n ≤ p.eval n

end Crypto.SecModel

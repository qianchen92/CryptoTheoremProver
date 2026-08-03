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

namespace IsPolyBounded

/-- The zero cost function is polynomially bounded. -/
theorem zero : IsPolyBounded (fun _ : Crypto.SecPar => 0) := by
  refine ⟨0, ?_⟩
  intro n
  simp

/-- Every constant natural-valued function is polynomially bounded. -/
theorem const (constant : Nat) :
    IsPolyBounded (fun _ : Crypto.SecPar => constant) := by
  refine ⟨Polynomial.C constant, ?_⟩
  intro n
  simp

/-- A pointwise smaller function inherits a polynomial bound. -/
theorem mono
    {f g : Crypto.SecPar → Nat}
    (hg : IsPolyBounded g)
    (hfg : ∀ n, f n ≤ g n) :
    IsPolyBounded f := by
  rcases hg with ⟨polynomial, hpolynomial⟩
  exact ⟨polynomial, fun n => (hfg n).trans (hpolynomial n)⟩

/-- Pointwise sums of polynomially bounded cost functions remain polynomially bounded. -/
theorem add
    {f g : Crypto.SecPar → Nat}
    (hf : IsPolyBounded f) (hg : IsPolyBounded g) :
    IsPolyBounded (fun n => f n + g n) := by
  rcases hf with ⟨leftPolynomial, hleft⟩
  rcases hg with ⟨rightPolynomial, hright⟩
  refine ⟨leftPolynomial + rightPolynomial, ?_⟩
  intro n
  simpa using Nat.add_le_add (hleft n) (hright n)

/-- Pointwise products of polynomially bounded cost functions remain polynomially bounded. -/
theorem mul
    {f g : Crypto.SecPar → Nat}
    (hf : IsPolyBounded f) (hg : IsPolyBounded g) :
    IsPolyBounded (fun n => f n * g n) := by
  rcases hf with ⟨leftPolynomial, hleft⟩
  rcases hg with ⟨rightPolynomial, hright⟩
  refine ⟨leftPolynomial * rightPolynomial, ?_⟩
  intro n
  simpa using Nat.mul_le_mul (hleft n) (hright n)

/-- Pointwise maxima of polynomially bounded cost functions remain polynomially bounded. -/
theorem max
    {f g : Crypto.SecPar → Nat}
    (hf : IsPolyBounded f) (hg : IsPolyBounded g) :
    IsPolyBounded (fun n => max (f n) (g n)) := by
  apply mono (add hf hg)
  intro n
  exact max_le (Nat.le_add_right _ _) (Nat.le_add_left _ _)

/--
The standard cost of running a machine with an implemented oracle is
polynomial: local machine work plus one oracle budget for each possible query.
The total-query budget is independent of the local-work budget.
-/
theorem composedOracle
    {machineBudget totalQueryBudget oracleBudget : Crypto.SecPar → Nat}
    (hmachine : IsPolyBounded machineBudget)
    (hqueries : IsPolyBounded totalQueryBudget)
    (horacle : IsPolyBounded oracleBudget) :
    IsPolyBounded
      (fun n => machineBudget n + totalQueryBudget n * oracleBudget n) :=
  add hmachine (mul hqueries horacle)

end IsPolyBounded

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

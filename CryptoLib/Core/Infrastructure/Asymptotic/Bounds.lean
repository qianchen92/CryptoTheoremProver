import CryptoLib.Core.Infrastructure.SecurityParameter
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Data.Real.Basic

namespace CryptoLib.Core.Infrastructure.Asymptotic

/-- A natural-valued function bounded by a polynomial in the security parameter. -/
def IsPolyBounded (f : CryptoLib.Core.SecPar → Nat) : Prop :=
  ∃ p : Polynomial Nat, ∀ n : CryptoLib.Core.SecPar, f n ≤ p.eval n

/-- A real-valued function negligible in the security parameter. -/
def IsNegligible (f : CryptoLib.Core.SecPar → Real) : Prop :=
  ∀ c : Nat, c > 0 →
    ∃ N : CryptoLib.Core.SecPar, ∀ n ≥ N, |f n| < (1 : Real) / (n ^ c : Real)

namespace IsPolyBounded

variable {f g : CryptoLib.Core.SecPar → Nat}

/-- The zero cost function is polynomially bounded. -/
theorem zero : IsPolyBounded (fun _ : CryptoLib.Core.SecPar => 0) := by
  refine ⟨0, ?_⟩
  intro n
  simp

/-- Every constant natural-valued function is polynomially bounded. -/
theorem const (constant : Nat) :
    IsPolyBounded (fun _ : CryptoLib.Core.SecPar => constant) := by
  refine ⟨Polynomial.C constant, ?_⟩
  intro n
  simp

/-- A pointwise smaller function inherits a polynomial bound. -/
theorem mono
    (hg : IsPolyBounded g)
    (hfg : ∀ n, f n ≤ g n) :
    IsPolyBounded f := by
  rcases hg with ⟨polynomial, hpolynomial⟩
  exact ⟨polynomial, fun n => (hfg n).trans (hpolynomial n)⟩

/-- Pointwise sums of polynomially bounded cost functions remain polynomially bounded. -/
theorem add
    (hf : IsPolyBounded f) (hg : IsPolyBounded g) :
    IsPolyBounded (fun n => f n + g n) := by
  rcases hf with ⟨leftPolynomial, hleft⟩
  rcases hg with ⟨rightPolynomial, hright⟩
  refine ⟨leftPolynomial + rightPolynomial, ?_⟩
  intro n
  simpa using Nat.add_le_add (hleft n) (hright n)

/-- Pointwise products of polynomially bounded cost functions remain polynomially bounded. -/
theorem mul
    (hf : IsPolyBounded f) (hg : IsPolyBounded g) :
    IsPolyBounded (fun n => f n * g n) := by
  rcases hf with ⟨leftPolynomial, hleft⟩
  rcases hg with ⟨rightPolynomial, hright⟩
  refine ⟨leftPolynomial * rightPolynomial, ?_⟩
  intro n
  simpa using Nat.mul_le_mul (hleft n) (hright n)

/-- Pointwise maxima of polynomially bounded cost functions remain polynomially bounded. -/
theorem max
    (hf : IsPolyBounded f) (hg : IsPolyBounded g) :
    IsPolyBounded (fun n => max (f n) (g n)) := by
  apply mono (add hf hg)
  intro n
  exact max_le (Nat.le_add_right _ _) (Nat.le_add_left _ _)

end IsPolyBounded

/-- The zero function is negligible. -/
theorem isNegligible_zero : IsNegligible (fun _ : CryptoLib.Core.SecPar => (0 : Real)) := by
  intro c _hc
  refine ⟨1, ?_⟩
  intro n hn
  have hnposNat : 0 < n := lt_of_lt_of_le Nat.zero_lt_one hn
  have hnpos : (0 : Real) < (n : Real) := by exact_mod_cast hnposNat
  have hpowpos : (0 : Real) < (n ^ c : Real) := pow_pos hnpos c
  simpa using one_div_pos.mpr hpowpos

namespace IsNegligible

variable {f g : CryptoLib.Core.SecPar → Real}

/-- A pointwise smaller absolute value inherits negligibility. -/
theorem mono
    (hg : IsNegligible g)
    (hfg : ∀ n, |f n| ≤ |g n|) :
    IsNegligible f := by
  intro c hc
  obtain ⟨threshold, hthreshold⟩ := hg c hc
  refine ⟨threshold, ?_⟩
  intro n hn
  exact (hfg n).trans_lt (hthreshold n hn)

/-- Pointwise sums of negligible real-valued functions remain negligible. -/
theorem add
    (hf : IsNegligible f) (hg : IsNegligible g) :
    IsNegligible (fun n => f n + g n) := by
  intro c hc
  obtain ⟨leftThreshold, hleft⟩ := hf (c + 1) (Nat.zero_lt_succ c)
  obtain ⟨rightThreshold, hright⟩ := hg (c + 1) (Nat.zero_lt_succ c)
  refine ⟨max 2 (max leftThreshold rightThreshold), ?_⟩
  intro n hn
  have hnTwo : 2 ≤ n := (le_max_left 2 _).trans hn
  have hnLeft : leftThreshold ≤ n :=
    (le_max_of_le_right (le_max_left leftThreshold rightThreshold)).trans hn
  have hnRight : rightThreshold ≤ n :=
    (le_max_of_le_right (le_max_right leftThreshold rightThreshold)).trans hn
  have hnPosNat : 0 < n := Nat.zero_lt_two.trans_le hnTwo
  have hnPos : (0 : Real) < n := by exact_mod_cast hnPosNat
  have hnTwoReal : (2 : Real) ≤ n := by exact_mod_cast hnTwo
  have hpowPos : (0 : Real) < (n : Real) ^ c := pow_pos hnPos c
  have hsuccPowPos : (0 : Real) < (n : Real) ^ (c + 1) := pow_pos hnPos (c + 1)
  calc
    |f n + g n| ≤ |f n| + |g n| := abs_add_le _ _
    _ < (1 : Real) / (n : Real) ^ (c + 1) +
        (1 : Real) / (n : Real) ^ (c + 1) :=
      add_lt_add (hleft n hnLeft) (hright n hnRight)
    _ = (2 : Real) / (n : Real) ^ (c + 1) := by ring
    _ ≤ (1 : Real) / (n : Real) ^ c := by
      apply (div_le_div_iff₀ hsuccPowPos hpowPos).2
      rw [pow_succ]
      simpa [mul_comm] using
        mul_le_mul_of_nonneg_left hnTwoReal hpowPos.le

/-- A finite pointwise sum of negligible functions is negligible. -/
theorem finset_sum
    {Index : Type} (indices : Finset Index)
    (functions : Index → CryptoLib.Core.SecPar → Real)
    (hfunctions : ∀ index ∈ indices, IsNegligible (functions index)) :
    IsNegligible (fun n => ∑ index ∈ indices, functions index n) := by
  classical
  induction indices using Finset.induction_on with
  | empty =>
      simpa using isNegligible_zero
  | @insert index indices hnotMem ih =>
      have hindex : IsNegligible (functions index) :=
        hfunctions index (Finset.mem_insert_self index indices)
      have hindices :
          IsNegligible (fun n => ∑ remaining ∈ indices, functions remaining n) :=
        ih (fun remaining hremaining =>
          hfunctions remaining (Finset.mem_insert_of_mem hremaining))
      simpa [Finset.sum_insert hnotMem] using hindex.add hindices

end IsNegligible

end CryptoLib.Core.Infrastructure.Asymptotic

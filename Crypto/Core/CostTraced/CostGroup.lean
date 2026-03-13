import Mathlib.Probability.ProbabilityMassFunction.Basic
import Mathlib.Probability.ProbabilityMassFunction.Constructions
import Mathlib.Probability.ProbabilityMassFunction.Monad
import Mathlib.Data.Nat.Log

namespace Crypto.Core.TracedStructure

universe u

structure CostGroupElem (G : Type u) [AddGroup G] [Fintype G] where
  val : G
  opCount : Nat
deriving Repr, DecidableEq

namespace CostGroupElem

variable {G : Type u} [AddGroup G] [Fintype G]

def ofValue (n : G) : CostGroupElem G :=
  ⟨n, 0⟩

def nsmulCost (k : Nat) : Nat :=
  Nat.clog 2 k

noncomputable def sample (dist : PMF G) : PMF (CostGroupElem G) :=
  do
    let n ← dist
    pure (ofValue n)

instance : Neg (CostGroupElem G) where
  neg a := ⟨-a.val, a.opCount⟩

instance : Add (CostGroupElem G) where
  add a b :=
    ⟨a.val + b.val, a.opCount + b.opCount + 1⟩

instance : Zero (CostGroupElem G) where
  zero := ofValue 0

instance : Sub (CostGroupElem G) where
  sub a b :=
    ⟨a.val - b.val, a.opCount + b.opCount + 1⟩

instance : SMul Nat (CostGroupElem G) where
  smul k a :=
    ⟨k • a.val, a.opCount + nsmulCost k⟩

instance : HMul Nat (CostGroupElem G) (CostGroupElem G) where
  hMul k a := k • a

-- Sampling theorems
@[simp] theorem ofValue_inj {m n : G} : ofValue m = ofValue n ↔ m = n := by
  constructor
  · intro h
    cases h
    rfl
  · intro h
    cases h
    rfl

theorem sample_eq_map (dist : PMF G) : sample dist = PMF.map ofValue dist := by
  rw [sample]
  simpa using (PMF.bind_pure_comp (f := ofValue) (p := dist))

@[simp] theorem sample_apply_ofValue (dist : PMF G) (n : G) :
    sample dist (ofValue n) = dist n := by
  rw [sample_eq_map, PMF.map_apply]
  rw [tsum_eq_single n]
  · simp
  · intro m hm
    have hneq : ofValue n ≠ ofValue m := by
      intro h
      apply hm
      simpa [ofValue_inj, eq_comm] using h
    simp [hneq]

theorem mem_support_sample_iff (dist : PMF G) (x : CostGroupElem G) :
    x ∈ (sample dist).support ↔ ∃ n ∈ dist.support, ofValue n = x := by
  rw [sample_eq_map, PMF.mem_support_map_iff]

@[simp] theorem ofValue_mem_support_sample_iff (dist : PMF G) (n : G) :
    ofValue n ∈ (sample dist).support ↔ n ∈ dist.support := by
  simp

theorem opCount_eq_zero_of_mem_support_sample {dist : PMF G} {x : CostGroupElem G}
  (hx : x ∈ (sample dist).support) : x.opCount = 0 := by
  rcases (mem_support_sample_iff dist x).mp hx with ⟨n, _, h⟩
  cases h
  rfl

-- Constant theorems
@[simp] theorem init_val (n : G) : (ofValue n).val = n := rfl

@[simp] theorem init_opCount (n : G) : (ofValue n).opCount = 0 := rfl

@[simp] theorem zero_val : (0 : CostGroupElem G).val = 0 := rfl

@[simp] theorem zero_opCount : (0 : CostGroupElem G).opCount = 0 := rfl

-- Operation theorems
@[simp] theorem neg_val (a : CostGroupElem G) :
  (-a).val = -a.val := rfl

@[simp] theorem neg_opCount (a : CostGroupElem G) :
  (-a).opCount = a.opCount := rfl

@[simp] theorem add_val (a b : CostGroupElem G) :
    (a + b).val = a.val + b.val := rfl

@[simp] theorem sub_val (a b : CostGroupElem G) :
  (a - b).val = a.val - b.val := rfl

@[simp] theorem add_opCount (a b : CostGroupElem G) :
    (a + b).opCount = a.opCount + b.opCount + 1 := rfl

@[simp] theorem sub_opCount (a b : CostGroupElem G) :
  (a - b).opCount = a.opCount + b.opCount + 1 := rfl

@[simp] theorem nsmul_val (k : Nat) (a : CostGroupElem G) :
  (k • a).val = k • a.val := rfl

@[simp] theorem nsmul_opCount (k : Nat) (a : CostGroupElem G) :
  (k • a).opCount = a.opCount + nsmulCost k := rfl

@[simp] theorem scalar_mul_val (k : Nat) (a : CostGroupElem G) :
  (k * a).val = k • a.val := rfl

@[simp] theorem scalar_mul_opCount (k : Nat) (a : CostGroupElem G) :
  (k * a).opCount = a.opCount + nsmulCost k := rfl

end CostGroupElem
end Crypto.Core.TracedStructure

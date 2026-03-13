import Mathlib.Probability.ProbabilityMassFunction.Basic
import Mathlib.Probability.ProbabilityMassFunction.Constructions
import Mathlib.Probability.ProbabilityMassFunction.Monad

namespace Crypto.Core.TracedStructure

structure CostInt where
  val : Int
  addCount : Nat
  mulCount : Nat
deriving Repr, DecidableEq

namespace CostInt

def ofValue (n : Int) : CostInt :=
  ⟨n, 0, 0⟩

noncomputable def sample (dist : PMF Int) : PMF CostInt :=
  do
    let n ← dist
    pure (ofValue n)

instance : Neg CostInt where
  neg a := ⟨-a.val, a.addCount, a.mulCount⟩

instance : Add CostInt where
  add a b :=
    ⟨a.val + b.val, a.addCount + b.addCount + 1, a.mulCount + b.mulCount⟩

instance : Zero CostInt where
  zero := ofValue 0

instance : One CostInt where
  one := ofValue 1

instance : Mul CostInt where
  mul a b :=
    ⟨a.val * b.val, a.addCount + b.addCount, a.mulCount + b.mulCount + 1⟩

instance : Sub CostInt where
  sub a b :=
  ⟨a.val - b.val, a.addCount + b.addCount + 1, a.mulCount + b.mulCount⟩

-- Sampling theorems
@[simp] theorem ofValue_inj {m n : Int} : ofValue m = ofValue n ↔ m = n := by
  constructor
  · intro h
    cases h
    rfl
  · intro h
    cases h
    rfl

theorem sample_eq_map (dist : PMF Int) : sample dist = PMF.map ofValue dist := by
  rw [sample]
  simpa using (PMF.bind_pure_comp (f := ofValue) (p := dist))

@[simp] theorem sample_apply_ofValue (dist : PMF Int) (n : Int) :
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

theorem mem_support_sample_iff (dist : PMF Int) (x : CostInt) :
    x ∈ (sample dist).support ↔ ∃ n ∈ dist.support, ofValue n = x := by
  rw [sample_eq_map, PMF.mem_support_map_iff]

@[simp] theorem ofValue_mem_support_sample_iff (dist : PMF Int) (n : Int) :
    ofValue n ∈ (sample dist).support ↔ n ∈ dist.support := by
  simp

theorem addCount_eq_zero_of_mem_support_sample {dist : PMF Int} {x : CostInt}
    (hx : x ∈ (sample dist).support) : x.addCount = 0 := by
  rcases (mem_support_sample_iff dist x).mp hx with ⟨n, _, h⟩
  cases h
  rfl

theorem mulCount_eq_zero_of_mem_support_sample {dist : PMF Int} {x : CostInt}
    (hx : x ∈ (sample dist).support) : x.mulCount = 0 := by
  rcases (mem_support_sample_iff dist x).mp hx with ⟨n, _, h⟩
  cases h
  rfl

-- Constant theorems
@[simp] theorem init_val (n : Int) : (ofValue n).val = n := rfl

@[simp] theorem init_addCount (n : Int) : (ofValue n).addCount = 0 := rfl

@[simp] theorem init_mulCount (n : Int) : (ofValue n).mulCount = 0 := rfl

@[simp] theorem zero_val : (0 : CostInt).val = 0 := rfl

@[simp] theorem zero_addCount : (0 : CostInt).addCount = 0 := rfl

@[simp] theorem zero_mulCount : (0 : CostInt).mulCount = 0 := rfl

@[simp] theorem one_val : (1 : CostInt).val = 1 := rfl

@[simp] theorem one_addCount : (1 : CostInt).addCount = 0 := rfl

@[simp] theorem one_mulCount : (1 : CostInt).mulCount = 0 := rfl

-- Operation theorems
@[simp] theorem neg_val (a : CostInt) :
  (-a).val = -a.val := rfl

@[simp] theorem neg_addCount (a : CostInt) :
  (-a).addCount = a.addCount := rfl

@[simp] theorem neg_mulCount (a : CostInt) :
  (-a).mulCount = a.mulCount := rfl

@[simp] theorem add_val (a b : CostInt) :
    (a + b).val = a.val + b.val := rfl

@[simp] theorem mul_val (a b : CostInt) :
    (a * b).val = a.val * b.val := rfl

@[simp] theorem sub_val (a b : CostInt) :
  (a - b).val = a.val - b.val := rfl

@[simp] theorem add_addCount (a b : CostInt) :
    (a + b).addCount = a.addCount + b.addCount + 1 := rfl

@[simp] theorem mul_mulCount (a b : CostInt) :
    (a * b).mulCount = a.mulCount + b.mulCount + 1 := rfl

@[simp] theorem sub_addCount (a b : CostInt) :
  (a - b).addCount = a.addCount + b.addCount + 1 := rfl

@[simp] theorem add_mulCount (a b : CostInt) :
    (a + b).mulCount = a.mulCount + b.mulCount := rfl

@[simp] theorem mul_addCount (a b : CostInt) :
    (a * b).addCount = a.addCount + b.addCount := rfl

@[simp] theorem sub_mulCount (a b : CostInt) :
  (a - b).mulCount = a.mulCount + b.mulCount := rfl

end CostInt
end Crypto.Core.TracedStructure

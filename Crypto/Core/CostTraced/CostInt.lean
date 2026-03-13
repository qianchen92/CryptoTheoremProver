namespace Crypto.Core.TracedStructure

structure CostInt where
  val : Int
  addCount : Nat
  mulCount : Nat
deriving Repr, DecidableEq

namespace CostInt

def ofValue (n : Int) : CostInt :=
  ⟨n, 0, 0⟩

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

@[simp] theorem init_val (n : Int) : (ofValue n).val = n := rfl

@[simp] theorem init_addCount (n : Int) : (ofValue n).addCount = 0 := rfl

@[simp] theorem init_mulCount (n : Int) : (ofValue n).mulCount = 0 := rfl

@[simp] theorem zero_val : (0 : CostInt).val = 0 := rfl

@[simp] theorem zero_addCount : (0 : CostInt).addCount = 0 := rfl

@[simp] theorem zero_mulCount : (0 : CostInt).mulCount = 0 := rfl

@[simp] theorem one_val : (1 : CostInt).val = 1 := rfl

@[simp] theorem one_addCount : (1 : CostInt).addCount = 0 := rfl

@[simp] theorem one_mulCount : (1 : CostInt).mulCount = 0 := rfl

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

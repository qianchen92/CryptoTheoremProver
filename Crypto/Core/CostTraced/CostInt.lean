namespace Crypto.Core.TracedStructure

structure TracedInt where
  val : Int
  addCount : Nat
  mulCount : Nat
deriving Repr, DecidableEq

namespace TracedInt

def ofValue (n : Int) : TracedInt :=
  ⟨n, 0, 0⟩

instance : Neg TracedInt where
  neg a := ⟨-a.val, a.addCount, a.mulCount⟩

instance : Add TracedInt where
  add a b :=
    ⟨a.val + b.val, a.addCount + b.addCount + 1, a.mulCount + b.mulCount⟩

instance : Zero TracedInt where
  zero := ofValue 0

instance : One TracedInt where
  one := ofValue 1

instance : Mul TracedInt where
  mul a b :=
    ⟨a.val * b.val, a.addCount + b.addCount, a.mulCount + b.mulCount + 1⟩

instance : Sub TracedInt where
  sub a b :=
  ⟨a.val - b.val, a.addCount + b.addCount + 1, a.mulCount + b.mulCount⟩

@[simp] theorem init_val (n : Int) : (ofValue n).val = n := rfl

@[simp] theorem init_addCount (n : Int) : (ofValue n).addCount = 0 := rfl

@[simp] theorem init_mulCount (n : Int) : (ofValue n).mulCount = 0 := rfl

@[simp] theorem zero_val : (0 : TracedInt).val = 0 := rfl

@[simp] theorem zero_addCount : (0 : TracedInt).addCount = 0 := rfl

@[simp] theorem zero_mulCount : (0 : TracedInt).mulCount = 0 := rfl

@[simp] theorem one_val : (1 : TracedInt).val = 1 := rfl

@[simp] theorem one_addCount : (1 : TracedInt).addCount = 0 := rfl

@[simp] theorem one_mulCount : (1 : TracedInt).mulCount = 0 := rfl

@[simp] theorem neg_val (a : TracedInt) :
  (-a).val = -a.val := rfl

@[simp] theorem neg_addCount (a : TracedInt) :
  (-a).addCount = a.addCount := rfl

@[simp] theorem neg_mulCount (a : TracedInt) :
  (-a).mulCount = a.mulCount := rfl

@[simp] theorem add_val (a b : TracedInt) :
    (a + b).val = a.val + b.val := rfl

@[simp] theorem mul_val (a b : TracedInt) :
    (a * b).val = a.val * b.val := rfl

@[simp] theorem sub_val (a b : TracedInt) :
  (a - b).val = a.val - b.val := rfl

@[simp] theorem add_addCount (a b : TracedInt) :
    (a + b).addCount = a.addCount + b.addCount + 1 := rfl

@[simp] theorem mul_mulCount (a b : TracedInt) :
    (a * b).mulCount = a.mulCount + b.mulCount + 1 := rfl

@[simp] theorem sub_addCount (a b : TracedInt) :
  (a - b).addCount = a.addCount + b.addCount + 1 := rfl

@[simp] theorem add_mulCount (a b : TracedInt) :
    (a + b).mulCount = a.mulCount + b.mulCount := rfl

@[simp] theorem mul_addCount (a b : TracedInt) :
    (a * b).addCount = a.addCount + b.addCount := rfl

@[simp] theorem sub_mulCount (a b : TracedInt) :
  (a - b).mulCount = a.mulCount + b.mulCount := rfl

end TracedInt
end Crypto.Core.TracedStructure

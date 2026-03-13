namespace Crypto.Core.TracedStructure

structure TracedNat where
  val : Nat
  addCount : Nat
  mulCount : Nat
deriving Repr, DecidableEq

namespace TracedNat

def ofValue (n : Nat) : TracedNat :=
  ⟨n, 0, 0⟩

instance {n : Nat} : OfNat TracedNat n where
  ofNat := ofValue n

instance : Add TracedNat where
  add a b :=
    ⟨a.val + b.val, a.addCount + b.addCount + 1, a.mulCount + b.mulCount⟩

instance : Zero TracedNat where
  zero := ofValue 0

instance : One TracedNat where
  one := ofValue 1

instance : Mul TracedNat where
  mul a b :=
    ⟨a.val * b.val, a.addCount + b.addCount, a.mulCount + b.mulCount + 1⟩

@[simp] theorem init_addCount (n : Nat) : (ofValue n).addCount = 0 := rfl

@[simp] theorem init_mulCount (n : Nat) : (ofValue n).mulCount = 0 := rfl

@[simp] theorem add_val (a b : TracedNat) :
    (a + b).val = a.val + b.val := rfl

@[simp] theorem mul_val (a b : TracedNat) :
    (a * b).val = a.val * b.val := rfl

@[simp] theorem add_addCount (a b : TracedNat) :
    (a + b).addCount = a.addCount + b.addCount + 1 := rfl

@[simp] theorem mul_mulCount (a b : TracedNat) :
    (a * b).mulCount = a.mulCount + b.mulCount + 1 := rfl

@[simp] theorem add_mulCount (a b : TracedNat) :
    (a + b).mulCount = a.mulCount + b.mulCount := rfl

@[simp] theorem mul_addCount (a b : TracedNat) :
    (a * b).addCount = a.addCount + b.addCount := rfl

end TracedNat
end Crypto.Core.TracedStructure

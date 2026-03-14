namespace Crypto.Core.CostStructure

universe u uR

structure Traced (α : Type u) where
  val : α
  cost : Nat
deriving Repr, DecidableEq

class HasAddCost (α : Type u) where
  addCost : Nat

class HasMulCost (α : Type u) where
  mulCost : Nat

class HasNegCost (α : Type u) where
  negCost : Nat
class HasSMulCost (R : Type uR) where
  smulCost : R → Nat

namespace Traced

def ofVal {α : Type u} (a : α) : Traced α :=
  ⟨a, 0⟩

def add {α : Type u} [Add α] [HasAddCost α]
    (a b : Traced α) : Traced α :=
  ⟨a.val + b.val, a.cost + b.cost + HasAddCost.addCost (α := α)⟩

def mul {α : Type u} [Mul α] [HasMulCost α]
    (a b : Traced α) : Traced α :=
  ⟨a.val * b.val, a.cost + b.cost + HasMulCost.mulCost (α := α)⟩

def neg {α : Type u} [Neg α] [HasNegCost α]
    (a : Traced α) : Traced α :=
  ⟨-a.val, a.cost + HasNegCost.negCost (α := α)⟩

def smul {R : Type uR} {α : Type u} [SMul R α] [HasSMulCost R]
    (r : R) (a : Traced α) : Traced α :=
  ⟨r • a.val, a.cost + HasSMulCost.smulCost (R := R) r⟩

instance {α : Type u} [Add α] [HasAddCost α] : Add (Traced α) where
  add := Traced.add

instance {α : Type u} [Neg α] [HasNegCost α] : Neg (Traced α) where
  neg := Traced.neg

instance {α : Type u} [Mul α] [HasMulCost α] : Mul (Traced α) where
  mul := Traced.mul

instance {R : Type uR} {α : Type u} [SMul R α] [HasSMulCost R] : SMul R (Traced α) where
  smul := Traced.smul

@[simp] theorem ofVal_val {α : Type u} (a : α) : (ofVal a).val = a := rfl

@[simp] theorem ofVal_cost {α : Type u} (a : α) : (ofVal a).cost = 0 := rfl

@[simp] theorem add_val {α : Type u} [Add α] [HasAddCost α]
    (a b : Traced α) : (Traced.add a b).val = a.val + b.val := rfl

@[simp] theorem add_cost {α : Type u} [Add α] [HasAddCost α]
    (a b : Traced α) :
    (Traced.add a b).cost = a.cost + b.cost + HasAddCost.addCost (α := α) := rfl

end Traced
end Crypto.Core.CostStructure

namespace Crypto.Core.CostStructure

universe u uR

structure Traced (α : Type u) where
  val : α
  cost : Nat
deriving Repr, DecidableEq

class HasAddCost (α : Type u) where
  addCost : Nat := 1

class HasMulCost (α : Type u) where
  mulCost : Nat := 1

class HasNegCost (α : Type u) where
  negCost : Nat := 1

class HasSMulCost (R : Type uR) where
  smulCost : R → Nat

namespace Traced

def pure {α : Type u} (a : α) : Traced α :=
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

end Traced
end Crypto.Core.CostStructure

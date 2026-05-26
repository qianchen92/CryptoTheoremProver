import Crypto.Infrastructure.Computation.Cost.Costed

namespace Crypto.Infrastructure.Computation.Algebra

universe uValue uScalar

namespace Costed

open Crypto.Infrastructure.Computation.Cost

def add {α : Type uValue} [Add α] [AddCost α] (a b : Costed α) : Costed α :=
  ⟨a.val + b.val, a.cost + b.cost + AddCost.addCost (α := α)⟩

def mul {α : Type uValue} [Mul α] [MulCost α] (a b : Costed α) : Costed α :=
  ⟨a.val * b.val, a.cost + b.cost + MulCost.mulCost (α := α)⟩

def neg {α : Type uValue} [Neg α] [NegCost α] (a : Costed α) : Costed α :=
  ⟨-a.val, a.cost + NegCost.negCost (α := α)⟩

def sub {α : Type uValue} [Sub α] [SubCost α] (a b : Costed α) : Costed α :=
  ⟨a.val - b.val, a.cost + b.cost + SubCost.subCost (α := α)⟩

def smul {R : Type uScalar} {α : Type uValue} [SMul R α] [SMulCost R α]
    (r : R) (a : Costed α) : Costed α :=
  ⟨r • a.val, a.cost + SMulCost.smulCost (R := R) (α := α) r⟩

instance {α : Type uValue} [Zero α] : Zero (Costed α) where
  zero := Crypto.Infrastructure.Computation.Cost.Costed.ofValue 0

instance {α : Type uValue} [One α] : One (Costed α) where
  one := Crypto.Infrastructure.Computation.Cost.Costed.ofValue 1

instance {α : Type uValue} [Add α] [AddCost α] : Add (Costed α) where
  add := add

instance {α : Type uValue} [Mul α] [MulCost α] : Mul (Costed α) where
  mul := mul

instance {α : Type uValue} [Neg α] [NegCost α] : Neg (Costed α) where
  neg := neg

instance {α : Type uValue} [Sub α] [SubCost α] : Sub (Costed α) where
  sub := sub

instance {R : Type uScalar} {α : Type uValue} [SMul R α] [SMulCost R α] :
    SMul R (Costed α) where
  smul := smul

instance {R : Type uScalar} {α : Type uValue} [SMul R α] [SMulCost R α] :
    HMul R (Costed α) (Costed α) where
  hMul := smul

@[simp] theorem zero_val {α : Type uValue} [Zero α] : (0 : Costed α).val = 0 := rfl

@[simp] theorem zero_cost {α : Type uValue} [Zero α] : (0 : Costed α).cost = 0 := rfl

@[simp] theorem one_val {α : Type uValue} [One α] : (1 : Costed α).val = 1 := rfl

@[simp] theorem one_cost {α : Type uValue} [One α] : (1 : Costed α).cost = 0 := rfl

@[simp] theorem add_val {α : Type uValue} [Add α] [AddCost α] (a b : Costed α) :
    (a + b).val = a.val + b.val :=
  rfl

@[simp] theorem add_cost {α : Type uValue} [Add α] [AddCost α] (a b : Costed α) :
    (a + b).cost = a.cost + b.cost + AddCost.addCost (α := α) :=
  rfl

@[simp] theorem mul_val {α : Type uValue} [Mul α] [MulCost α] (a b : Costed α) :
    (a * b).val = a.val * b.val :=
  rfl

@[simp] theorem mul_cost {α : Type uValue} [Mul α] [MulCost α] (a b : Costed α) :
    (a * b).cost = a.cost + b.cost + MulCost.mulCost (α := α) :=
  rfl

@[simp] theorem neg_val {α : Type uValue} [Neg α] [NegCost α] (a : Costed α) :
    (-a).val = -a.val :=
  rfl

@[simp] theorem neg_cost {α : Type uValue} [Neg α] [NegCost α] (a : Costed α) :
    (-a).cost = a.cost + NegCost.negCost (α := α) :=
  rfl

@[simp] theorem sub_val {α : Type uValue} [Sub α] [SubCost α] (a b : Costed α) :
    (a - b).val = a.val - b.val :=
  rfl

@[simp] theorem sub_cost {α : Type uValue} [Sub α] [SubCost α] (a b : Costed α) :
    (a - b).cost = a.cost + b.cost + SubCost.subCost (α := α) :=
  rfl

@[simp] theorem smul_val {R : Type uScalar} {α : Type uValue} [SMul R α] [SMulCost R α]
    (r : R) (a : Costed α) :
    (r • a).val = r • a.val :=
  rfl

@[simp] theorem smul_cost {R : Type uScalar} {α : Type uValue} [SMul R α] [SMulCost R α]
    (r : R) (a : Costed α) :
    (r • a).cost = a.cost + SMulCost.smulCost (R := R) (α := α) r :=
  rfl

@[simp] theorem hMul_val {R : Type uScalar} {α : Type uValue} [SMul R α] [SMulCost R α]
    (r : R) (a : Costed α) :
    (r * a).val = r • a.val :=
  rfl

@[simp] theorem hMul_cost {R : Type uScalar} {α : Type uValue} [SMul R α] [SMulCost R α]
    (r : R) (a : Costed α) :
    (r * a).cost = a.cost + SMulCost.smulCost (R := R) (α := α) r :=
  rfl

end Costed

end Crypto.Infrastructure.Computation.Algebra

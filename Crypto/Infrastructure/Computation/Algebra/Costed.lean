import Crypto.Infrastructure.Computation.Cost.Costed

namespace Crypto.Infrastructure.Computation.Algebra

universe uValue uScalar

namespace Costed

open Crypto.Infrastructure.Computation.Cost

def add {α : Type uValue} [Add α] [AddCost α] (a b : α) : Costed α :=
  ⟨a + b, AddCost.addCost a b⟩

def mul {α : Type uValue} [Mul α] [MulCost α] (a b : α) : Costed α :=
  ⟨a * b, MulCost.mulCost a b⟩

def neg {α : Type uValue} [Neg α] [NegCost α] (a : α) : Costed α :=
  ⟨-a, NegCost.negCost a⟩

def sub {α : Type uValue} [Sub α] [SubCost α] (a b : α) : Costed α :=
  ⟨a - b, SubCost.subCost a b⟩

def smul {R : Type uScalar} {α : Type uValue} [SMul R α] [SMulCost R α]
    (r : R) (a : α) : Costed α :=
  ⟨r • a, SMulCost.smulCost r a⟩

@[simp] theorem add_val {α : Type uValue} [Add α] [AddCost α] (a b : α) :
    (add a b).val = a + b :=
  rfl

@[simp] theorem add_cost {α : Type uValue} [Add α] [AddCost α] (a b : α) :
    (add a b).cost = AddCost.addCost a b :=
  rfl

@[simp] theorem mul_val {α : Type uValue} [Mul α] [MulCost α] (a b : α) :
    (mul a b).val = a * b :=
  rfl

@[simp] theorem mul_cost {α : Type uValue} [Mul α] [MulCost α] (a b : α) :
    (mul a b).cost = MulCost.mulCost a b :=
  rfl

@[simp] theorem neg_val {α : Type uValue} [Neg α] [NegCost α] (a : α) :
    (neg a).val = -a :=
  rfl

@[simp] theorem neg_cost {α : Type uValue} [Neg α] [NegCost α] (a : α) :
    (neg a).cost = NegCost.negCost a :=
  rfl

@[simp] theorem sub_val {α : Type uValue} [Sub α] [SubCost α] (a b : α) :
    (sub a b).val = a - b :=
  rfl

@[simp] theorem sub_cost {α : Type uValue} [Sub α] [SubCost α] (a b : α) :
    (sub a b).cost = SubCost.subCost a b :=
  rfl

@[simp] theorem smul_val {R : Type uScalar} {α : Type uValue} [SMul R α] [SMulCost R α]
    (r : R) (a : α) :
    (smul r a).val = r • a :=
  rfl

@[simp] theorem smul_cost {R : Type uScalar} {α : Type uValue} [SMul R α] [SMulCost R α]
    (r : R) (a : α) :
    (smul r a).cost = SMulCost.smulCost r a :=
  rfl

end Costed

end Crypto.Infrastructure.Computation.Algebra

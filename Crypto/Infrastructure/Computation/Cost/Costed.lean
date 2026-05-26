import Crypto.Infrastructure.Computation.Cost.Model

namespace Crypto.Infrastructure.Computation.Cost

universe uValue uMapped

/-- A value paired with the operation cost accumulated while computing it. -/
structure Costed (α : Type uValue) where
  val : α
  cost : Cost
deriving Repr, DecidableEq

namespace Costed

/-- Inject a value with zero accumulated cost. -/
def ofValue {α : Type uValue} (a : α) : Costed α :=
  ⟨a, 0⟩

/-- Map a pure function over the value while preserving accumulated cost. -/
def map {α : Type uValue} {β : Type uMapped} (f : α → β) (x : Costed α) : Costed β :=
  ⟨f x.val, x.cost⟩

@[simp] theorem ofValue_val {α : Type uValue} (a : α) : (ofValue a).val = a := rfl

@[simp] theorem ofValue_cost {α : Type uValue} (a : α) : (ofValue a).cost = 0 := rfl

@[simp] theorem map_val {α : Type uValue} {β : Type uMapped} (f : α → β) (x : Costed α) :
    (x.map f).val = f x.val :=
  rfl

@[simp] theorem map_cost {α : Type uValue} {β : Type uMapped} (f : α → β) (x : Costed α) :
    (x.map f).cost = x.cost :=
  rfl

end Costed

end Crypto.Infrastructure.Computation.Cost

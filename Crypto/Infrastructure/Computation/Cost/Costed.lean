import Crypto.Infrastructure.Computation.Cost.Model

namespace Crypto.Infrastructure.Computation.Cost

universe uValue uMapped

/-- A value paired with the operation cost accumulated while computing it. -/
structure Costed (α : Type uValue) where
  val : α
  cost : Cost
deriving Repr, DecidableEq

namespace Costed

/-- The zero-cost writer computation returning `a`. -/
def pure {α : Type uValue} (a : α) : Costed α :=
  ⟨a, 0⟩

/-- Map a pure function over the value while preserving accumulated cost. -/
def map {α : Type uValue} {β : Type uMapped} (f : α → β) (x : Costed α) : Costed β :=
  ⟨f x.val, x.cost⟩

/-- Sequence two writer computations, adding their path costs exactly once. -/
def bind {α : Type uValue} {β : Type uMapped}
    (x : Costed α) (next : α → Costed β) : Costed β :=
  let result := next x.val
  ⟨result.val, x.cost + result.cost⟩

instance : Monad Costed where
  pure := fun value => Costed.pure value
  bind := fun value next => Costed.bind value next
  map := fun f value => Costed.map f value

@[simp] theorem pure_val {α : Type uValue} (a : α) : (pure a).val = a := rfl

@[simp] theorem pure_cost {α : Type uValue} (a : α) : (pure a).cost = 0 := rfl

@[simp] theorem map_val {α : Type uValue} {β : Type uMapped} (f : α → β) (x : Costed α) :
    (x.map f).val = f x.val :=
  rfl

@[simp] theorem map_cost {α : Type uValue} {β : Type uMapped} (f : α → β) (x : Costed α) :
    (x.map f).cost = x.cost :=
  rfl

@[simp] theorem bind_val {α : Type uValue} {β : Type uMapped}
    (x : Costed α) (next : α → Costed β) :
    (x.bind next).val = (next x.val).val :=
  rfl

@[simp] theorem bind_cost {α : Type uValue} {β : Type uMapped}
    (x : Costed α) (next : α → Costed β) :
    (x.bind next).cost = x.cost + (next x.val).cost :=
  rfl

end Costed

end Crypto.Infrastructure.Computation.Cost

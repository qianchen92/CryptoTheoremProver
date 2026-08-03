import Crypto.Infrastructure.Computation.Cost.Model

namespace Crypto.Infrastructure.Computation.Cost

universe uCost uValue uMapped

/-- A value paired with the exact resource cost accumulated while computing it. -/
structure CostedT (M : CostModel.{uCost}) (α : Type uValue) where
  val : α
  cost : M.Cost

namespace CostedT

variable {M : CostModel.{uCost}} {α : Type uValue}

/-- A costed result is equivalent to its value/cost pair. -/
def equivProd : CostedT M α ≃ α × M.Cost where
  toFun result := (result.val, result.cost)
  invFun result := ⟨result.1, result.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

instance [Repr α] [Repr M.Cost] : Repr (CostedT M α) where
  reprPrec result precedence := reprPrec (result.val, result.cost) precedence

instance [DecidableEq α] [DecidableEq M.Cost] : DecidableEq (CostedT M α) :=
  equivProd.decidableEq

/-- The zero-cost writer computation returning `value`. -/
def pure (M : CostModel.{uCost}) {α : Type uValue} (value : α) : CostedT M α := by
  letI := M.instAddMonoid
  exact ⟨value, 0⟩

/-- Map a pure function over the value while preserving accumulated cost. -/
def map {M : CostModel.{uCost}} {α : Type uValue} {β : Type uMapped}
    (f : α → β) (result : CostedT M α) : CostedT M β :=
  ⟨f result.val, result.cost⟩

/-- Sequence two writer computations, composing their path costs exactly once. -/
def bind {M : CostModel.{uCost}} {α : Type uValue} {β : Type uMapped}
    (result : CostedT M α) (next : α → CostedT M β) : CostedT M β := by
  letI := M.instAddMonoid
  exact
    let nextResult := next result.val
    ⟨nextResult.val, result.cost + nextResult.cost⟩

instance (M : CostModel.{uCost}) : Monad (CostedT M) where
  pure := fun value => CostedT.pure M value
  bind := fun result next => CostedT.bind result next
  map := fun f result => CostedT.map f result

@[simp] theorem pure_val (M : CostModel.{uCost}) {α : Type uValue} (value : α) :
    (pure M value).val = value :=
  rfl

@[simp] theorem pure_cost (M : CostModel.{uCost}) {α : Type uValue} (value : α) :
    (pure M value).cost = M.instAddMonoid.zero :=
  rfl

@[simp] theorem map_val (M : CostModel.{uCost})
    {α : Type uValue} {β : Type uMapped} (f : α → β) (result : CostedT M α) :
    (result.map f).val = f result.val :=
  rfl

@[simp] theorem map_cost (M : CostModel.{uCost})
    {α : Type uValue} {β : Type uMapped} (f : α → β) (result : CostedT M α) :
    (result.map f).cost = result.cost :=
  rfl

@[simp] theorem bind_val (M : CostModel.{uCost})
    {α : Type uValue} {β : Type uMapped}
    (result : CostedT M α) (next : α → CostedT M β) :
    (result.bind next).val = (next result.val).val :=
  rfl

@[simp] theorem bind_cost (M : CostModel.{uCost})
    {α : Type uValue} {β : Type uMapped}
    (result : CostedT M α) (next : α → CostedT M β) :
    (result.bind next).cost =
      M.instAddMonoid.add result.cost (next result.val).cost :=
  rfl

/-- Mapping the identity function does not change a deterministic writer result. -/
@[simp] theorem map_id (result : CostedT M α) :
    map id result = result := by
  cases result
  rfl

/-- Deterministic writer maps compose. -/
theorem map_comp {β γ : Type uMapped}
    (first : α → β) (second : β → γ) (result : CostedT M α) :
    map second (map first result) = map (second ∘ first) result := by
  cases result
  rfl

/-- Zero-cost pure is a left identity for deterministic writer sequencing. -/
@[simp] theorem pure_bind {β : Type uMapped}
    (value : α) (next : α → CostedT M β) :
    bind (pure M value) next = next value := by
  letI := M.instAddMonoid
  cases hnext : next value
  simp [bind, pure, hnext]

/-- Zero-cost pure is a right identity for deterministic writer sequencing. -/
@[simp] theorem bind_pure (result : CostedT M α) :
    bind result (pure M) = result := by
  letI := M.instAddMonoid
  cases result
  simp [bind, pure]

/-- Deterministic writer sequencing is associative in execution order. -/
theorem bind_assoc {β γ : Type uMapped}
    (result : CostedT M α) (next : α → CostedT M β)
    (finish : β → CostedT M γ) :
    bind (bind result next) finish =
      bind result (fun value => bind (next value) finish) := by
  letI := M.instAddMonoid
  cases result with
  | mk value cost =>
      cases hnext : next value with
      | mk nextValue nextCost =>
          cases hfinish : finish nextValue with
          | mk finalValue finalCost =>
              simp [bind, hnext, hfinish, add_assoc]

/-- `CostedT` is the lawful writer monad for the model's sequential monoid. -/
instance (M : CostModel.{uCost}) : LawfulMonad (CostedT M) :=
  LawfulMonad.mk'
    (id_map := fun result => map_id result)
    (pure_bind := fun value next => pure_bind value next)
    (bind_assoc := fun result next finish => bind_assoc result next finish)
    (bind_pure_comp := by
      intro α β f result
      letI := M.instAddMonoid
      cases result
      simp [Bind.bind, Pure.pure, Functor.map, bind, pure, map])

end CostedT

/-- Backwards-compatible natural-number costed computation. -/
abbrev Costed (α : Type uValue) := CostedT natCostModel α

namespace Costed

/-- Backwards-compatible constructor for a natural-number costed result. -/
abbrev mk {α : Type uValue} : α → Cost → Costed α :=
  CostedT.mk (M := natCostModel)

/-- Backwards-compatible value projection. -/
abbrev val {α : Type uValue} : Costed α → α :=
  CostedT.val

/-- Backwards-compatible cost projection. -/
abbrev cost {α : Type uValue} : Costed α → Cost :=
  CostedT.cost

/-- The zero-cost natural-number writer computation returning `value`. -/
abbrev pure {α : Type uValue} (value : α) : Costed α :=
  CostedT.pure natCostModel value

/-- Map a pure function over a natural-number costed result. -/
abbrev map {α : Type uValue} {β : Type uMapped}
    (f : α → β) (result : Costed α) : Costed β :=
  CostedT.map f result

/-- Sequence natural-number writer computations. -/
abbrev bind {α : Type uValue} {β : Type uMapped}
    (result : Costed α) (next : α → Costed β) : Costed β :=
  CostedT.bind result next

@[simp] theorem pure_val {α : Type uValue} (value : α) : (pure value).val = value := rfl

@[simp] theorem pure_cost {α : Type uValue} (value : α) : (pure value).cost = 0 := rfl

@[simp] theorem map_val {α : Type uValue} {β : Type uMapped}
    (f : α → β) (result : Costed α) :
    (result.map f).val = f result.val :=
  rfl

@[simp] theorem map_cost {α : Type uValue} {β : Type uMapped}
    (f : α → β) (result : Costed α) :
    (result.map f).cost = result.cost :=
  rfl

@[simp] theorem bind_val {α : Type uValue} {β : Type uMapped}
    (result : Costed α) (next : α → Costed β) :
    (result.bind next).val = (next result.val).val :=
  rfl

@[simp] theorem bind_cost {α : Type uValue} {β : Type uMapped}
    (result : Costed α) (next : α → Costed β) :
    (result.bind next).cost = result.cost + (next result.val).cost :=
  rfl

end Costed

end Crypto.Infrastructure.Computation.Cost

import Crypto.Infrastructure.Computation.Cost.Model

namespace Crypto.Infrastructure.Computation.Cost

universe uCost uValue uMapped

/-- A value paired with the exact resource cost accumulated while computing it. -/
structure Costed (M : CostModel.{uCost}) (α : Type uValue) where
  val : α
  cost : M.Cost

namespace Costed

variable
    {M : CostModel.{uCost}}
    {α : Type uValue} {β γ : Type uMapped}

/-- A costed result is equivalent to its value/cost pair. -/
def equivProd : Costed M α ≃ α × M.Cost where
  toFun result := (result.val, result.cost)
  invFun result := ⟨result.1, result.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

instance [Repr α] [Repr M.Cost] : Repr (Costed M α) where
  reprPrec result precedence := reprPrec (result.val, result.cost) precedence

instance [DecidableEq α] [DecidableEq M.Cost] : DecidableEq (Costed M α) :=
  equivProd.decidableEq

/-- The zero-cost writer computation returning `value`. -/
def pure (M : CostModel.{uCost}) {α : Type uValue} (value : α) : Costed M α := by
  letI := M.instAddMonoid
  exact ⟨value, 0⟩

/-- Map a pure function over the value while preserving accumulated cost. -/
def map (f : α → β) (result : Costed M α) : Costed M β :=
  ⟨f result.val, result.cost⟩

/-- Sequence two writer computations, composing their path costs exactly once. -/
def bind (result : Costed M α) (next : α → Costed M β) : Costed M β := by
  letI := M.instAddMonoid
  exact
    let nextResult := next result.val
    ⟨nextResult.val, result.cost + nextResult.cost⟩

instance (M : CostModel.{uCost}) : Monad (Costed M) where
  pure := fun value => Costed.pure M value
  bind := fun result next => Costed.bind result next
  map := fun f result => Costed.map f result

section ModelLemmas

variable (M : CostModel.{uCost}) {α : Type uValue} {β : Type uMapped}

@[simp] theorem pure_val (value : α) :
    (pure M value).val = value :=
  rfl

@[simp] theorem pure_cost (value : α) :
    (pure M value).cost = M.instAddMonoid.zero :=
  rfl

@[simp] theorem map_val (f : α → β) (result : Costed M α) :
    (result.map f).val = f result.val :=
  rfl

@[simp] theorem map_cost (f : α → β) (result : Costed M α) :
    (result.map f).cost = result.cost :=
  rfl

@[simp] theorem bind_val
    (result : Costed M α) (next : α → Costed M β) :
    (result.bind next).val = (next result.val).val :=
  rfl

@[simp] theorem bind_cost
    (result : Costed M α) (next : α → Costed M β) :
    (result.bind next).cost =
      M.instAddMonoid.add result.cost (next result.val).cost :=
  rfl

end ModelLemmas

/-- Mapping the identity function does not change a deterministic writer result. -/
@[simp] theorem map_id (result : Costed M α) :
    map id result = result := by
  cases result
  rfl

/-- Deterministic writer maps compose. -/
theorem map_comp
    (first : α → β) (second : β → γ) (result : Costed M α) :
    map second (map first result) = map (second ∘ first) result := by
  cases result
  rfl

/-- Zero-cost pure is a left identity for deterministic writer sequencing. -/
@[simp] theorem pure_bind (value : α) (next : α → Costed M β) :
    bind (pure M value) next = next value := by
  letI := M.instAddMonoid
  cases hnext : next value
  simp [bind, pure, hnext]

/-- Zero-cost pure is a right identity for deterministic writer sequencing. -/
@[simp] theorem bind_pure (result : Costed M α) :
    bind result (pure M) = result := by
  letI := M.instAddMonoid
  cases result
  simp [bind, pure]

/-- Deterministic writer sequencing is associative in execution order. -/
theorem bind_assoc
    (result : Costed M α) (next : α → Costed M β)
    (finish : β → Costed M γ) :
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

/-- `Costed` is the lawful writer monad for the model's sequential monoid. -/
instance (M : CostModel.{uCost}) : LawfulMonad (Costed M) :=
  LawfulMonad.mk'
    (id_map := fun result => map_id result)
    (pure_bind := fun value next => pure_bind value next)
    (bind_assoc := fun result next finish => bind_assoc result next finish)
    (bind_pure_comp := by
      intro α β f result
      letI := M.instAddMonoid
      cases result
      simp [Bind.bind, Pure.pure, Functor.map, bind, pure, map])

end Costed

end Crypto.Infrastructure.Computation.Cost

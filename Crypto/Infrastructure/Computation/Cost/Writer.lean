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
  exact ⟨value, M.instAddMonoid.zero⟩

/-- Map a pure function over the value while preserving accumulated cost. -/
def map (f : α → β) (result : Costed M α) : Costed M β :=
  ⟨f result.val, result.cost⟩

/-- Sequence two writer computations, composing their path costs exactly once. -/
def bind (result : Costed M α) (next : α → Costed M β) : Costed M β := by
  exact
    let nextResult := next result.val
    ⟨nextResult.val,
      M.instAddMonoid.add result.cost nextResult.cost⟩

instance (M : CostModel.{uCost}) : Monad (Costed M) where
  pure := fun value => Costed.pure M value
  bind := fun result next => Costed.bind result next
  map := fun f result => Costed.map f result

section ModelLemmas

variable (M : CostModel.{uCost}) {α : Type uValue} {β : Type uMapped}

/-- The model's explicit zero is a left identity for its explicit addition. -/
@[simp] theorem model_zero_add (cost : M.Cost) :
    M.instAddMonoid.add M.instAddMonoid.zero cost = cost :=
  M.instAddMonoid.zero_add cost

/-- The model's explicit zero is a right identity for its explicit addition. -/
@[simp] theorem model_add_zero (cost : M.Cost) :
    M.instAddMonoid.add cost M.instAddMonoid.zero = cost :=
  M.instAddMonoid.add_zero cost

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
  cases hnext : next value with
  | mk nextValue nextCost =>
      simp only [bind, pure, hnext]
      exact congrArg (fun cost => Costed.mk nextValue cost)
        (M.instAddMonoid.zero_add nextCost)

/-- Zero-cost pure is a right identity for deterministic writer sequencing. -/
@[simp] theorem bind_pure (result : Costed M α) :
    bind result (pure M) = result := by
  cases result with
  | mk value cost =>
      change
        Costed.mk value
            (M.instAddMonoid.add cost M.instAddMonoid.zero) =
          Costed.mk value cost
      exact congrArg (fun nextCost => Costed.mk value nextCost)
        (M.instAddMonoid.add_zero cost)

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
              simp only [bind, hnext, hfinish]
              change
                Costed.mk finalValue
                    (M.instAddMonoid.add
                      (M.instAddMonoid.add cost nextCost) finalCost) =
                  Costed.mk finalValue
                    (M.instAddMonoid.add cost
                      (M.instAddMonoid.add nextCost finalCost))
              exact congrArg (fun total => Costed.mk finalValue total)
                (M.instAddMonoid.add_assoc cost nextCost finalCost)

/-- `Costed` is the lawful writer monad for the model's sequential monoid. -/
instance (M : CostModel.{uCost}) : LawfulMonad (Costed M) :=
  LawfulMonad.mk'
    (id_map := fun result => map_id result)
    (pure_bind := fun value next => pure_bind value next)
    (bind_assoc := fun result next finish => bind_assoc result next finish)
    (bind_pure_comp := by
      intro α β f result
      cases result with
      | mk value cost =>
          change
            Costed.mk (f value)
                (M.instAddMonoid.add cost M.instAddMonoid.zero) =
              Costed.mk (f value) cost
          exact congrArg (fun total => Costed.mk (f value) total)
            (M.instAddMonoid.add_zero cost))

end Costed

end Crypto.Infrastructure.Computation.Cost

import Crypto.Infrastructure.Computation.Cost.Writer
import Mathlib.Probability.ProbabilityMassFunction.Constructions
import Mathlib.Probability.ProbabilityMassFunction.Monad

namespace Crypto.Infrastructure.Computation.Cost

universe uCost uValue uMapped

/-- A randomized computation whose paths carry costs from `M`. -/
def RandCosted (M : CostModel.{uCost}) (α : Type uValue) := PMF (Costed M α)

namespace RandCosted

noncomputable section

/-- Lift one deterministic writer result to a point-mass randomized computation. -/
abbrev liftCosted {M : CostModel.{uCost}} {α : Type uValue}
    (result : Costed M α) : RandCosted M α :=
  PMF.pure result

/-- Return a value with zero path cost. -/
abbrev pure (M : CostModel.{uCost}) {α : Type uValue}
    (value : α) : RandCosted M α :=
  liftCosted (Costed.pure M value)

/-- Map a pure function over randomized results while preserving every path cost. -/
abbrev map {M : CostModel.{uCost}}
    {α : Type uValue} {β : Type uMapped}
    (f : α → β) (dist : RandCosted M α) : RandCosted M β :=
  PMF.map (Costed.map f) dist

/--
Sequence randomized writer computations.

The continuation receives the ordinary value, and each resulting path records
the sequential composition of the first and second path costs exactly once.
-/
abbrev bind {M : CostModel.{uCost}}
    {α : Type uValue} {β : Type uMapped}
    (dist : RandCosted M α) (next : α → RandCosted M β) : RandCosted M β :=
  PMF.bind dist fun first =>
    PMF.map
      (fun second : Costed M β => first.bind fun _ => second)
      (next first.val)

noncomputable instance (M : CostModel.{uCost}) : Monad (RandCosted M) where
  pure := fun value => RandCosted.pure M value
  bind := fun dist next => RandCosted.bind dist next
  map := fun f dist => RandCosted.map f dist

/-- Randomized writer maps preserve identity. -/
@[simp] theorem map_id {M : CostModel.{uCost}}
    {α : Type uValue} (dist : RandCosted M α) :
    map id dist = dist := by
  change
    PMF.map (fun result : Costed M α => Costed.map id result) dist = dist
  have mapIdentity :
      (fun result : Costed M α => Costed.map id result) = id := by
    funext result
    exact Costed.map_id result
  rw [mapIdentity, PMF.map_id]

/-- Randomized writer maps compose without changing path costs. -/
theorem map_comp {M : CostModel.{uCost}}
    {α : Type uValue} {β γ : Type uMapped}
    (first : α → β) (second : β → γ) (dist : RandCosted M α) :
    map second (map first dist) = map (second ∘ first) dist := by
  change
    PMF.map (Costed.map second) (PMF.map (Costed.map first) dist) =
      PMF.map (Costed.map (second ∘ first)) dist
  rw [PMF.map_comp]
  apply congrArg (fun transform => PMF.map transform dist)
  funext result
  exact Costed.map_comp first second result

/-- Randomized zero-cost pure is a left identity for writer sequencing. -/
@[simp] theorem pure_bind {M : CostModel.{uCost}}
    {α : Type uValue} {β : Type uMapped}
    (value : α) (next : α → RandCosted M β) :
    bind (pure M value) next = next value := by
  change
    PMF.bind (PMF.pure (Costed.pure M value))
        (fun firstResult =>
          PMF.map
            (fun nextResult => firstResult.bind fun _value => nextResult)
            (next firstResult.val)) =
      next value
  rw [PMF.pure_bind]
  have bindIdentity :
      (fun nextResult : Costed M β =>
        (Costed.pure M value).bind fun _value => nextResult) = id := by
    funext nextResult
    exact Costed.pure_bind value (fun _value => nextResult)
  rw [bindIdentity, PMF.map_id]
  rfl

/-- Randomized zero-cost pure is a right identity for writer sequencing. -/
@[simp] theorem bind_pure {M : CostModel.{uCost}}
    {α : Type uValue} (dist : RandCosted M α) :
    bind dist (fun value => pure M value) = dist := by
  change
    PMF.bind dist
        (fun firstResult =>
          PMF.map
            (fun nextResult => firstResult.bind fun _value => nextResult)
            (PMF.pure (Costed.pure M firstResult.val))) =
      dist
  simp only [PMF.pure_map]
  have handlerIdentity :
      (fun firstResult : Costed M α =>
        PMF.pure
          (firstResult.bind fun _value => Costed.pure M firstResult.val)) =
        PMF.pure := by
    funext firstResult
    apply congrArg PMF.pure
    change firstResult.bind (Costed.pure M) = firstResult
    exact Costed.bind_pure firstResult
  rw [handlerIdentity, PMF.bind_pure]

/-- Randomized writer sequencing is associative in execution order. -/
theorem bind_assoc {M : CostModel.{uCost}}
    {α : Type uValue} {β γ : Type uMapped}
    (dist : RandCosted M α) (next : α → RandCosted M β)
    (finish : β → RandCosted M γ) :
    bind (bind dist next) finish =
      bind dist (fun value => bind (next value) finish) := by
  simp only [bind, PMF.bind_bind, PMF.bind_map, PMF.map_bind,
    PMF.map_comp]
  apply congrArg (PMF.bind dist)
  funext firstResult
  apply congrArg (PMF.bind (next firstResult.val))
  funext nextResult
  apply congrArg
    (fun transform => PMF.map transform (finish nextResult.val))
  funext finalResult
  exact
    Costed.bind_assoc firstResult
      (fun _value => nextResult) (fun _value => finalResult)

/-- Binding a randomized writer into zero-cost pure is its value-only map. -/
theorem bind_pure_comp {M : CostModel.{uCost}}
    {α : Type uValue} {β : Type uMapped}
    (f : α → β) (dist : RandCosted M α) :
    bind dist (fun value => pure M (f value)) = map f dist := by
  change
    PMF.bind dist
        (fun firstResult =>
          PMF.map
            (fun nextResult => firstResult.bind fun _value => nextResult)
            (PMF.pure (Costed.pure M (f firstResult.val)))) =
      PMF.map (Costed.map f) dist
  simp only [PMF.pure_map]
  have handlerEquality :
      (fun firstResult : Costed M α =>
        PMF.pure
          (firstResult.bind fun _value => Costed.pure M (f firstResult.val))) =
        (PMF.pure ∘ Costed.map f) := by
    funext firstResult
    apply congrArg PMF.pure
    letI := M.instAddMonoid
    cases firstResult
    simp [Costed.bind, Costed.pure, Costed.map]
  rw [handlerEquality]
  exact PMF.bind_pure_comp (Costed.map f) dist

/-- `RandCosted` is the lawful randomized writer monad. -/
noncomputable instance (M : CostModel.{uCost}) : LawfulMonad (RandCosted M) :=
  LawfulMonad.mk'
    (id_map := fun dist => map_id dist)
    (pure_bind := fun value next => pure_bind value next)
    (bind_assoc := fun dist next finish => bind_assoc dist next finish)
    (bind_pure_comp := fun f dist => bind_pure_comp f dist)

/-- Attach an explicit path cost to every outcome of a distribution. -/
abbrev sampleWithCost {M : CostModel.{uCost}} {α : Type uValue}
    (dist : PMF α) (cost : α → M.Cost) : RandCosted M α :=
  PMF.map (fun value => ⟨value, cost value⟩) dist

/-- Lift a distribution to an explicitly zero-cost randomized computation. -/
abbrev sampleZeroCost (M : CostModel.{uCost})
    {α : Type uValue} (dist : PMF α) : RandCosted M α := by
  letI := M.instAddMonoid
  exact sampleWithCost dist (fun _ => 0)

/-- Forget costs from a randomized costed computation. -/
abbrev valueDist {M : CostModel.{uCost}} {α : Type uValue}
    (dist : RandCosted M α) : PMF α :=
  PMF.map Costed.val dist

/-- Keep only costs from a randomized costed computation. -/
abbrev costDist {M : CostModel.{uCost}} {α : Type uValue}
    (dist : RandCosted M α) : PMF M.Cost :=
  PMF.map Costed.cost dist

@[simp] theorem valueDist_pure (M : CostModel.{uCost})
    {α : Type uValue} (value : α) :
    valueDist (pure M value) = PMF.pure value := by
  exact PMF.pure_map (f := Costed.val) (Costed.pure M value)

@[simp] theorem valueDist_liftCosted {M : CostModel.{uCost}}
    {α : Type uValue} (result : Costed M α) :
    valueDist (liftCosted result) = PMF.pure result.val := by
  exact PMF.pure_map (f := Costed.val) result

@[simp] theorem valueDist_map {M : CostModel.{uCost}}
    {α : Type uValue} {β : Type uMapped}
    (f : α → β) (dist : RandCosted M α) :
    valueDist (map f dist) = PMF.map f (valueDist dist) := by
  simp only [valueDist, map, PMF.map_comp]
  rfl

@[simp] theorem valueDist_bind {M : CostModel.{uCost}}
    {α : Type uValue} {β : Type uMapped}
    (dist : RandCosted M α) (next : α → RandCosted M β) :
    valueDist (bind dist next) =
      PMF.bind (valueDist dist) fun value => valueDist (next value) := by
  simp only [valueDist, bind, PMF.map_bind, PMF.map_comp, PMF.bind_map]
  rfl

@[simp] theorem valueDist_sampleWithCost {M : CostModel.{uCost}}
    {α : Type uValue} (dist : PMF α) (cost : α → M.Cost) :
    valueDist (sampleWithCost dist cost) = dist := by
  rw [valueDist, sampleWithCost, PMF.map_comp]
  simpa [Function.comp_def] using PMF.map_id dist

@[simp] theorem costDist_sampleWithCost {M : CostModel.{uCost}}
    {α : Type uValue} (dist : PMF α) (cost : α → M.Cost) :
    costDist (sampleWithCost dist cost) = PMF.map cost dist := by
  simp only [costDist, sampleWithCost, PMF.map_comp]
  rfl

@[simp] theorem valueDist_sampleZeroCost (M : CostModel.{uCost})
    {α : Type uValue} (dist : PMF α) :
    valueDist (sampleZeroCost M dist) = dist :=
  valueDist_sampleWithCost dist (fun _ => M.instAddMonoid.zero)

end

end RandCosted

end Crypto.Infrastructure.Computation.Cost

import Crypto.Infrastructure.Computation.Cost.Costed
import Mathlib.Probability.ProbabilityMassFunction.Constructions
import Mathlib.Probability.ProbabilityMassFunction.Monad

namespace Crypto.Infrastructure.Computation.Cost

universe uCost uValue uMapped

/-- A randomized computation whose paths carry costs from `M`. -/
def RandCostedT (M : CostModel.{uCost}) (α : Type uValue) := PMF (CostedT M α)

namespace RandCostedT

noncomputable section

/-- Lift one deterministic writer result to a point-mass randomized computation. -/
abbrev liftCosted {M : CostModel.{uCost}} {α : Type uValue}
    (result : CostedT M α) : RandCostedT M α :=
  PMF.pure result

/-- Return a value with zero path cost. -/
abbrev pure (M : CostModel.{uCost}) {α : Type uValue}
    (value : α) : RandCostedT M α :=
  liftCosted (CostedT.pure M value)

/-- Map a pure function over randomized results while preserving every path cost. -/
abbrev map {M : CostModel.{uCost}}
    {α : Type uValue} {β : Type uMapped}
    (f : α → β) (dist : RandCostedT M α) : RandCostedT M β :=
  PMF.map (CostedT.map f) dist

/--
Sequence randomized writer computations.

The continuation receives the ordinary value, and each resulting path records
the sequential composition of the first and second path costs exactly once.
-/
abbrev bind {M : CostModel.{uCost}}
    {α : Type uValue} {β : Type uMapped}
    (dist : RandCostedT M α) (next : α → RandCostedT M β) : RandCostedT M β :=
  PMF.bind dist fun first =>
    PMF.map
      (fun second : CostedT M β => first.bind fun _ => second)
      (next first.val)

noncomputable instance (M : CostModel.{uCost}) : Monad (RandCostedT M) where
  pure := fun value => RandCostedT.pure M value
  bind := fun dist next => RandCostedT.bind dist next
  map := fun f dist => RandCostedT.map f dist

/-- Randomized writer maps preserve identity. -/
@[simp] theorem map_id {M : CostModel.{uCost}}
    {α : Type uValue} (dist : RandCostedT M α) :
    map id dist = dist := by
  change
    PMF.map (fun result : CostedT M α => CostedT.map id result) dist = dist
  have mapIdentity :
      (fun result : CostedT M α => CostedT.map id result) = id := by
    funext result
    exact CostedT.map_id result
  rw [mapIdentity, PMF.map_id]

/-- Randomized writer maps compose without changing path costs. -/
theorem map_comp {M : CostModel.{uCost}}
    {α : Type uValue} {β γ : Type uMapped}
    (first : α → β) (second : β → γ) (dist : RandCostedT M α) :
    map second (map first dist) = map (second ∘ first) dist := by
  change
    PMF.map (CostedT.map second) (PMF.map (CostedT.map first) dist) =
      PMF.map (CostedT.map (second ∘ first)) dist
  rw [PMF.map_comp]
  apply congrArg (fun transform => PMF.map transform dist)
  funext result
  exact CostedT.map_comp first second result

/-- Randomized zero-cost pure is a left identity for writer sequencing. -/
@[simp] theorem pure_bind {M : CostModel.{uCost}}
    {α : Type uValue} {β : Type uMapped}
    (value : α) (next : α → RandCostedT M β) :
    bind (pure M value) next = next value := by
  change
    PMF.bind (PMF.pure (CostedT.pure M value))
        (fun firstResult =>
          PMF.map
            (fun nextResult => firstResult.bind fun _value => nextResult)
            (next firstResult.val)) =
      next value
  rw [PMF.pure_bind]
  have bindIdentity :
      (fun nextResult : CostedT M β =>
        (CostedT.pure M value).bind fun _value => nextResult) = id := by
    funext nextResult
    exact CostedT.pure_bind value (fun _value => nextResult)
  rw [bindIdentity, PMF.map_id]
  rfl

/-- Randomized zero-cost pure is a right identity for writer sequencing. -/
@[simp] theorem bind_pure {M : CostModel.{uCost}}
    {α : Type uValue} (dist : RandCostedT M α) :
    bind dist (fun value => pure M value) = dist := by
  change
    PMF.bind dist
        (fun firstResult =>
          PMF.map
            (fun nextResult => firstResult.bind fun _value => nextResult)
            (PMF.pure (CostedT.pure M firstResult.val))) =
      dist
  simp only [PMF.pure_map]
  have handlerIdentity :
      (fun firstResult : CostedT M α =>
        PMF.pure
          (firstResult.bind fun _value => CostedT.pure M firstResult.val)) =
        PMF.pure := by
    funext firstResult
    apply congrArg PMF.pure
    change firstResult.bind (CostedT.pure M) = firstResult
    exact CostedT.bind_pure firstResult
  rw [handlerIdentity, PMF.bind_pure]

/-- Randomized writer sequencing is associative in execution order. -/
theorem bind_assoc {M : CostModel.{uCost}}
    {α : Type uValue} {β γ : Type uMapped}
    (dist : RandCostedT M α) (next : α → RandCostedT M β)
    (finish : β → RandCostedT M γ) :
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
    CostedT.bind_assoc firstResult
      (fun _value => nextResult) (fun _value => finalResult)

/-- Binding a randomized writer into zero-cost pure is its value-only map. -/
theorem bind_pure_comp {M : CostModel.{uCost}}
    {α : Type uValue} {β : Type uMapped}
    (f : α → β) (dist : RandCostedT M α) :
    bind dist (fun value => pure M (f value)) = map f dist := by
  change
    PMF.bind dist
        (fun firstResult =>
          PMF.map
            (fun nextResult => firstResult.bind fun _value => nextResult)
            (PMF.pure (CostedT.pure M (f firstResult.val)))) =
      PMF.map (CostedT.map f) dist
  simp only [PMF.pure_map]
  have handlerEquality :
      (fun firstResult : CostedT M α =>
        PMF.pure
          (firstResult.bind fun _value => CostedT.pure M (f firstResult.val))) =
        (PMF.pure ∘ CostedT.map f) := by
    funext firstResult
    apply congrArg PMF.pure
    letI := M.instAddMonoid
    cases firstResult
    simp [CostedT.bind, CostedT.pure, CostedT.map]
  rw [handlerEquality]
  exact PMF.bind_pure_comp (CostedT.map f) dist

/-- `RandCostedT` is the lawful randomized writer monad. -/
noncomputable instance (M : CostModel.{uCost}) : LawfulMonad (RandCostedT M) :=
  LawfulMonad.mk'
    (id_map := fun dist => map_id dist)
    (pure_bind := fun value next => pure_bind value next)
    (bind_assoc := fun dist next finish => bind_assoc dist next finish)
    (bind_pure_comp := fun f dist => bind_pure_comp f dist)

/-- Attach an explicit path cost to every outcome of a distribution. -/
abbrev sampleWithCost {M : CostModel.{uCost}} {α : Type uValue}
    (dist : PMF α) (cost : α → M.Cost) : RandCostedT M α :=
  PMF.map (fun value => ⟨value, cost value⟩) dist

/-- Lift a distribution to an explicitly zero-cost randomized computation. -/
abbrev sampleZeroCost (M : CostModel.{uCost})
    {α : Type uValue} (dist : PMF α) : RandCostedT M α := by
  letI := M.instAddMonoid
  exact sampleWithCost dist (fun _ => 0)

/-- Forget costs from a randomized costed computation. -/
abbrev valueDist {M : CostModel.{uCost}} {α : Type uValue}
    (dist : RandCostedT M α) : PMF α :=
  PMF.map CostedT.val dist

/-- Keep only costs from a randomized costed computation. -/
abbrev costDist {M : CostModel.{uCost}} {α : Type uValue}
    (dist : RandCostedT M α) : PMF M.Cost :=
  PMF.map CostedT.cost dist

@[simp] theorem valueDist_pure (M : CostModel.{uCost})
    {α : Type uValue} (value : α) :
    valueDist (pure M value) = PMF.pure value := by
  exact PMF.pure_map (f := CostedT.val) (CostedT.pure M value)

@[simp] theorem valueDist_liftCosted {M : CostModel.{uCost}}
    {α : Type uValue} (result : CostedT M α) :
    valueDist (liftCosted result) = PMF.pure result.val := by
  exact PMF.pure_map (f := CostedT.val) result

@[simp] theorem valueDist_map {M : CostModel.{uCost}}
    {α : Type uValue} {β : Type uMapped}
    (f : α → β) (dist : RandCostedT M α) :
    valueDist (map f dist) = PMF.map f (valueDist dist) := by
  simp only [valueDist, map, PMF.map_comp]
  rfl

@[simp] theorem valueDist_bind {M : CostModel.{uCost}}
    {α : Type uValue} {β : Type uMapped}
    (dist : RandCostedT M α) (next : α → RandCostedT M β) :
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

/--
Uniform path bounds compose through randomized writer bind.

This theorem uses only the sequential monoid and its two monotonicity laws; it
does not project the exact cost to `Nat`.
-/
theorem bind_cost_le {M : CostModel.{uCost}}
    {α : Type uValue} {β : Type uMapped}
    (first : RandCostedT M α) (next : α → RandCostedT M β)
    (firstBudget nextBudget : M.Cost)
    (first_cost_le :
      ∀ firstResult, firstResult ∈ first.support →
        M.instPartialOrder.le firstResult.cost firstBudget)
    (next_cost_le :
      ∀ value nextResult, nextResult ∈ (next value).support →
        M.instPartialOrder.le nextResult.cost nextBudget) :
    ∀ result, result ∈ (bind first next).support →
      M.instPartialOrder.le result.cost
        (M.instAddMonoid.add firstBudget nextBudget) := by
  letI := M.instAddMonoid
  letI := M.instPartialOrder
  letI := M.instAddLeftMono
  letI := M.instAddRightMono
  intro result hresult
  simp only [bind] at hresult
  rw [PMF.mem_support_bind_iff] at hresult
  rcases hresult with ⟨firstResult, hfirstResult, hnextResult⟩
  rw [PMF.mem_support_map_iff] at hnextResult
  rcases hnextResult with ⟨nextResult, hnextResult, hresult⟩
  subst result
  exact add_le_add
    (first_cost_le firstResult hfirstResult)
    (next_cost_le firstResult.val nextResult hnextResult)

end

end RandCostedT

end Crypto.Infrastructure.Computation.Cost

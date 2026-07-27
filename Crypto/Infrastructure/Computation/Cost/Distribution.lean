import Crypto.Infrastructure.Computation.Cost.Costed
import Mathlib.Probability.ProbabilityMassFunction.Constructions
import Mathlib.Probability.ProbabilityMassFunction.Monad

namespace Crypto.Infrastructure.Computation.Cost

universe uValue uMapped

/-- A randomized computation whose paths carry accumulated costs. -/
def RandCosted (α : Type uValue) := PMF (Costed α)

namespace RandCosted

/-- Lift one deterministic writer result to a point-mass randomized computation. -/
noncomputable def liftCosted {α : Type uValue} (result : Costed α) : RandCosted α :=
  PMF.pure result

/-- Return a value with zero path cost. -/
noncomputable def pure {α : Type uValue} (value : α) : RandCosted α :=
  liftCosted (Costed.pure value)

/-- Map a pure function over randomized results while preserving every path cost. -/
noncomputable def map {α : Type uValue} {β : Type uMapped}
    (f : α → β) (dist : RandCosted α) : RandCosted β :=
  PMF.map (Costed.map f) dist

/--
Sequence randomized writer computations.

The continuation receives the ordinary value, and each resulting path records
the sum of the first and second path costs.
-/
noncomputable def bind {α : Type uValue} {β : Type uMapped}
    (dist : RandCosted α) (next : α → RandCosted β) : RandCosted β :=
  PMF.bind dist fun first =>
    PMF.map
      (fun second : Costed β => first.bind fun _ => second)
      (next first.val)

noncomputable instance : Monad RandCosted where
  pure := fun value => RandCosted.pure value
  bind := fun dist next => RandCosted.bind dist next
  map := fun f dist => RandCosted.map f dist

/-- Attach an explicit path cost to every outcome of a distribution. -/
noncomputable def sampleWithCost {α : Type uValue}
    (dist : PMF α) (cost : α → Cost) : RandCosted α :=
  PMF.map (fun value => ⟨value, cost value⟩) dist

/--
Lift a distribution over values to an explicitly zero-cost randomized computation.

Use this only when sampling is intentionally outside the measured cost model.
-/
noncomputable def sampleZeroCost {α : Type uValue} (dist : PMF α) : RandCosted α :=
  sampleWithCost dist (fun _ => 0)

/-- Forget costs from a randomized costed computation. -/
noncomputable def valueDist {α : Type uValue} (dist : RandCosted α) : PMF α :=
  PMF.map Costed.val dist

/-- Keep only costs from a randomized costed computation. -/
noncomputable def costDist {α : Type uValue} (dist : RandCosted α) : PMF Cost :=
  PMF.map Costed.cost dist

@[simp] theorem valueDist_pure {α : Type uValue} (value : α) :
    valueDist (pure value) = PMF.pure value := by
  exact PMF.pure_map (f := Costed.val) (Costed.pure value)

@[simp] theorem valueDist_liftCosted {α : Type uValue} (result : Costed α) :
    valueDist (liftCosted result) = PMF.pure result.val := by
  exact PMF.pure_map (f := Costed.val) result

@[simp] theorem valueDist_map {α : Type uValue} {β : Type uMapped}
    (f : α → β) (dist : RandCosted α) :
    valueDist (map f dist) = PMF.map f (valueDist dist) := by
  simp only [valueDist, map, PMF.map_comp]
  rfl

@[simp] theorem valueDist_bind {α : Type uValue} {β : Type uMapped}
    (dist : RandCosted α) (next : α → RandCosted β) :
    valueDist (bind dist next) =
      PMF.bind (valueDist dist) fun value => valueDist (next value) := by
  simp only [valueDist, bind, PMF.map_bind, PMF.map_comp, PMF.bind_map]
  rfl

@[simp] theorem valueDist_sampleWithCost {α : Type uValue}
    (dist : PMF α) (cost : α → Cost) :
    valueDist (sampleWithCost dist cost) = dist := by
  rw [valueDist, sampleWithCost, PMF.map_comp]
  simpa [Function.comp_def] using PMF.map_id dist

@[simp] theorem costDist_sampleWithCost {α : Type uValue}
    (dist : PMF α) (cost : α → Cost) :
    costDist (sampleWithCost dist cost) = PMF.map cost dist := by
  simp only [costDist, sampleWithCost, PMF.map_comp]
  rfl

@[simp] theorem valueDist_sampleZeroCost {α : Type uValue} (dist : PMF α) :
    valueDist (sampleZeroCost dist) = dist :=
  valueDist_sampleWithCost dist (fun _ => 0)

end RandCosted

end Crypto.Infrastructure.Computation.Cost

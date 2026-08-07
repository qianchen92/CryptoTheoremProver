import CryptoLib.Core.Infrastructure.Computation.Cost.Measure
import CryptoLib.Core.Infrastructure.Computation.Cost.PathBound

namespace CryptoLib.Core.Infrastructure.Computation.Cost

universe uCost uValue uMapped

namespace Costed

variable
    {M : CostModel.{uCost}} (measure : NatMeasure M)
    {α : Type uValue} {β : Type uMapped}

/-- Project an exact costed result to the natural-number cost model. -/
def mapCost (result : Costed M α) : Costed CostModel.nat α :=
  ⟨result.val, measure result.cost⟩

@[simp] theorem mapCost_val (result : Costed M α) :
    (mapCost measure result).val = result.val :=
  rfl

@[simp] theorem mapCost_cost (result : Costed M α) :
    (mapCost measure result).cost = measure result.cost :=
  rfl

/-- Projecting an already natural-number-valued cost through the identity measure is inert. -/
@[simp] theorem mapCost_nat {α : Type uValue}
    (result : Costed CostModel.nat α) :
    mapCost NatMeasure.nat result = result := by
  cases result
  rfl

@[simp] theorem mapCost_pure (value : α) :
    mapCost measure (pure M value) = Costed.pure CostModel.nat value := by
  change
    (⟨value, measure M.instAddMonoid.zero⟩ : Costed CostModel.nat α) =
      (⟨value, 0⟩ : Costed CostModel.nat α)
  rw [measure.map_zero]

/-- Cost projection commutes with value-only maps. -/
@[simp] theorem mapCost_map
    (f : α → β) (result : Costed M α) :
    mapCost measure (result.map f) = (mapCost measure result).map f := by
  cases result
  rfl

@[simp] theorem mapCost_bind
    (result : Costed M α) (next : α → Costed M β) :
    mapCost measure (result.bind next) =
      (mapCost measure result).bind fun value => mapCost measure (next value) := by
  change
    (⟨(next result.val).val,
        measure (M.instAddMonoid.add result.cost (next result.val).cost)⟩ :
          Costed CostModel.nat β) =
      (⟨(next result.val).val,
        measure result.cost + measure (next result.val).cost⟩ :
          Costed CostModel.nat β)
  rw [measure.map_add]

end Costed

namespace RandCosted

variable
    {M : CostModel.{uCost}} (measure : NatMeasure M)
    {α : Type uValue} {β : Type uMapped}

/-- Project every exact path cost to natural-number runtime. -/
noncomputable def mapCost (dist : RandCosted M α) :
    RandCosted CostModel.nat α :=
  PMF.map (Costed.mapCost measure) dist

/-- Identity cost projection leaves a natural-number randomized writer unchanged. -/
@[simp] theorem mapCost_nat {α : Type uValue}
    (dist : RandCosted CostModel.nat α) :
    mapCost NatMeasure.nat dist = dist := by
  change PMF.map (Costed.mapCost NatMeasure.nat) dist = dist
  have mapIdentity :
      (Costed.mapCost NatMeasure.nat :
        Costed CostModel.nat α → Costed CostModel.nat α) = id := by
    funext result
    exact Costed.mapCost_nat result
  rw [mapIdentity, PMF.map_id]

/-- Cost projection commutes with lifting an exact writer result. -/
@[simp] theorem mapCost_liftCosted (result : Costed M α) :
    mapCost measure (liftCosted result) =
      liftCosted (Costed.mapCost measure result) := by
  exact PMF.pure_map (f := Costed.mapCost measure) result

/-- Cost projection commutes with randomized pure. -/
@[simp] theorem mapCost_pure (value : α) :
    mapCost measure (pure M value) =
      RandCosted.pure CostModel.nat value := by
  change
    PMF.map (Costed.mapCost measure) (PMF.pure (Costed.pure M value)) =
      PMF.pure (Costed.pure CostModel.nat value)
  rw [PMF.pure_map, Costed.mapCost_pure]

/-- Cost projection commutes with value-only maps. -/
@[simp] theorem mapCost_map
    (f : α → β) (dist : RandCosted M α) :
    mapCost measure (map f dist) =
      RandCosted.map f (mapCost measure dist) := by
  simp only [mapCost, map, PMF.map_comp]
  rfl

/-- Cost projection is a writer-monad morphism for randomized sequencing. -/
@[simp] theorem mapCost_bind (dist : RandCosted M α)
    (next : α → RandCosted M β) :
    mapCost measure (bind dist next) =
      RandCosted.bind (mapCost measure dist)
        (fun value => mapCost measure (next value)) := by
  change
    PMF.map (Costed.mapCost measure)
        (PMF.bind dist fun firstResult =>
          PMF.map
            (fun nextResult => firstResult.bind fun _value => nextResult)
            (next firstResult.val)) =
      PMF.bind (PMF.map (Costed.mapCost measure) dist) fun firstResult =>
        PMF.map
          (fun nextResult => firstResult.bind fun _value => nextResult)
          (PMF.map (Costed.mapCost measure) (next firstResult.val))
  rw [PMF.map_bind, PMF.bind_map]
  apply congrArg (PMF.bind dist)
  funext firstResult
  dsimp only [Function.comp_apply]
  rw [PMF.map_comp, PMF.map_comp]
  apply congrArg (fun transform => PMF.map transform (next firstResult.val))
  funext nextResult
  exact Costed.mapCost_bind measure firstResult (fun _value => nextResult)

/-- Explicit value-dependent costs are projected pointwise. -/
@[simp] theorem mapCost_sampleWithCost
    (dist : PMF α) (cost : α → M.Cost) :
    mapCost measure (sampleWithCost dist cost) =
      sampleWithCost dist (fun value => measure (cost value)) := by
  simp only [mapCost, sampleWithCost, PMF.map_comp]
  rfl

/-- Projecting costs does not alter the ordinary value distribution. -/
@[simp] theorem valueDist_mapCost (dist : RandCosted M α) :
    RandCosted.valueDist (mapCost measure dist) = valueDist dist := by
  simp only [mapCost, valueDist, PMF.map_comp]
  rfl

/-- The projected cost distribution is the image under the chosen measure. -/
@[simp] theorem costDist_mapCost (dist : RandCosted M α) :
    RandCosted.costDist (mapCost measure dist) = PMF.map measure (costDist dist) := by
  simp only [mapCost, costDist, PMF.map_comp]
  rfl

namespace CostBound

/-- A monotone natural-number observation preserves every exact path bound. -/
theorem mapCost
    {dist : RandCosted M α} {budget : M.Cost}
    (bound : RandCosted.CostBound dist budget) :
    RandCosted.CostBound
      (RandCosted.mapCost measure dist) (measure budget) := by
  intro result hresult
  simp only [RandCosted.mapCost] at hresult
  rw [PMF.mem_support_map_iff] at hresult
  rcases hresult with ⟨exactResult, hexactResult, hresult⟩
  subst result
  exact measure.monotone_toNat (bound exactResult hexactResult)

end CostBound

end RandCosted

end CryptoLib.Core.Infrastructure.Computation.Cost

import Crypto.Infrastructure.Computation.Cost.Distribution

namespace Crypto.Infrastructure.Computation.Cost

universe uCost uValue

section NatMeasureDefinition

variable (M : CostModel.{uCost})

local instance : AddMonoid M.Cost := M.instAddMonoid
local instance : PartialOrder M.Cost := M.instPartialOrder

/--
An additive, monotone observation of an exact cost model as natural-number
runtime. This is the explicit boundary between exact resource semantics and
`Nat`-based complexity.
-/
structure NatMeasure where
  toNat : M.Cost →+ Nat
  monotone_toNat : Monotone toNat

end NatMeasureDefinition

namespace NatMeasure

variable {M : CostModel.{uCost}}

instance : CoeFun (NatMeasure M) (fun _ => M.Cost → Nat) where
  coe measure := measure.toNat

@[simp] theorem map_zero (measure : NatMeasure M) :
    measure M.instAddMonoid.zero = 0 :=
  by
    letI := M.instAddMonoid
    exact measure.toNat.map_zero

@[simp] theorem map_add (measure : NatMeasure M) (left right : M.Cost) :
    measure (M.instAddMonoid.add left right) = measure left + measure right :=
  by
    letI := M.instAddMonoid
    exact measure.toNat.map_add left right

/-- The identity observation for the natural-number cost model. -/
def nat : NatMeasure CostModel.nat where
  toNat :=
    { toFun := id
      map_zero' := rfl
      map_add' := by
        intro _ _
        rfl }
  monotone_toNat := monotone_id

end NatMeasure

namespace CostedT

/-- Project an exact costed result to the natural-number cost model. -/
def mapCost {M : CostModel.{uCost}} (measure : NatMeasure M)
    {α : Type uValue} (result : CostedT M α) : CostedT CostModel.nat α :=
  ⟨result.val, measure result.cost⟩

@[simp] theorem mapCost_val {M : CostModel.{uCost}} (measure : NatMeasure M)
    {α : Type uValue} (result : CostedT M α) :
    (mapCost measure result).val = result.val :=
  rfl

@[simp] theorem mapCost_cost {M : CostModel.{uCost}} (measure : NatMeasure M)
    {α : Type uValue} (result : CostedT M α) :
    (mapCost measure result).cost = measure result.cost :=
  rfl

@[simp] theorem mapCost_pure {M : CostModel.{uCost}} (measure : NatMeasure M)
    {α : Type uValue} (value : α) :
    mapCost measure (pure M value) = CostedT.pure CostModel.nat value := by
  change
    (⟨value, measure M.instAddMonoid.zero⟩ : CostedT CostModel.nat α) =
      (⟨value, 0⟩ : CostedT CostModel.nat α)
  rw [measure.map_zero]

@[simp] theorem mapCost_bind {M : CostModel.{uCost}} (measure : NatMeasure M)
    {α β : Type uValue} (result : CostedT M α) (next : α → CostedT M β) :
    mapCost measure (result.bind next) =
      (mapCost measure result).bind fun value => mapCost measure (next value) := by
  change
    (⟨(next result.val).val,
        measure (M.instAddMonoid.add result.cost (next result.val).cost)⟩ :
          CostedT CostModel.nat β) =
      (⟨(next result.val).val,
        measure result.cost + measure (next result.val).cost⟩ :
          CostedT CostModel.nat β)
  rw [measure.map_add]

end CostedT

namespace RandCostedT

/-- Project every exact path cost to natural-number runtime. -/
noncomputable def mapCost {M : CostModel.{uCost}} (measure : NatMeasure M)
    {α : Type uValue} (dist : RandCostedT M α) :
    RandCostedT CostModel.nat α :=
  PMF.map (CostedT.mapCost measure) dist

/-- Cost projection commutes with randomized pure. -/
@[simp] theorem mapCost_pure {M : CostModel.{uCost}} (measure : NatMeasure M)
    {α : Type uValue} (value : α) :
    mapCost measure (pure M value) =
      RandCostedT.pure CostModel.nat value := by
  change
    PMF.map (CostedT.mapCost measure) (PMF.pure (CostedT.pure M value)) =
      PMF.pure (CostedT.pure CostModel.nat value)
  rw [PMF.pure_map, CostedT.mapCost_pure]

/-- Cost projection commutes with value-only maps. -/
@[simp] theorem mapCost_map {M : CostModel.{uCost}} (measure : NatMeasure M)
    {α β : Type uValue} (f : α → β) (dist : RandCostedT M α) :
    mapCost measure (map f dist) =
      RandCostedT.map f (mapCost measure dist) := by
  simp only [mapCost, map, PMF.map_comp]
  rfl

/-- Cost projection is a writer-monad morphism for randomized sequencing. -/
@[simp] theorem mapCost_bind {M : CostModel.{uCost}} (measure : NatMeasure M)
    {α β : Type uValue} (dist : RandCostedT M α)
    (next : α → RandCostedT M β) :
    mapCost measure (bind dist next) =
      RandCostedT.bind (mapCost measure dist)
        (fun value => mapCost measure (next value)) := by
  change
    PMF.map (CostedT.mapCost measure)
        (PMF.bind dist fun firstResult =>
          PMF.map
            (fun nextResult => firstResult.bind fun _value => nextResult)
            (next firstResult.val)) =
      PMF.bind (PMF.map (CostedT.mapCost measure) dist) fun firstResult =>
        PMF.map
          (fun nextResult => firstResult.bind fun _value => nextResult)
          (PMF.map (CostedT.mapCost measure) (next firstResult.val))
  rw [PMF.map_bind, PMF.bind_map]
  apply congrArg (PMF.bind dist)
  funext firstResult
  dsimp only [Function.comp_apply]
  rw [PMF.map_comp, PMF.map_comp]
  apply congrArg (fun transform => PMF.map transform (next firstResult.val))
  funext nextResult
  exact CostedT.mapCost_bind measure firstResult (fun _value => nextResult)

/-- Projecting costs does not alter the ordinary value distribution. -/
@[simp] theorem valueDist_mapCost {M : CostModel.{uCost}} (measure : NatMeasure M)
    {α : Type uValue} (dist : RandCostedT M α) :
    RandCostedT.valueDist (mapCost measure dist) = valueDist dist := by
  simp only [mapCost, valueDist, PMF.map_comp]
  rfl

/-- The projected cost distribution is the image under the chosen measure. -/
@[simp] theorem costDist_mapCost {M : CostModel.{uCost}} (measure : NatMeasure M)
    {α : Type uValue} (dist : RandCostedT M α) :
    RandCostedT.costDist (mapCost measure dist) = PMF.map measure (costDist dist) := by
  simp only [mapCost, costDist, PMF.map_comp]
  rfl

end RandCostedT

end Crypto.Infrastructure.Computation.Cost

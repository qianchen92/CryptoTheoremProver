import Crypto.Infrastructure.Computation.Cost.Model
import Mathlib.Algebra.Group.Hom.Defs

namespace Crypto.Infrastructure.Computation.Cost

universe uCost

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

local instance : AddMonoid M.Cost := M.instAddMonoid

instance : CoeFun (NatMeasure M) (fun _ => M.Cost → Nat) where
  coe measure := measure.toNat

@[simp] theorem map_zero (measure : NatMeasure M) :
    measure M.instAddMonoid.zero = 0 := by
  exact measure.toNat.map_zero

@[simp] theorem map_add (measure : NatMeasure M) (left right : M.Cost) :
    measure (M.instAddMonoid.add left right) = measure left + measure right := by
  exact measure.toNat.map_add left right

/-- Additive observation commutes with finite sequential repetition. -/
@[simp] theorem map_nsmul (measure : NatMeasure M)
    (count : Nat) (cost : M.Cost) :
    measure (count • cost) = count • measure cost := by
  exact measure.toNat.map_nsmul cost count

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

end Crypto.Infrastructure.Computation.Cost

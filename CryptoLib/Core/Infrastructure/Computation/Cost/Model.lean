import Mathlib.Algebra.Order.Group.Nat

namespace CryptoLib.Core.Infrastructure.Computation.Cost

universe uCost

/--
A compositional model of exact execution resources.

Sequential execution is described by an additive monoid.  The order is used
only for bounds; exact interpreters do not discard information by projecting to
`Nat`.
-/
structure CostModel where
  Cost : Type uCost
  instAddMonoid : AddMonoid Cost
  instPartialOrder : PartialOrder Cost
  instAddLeftMono : @AddLeftMono Cost instAddMonoid.toAdd instPartialOrder.toLE
  instAddRightMono : @AddRightMono Cost instAddMonoid.toAdd instPartialOrder.toLE

namespace CostModel

/-- The ordinary natural-number step-count model. -/
abbrev nat : CostModel where
  Cost := Nat
  instAddMonoid := inferInstance
  instPartialOrder := inferInstance
  instAddLeftMono := inferInstance
  instAddRightMono := inferInstance

end CostModel

/--
A cost model equipped with a least common upper bound in its existing order.

The operation and its three order laws are stored directly against
`CostModel.instPartialOrder`.  In particular, this capability does not carry a
second `PartialOrder` whose coherence with the exact-cost order would need to
be proved separately.
-/
structure WorstCaseCostModel extends CostModel where
  sup : Cost → Cost → Cost
  le_sup_left : ∀ left right,
    instPartialOrder.le left (sup left right)
  le_sup_right : ∀ left right,
    instPartialOrder.le right (sup left right)
  sup_le : ∀ left right upper,
    instPartialOrder.le left upper →
    instPartialOrder.le right upper →
    instPartialOrder.le (sup left right) upper

namespace WorstCaseCostModel

/-- The natural-number model with `max` as its worst-case combination. -/
def nat : WorstCaseCostModel where
  toCostModel := CostModel.nat
  sup := max
  le_sup_left := Nat.le_max_left
  le_sup_right := Nat.le_max_right
  sup_le := fun _left _right _upper left_le right_le =>
    Nat.max_le.mpr ⟨left_le, right_le⟩

end WorstCaseCostModel

end CryptoLib.Core.Infrastructure.Computation.Cost

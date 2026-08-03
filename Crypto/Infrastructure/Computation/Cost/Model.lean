import Mathlib.Algebra.Order.Group.Nat

namespace Crypto.Infrastructure.Computation.Cost

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
A cost model equipped with a least common upper bound, used for deriving
branching bounds automatically.

The semilattice order must agree with the order in `toCostModel`.  Keeping the
capability separate means straight-line exact interpreters require only a
`CostModel`.
-/
structure WorstCaseCostModel extends CostModel where
  instSemilatticeSup : SemilatticeSup Cost
  partialOrder_eq : instSemilatticeSup.toPartialOrder = instPartialOrder

namespace WorstCaseCostModel

/-- The natural-number model with `max` as its worst-case combination. -/
def nat : WorstCaseCostModel where
  toCostModel := CostModel.nat
  instSemilatticeSup := (inferInstance : SemilatticeSup Nat)
  partialOrder_eq := rfl

end WorstCaseCostModel

end Crypto.Infrastructure.Computation.Cost

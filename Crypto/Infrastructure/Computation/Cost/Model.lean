import Mathlib.Algebra.Order.Group.Nat

namespace Crypto.Infrastructure.Computation.Cost

universe uCost uValue uScalar

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

/-- Public name for the natural-number compatibility cost model. -/
abbrev natCostModel : CostModel := CostModel.nat

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
  toCostModel := natCostModel
  instSemilatticeSup := (inferInstance : SemilatticeSup Nat)
  partialOrder_eq := rfl

end WorstCaseCostModel

set_option linter.dupNamespace false

/-- Operation cost in the backwards-compatible natural-number model. -/
abbrev Cost := natCostModel.Cost

set_option linter.dupNamespace true

/-- Cost model for addition on a type. -/
class AddCost (α : Type uValue) where
  addCost : α → α → Cost

/-- Cost model for multiplication on a type. -/
class MulCost (α : Type uValue) where
  mulCost : α → α → Cost

/-- Cost model for negation on a type. -/
class NegCost (α : Type uValue) where
  negCost : α → Cost

/-- Cost model for subtraction on a type. -/
class SubCost (α : Type uValue) where
  subCost : α → α → Cost

/-- Cost model for scalar multiplication from `R` into `α`. -/
class SMulCost (R : Type uScalar) (α : Type uValue) where
  smulCost : R → α → Cost

end Crypto.Infrastructure.Computation.Cost

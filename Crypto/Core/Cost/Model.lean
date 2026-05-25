namespace Crypto.Core.Cost

universe uValue uScalar

/-- Operation cost is represented as a natural-number step count. -/
abbrev Cost := Nat

/-- Cost model for addition on a type. -/
class AddCost (α : Type uValue) where
  addCost : Cost

/-- Cost model for multiplication on a type. -/
class MulCost (α : Type uValue) where
  mulCost : Cost

/-- Cost model for negation on a type. -/
class NegCost (α : Type uValue) where
  negCost : Cost

/-- Cost model for subtraction on a type. -/
class SubCost (α : Type uValue) where
  subCost : Cost

/-- Cost model for scalar multiplication from `R` into `α`. -/
class SMulCost (R : Type uScalar) (α : Type uValue) where
  smulCost : R → Cost

end Crypto.Core.Cost

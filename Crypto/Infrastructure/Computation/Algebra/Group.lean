import Crypto.Infrastructure.Computation.Cost.Model
import Mathlib.Algebra.Group.Defs
import Mathlib.Data.Fintype.Basic

namespace Crypto.Infrastructure.Computation.Algebra.Group

open Crypto.Infrastructure.Computation.Cost

universe uGroup

/-- A public description of a finite nonempty additive group. -/
structure AdditiveGroupParam where
  Carrier : Type uGroup
  addGroup : AddGroup Carrier
  fintype : Fintype Carrier
  nonempty : Nonempty Carrier

attribute [instance] AdditiveGroupParam.addGroup
attribute [instance] AdditiveGroupParam.fintype
attribute [instance] AdditiveGroupParam.nonempty

/--
One abstract algebraic-operation unit.

This is an operation-count model, not a claim about Lean host evaluation.
-/
def unitOperationCost : Cost :=
  1

/--
Cost of computing `k • value` by starting from zero and performing `k`
additions.  This deliberately conservative linear model does not describe Lean
host runtime or a faster addition-chain implementation.
-/
def linearRepeatedAddCost (k : Nat) : Cost :=
  k

/-- Explicit unit-operation model for addition in an additive group. -/
def unitAddCostModel (G : Type uGroup) [AddGroup G] :
    AddCost G where
  addCost := fun _ _ => unitOperationCost

/-- Explicit unit-operation model for subtraction in an additive group. -/
def unitSubCostModel (G : Type uGroup) [AddGroup G] :
    SubCost G where
  subCost := fun _ _ => unitOperationCost

/-- Explicit unit-operation model for negation in an additive group. -/
def unitNegCostModel (G : Type uGroup) [AddGroup G] :
    NegCost G where
  negCost := fun _ => unitOperationCost

/-- Explicit linear repeated-addition model for natural scalar multiplication. -/
def linearNatSMulCostModel (G : Type uGroup) [AddGroup G] :
    SMulCost Nat G where
  smulCost := fun k _ => linearRepeatedAddCost k

/--
The explicit operation-count models commonly selected together for an
additive group.

No field is installed globally.  A caller may select the fields locally with
`letI` before invoking `AdditiveBackend.ofCostModel`.
-/
structure ExplicitCostModel (G : Type uGroup) [AddGroup G] where
  add : AddCost G
  sub : SubCost G
  neg : NegCost G
  natSMul : SMulCost Nat G

/--
Unit-cost addition, subtraction, and negation together with linear natural
scalar multiplication.
-/
def unitLinearCostModel (G : Type uGroup) [AddGroup G] :
    ExplicitCostModel G where
  add := unitAddCostModel G
  sub := unitSubCostModel G
  neg := unitNegCostModel G
  natSMul := linearNatSMulCostModel G

end Crypto.Infrastructure.Computation.Algebra.Group

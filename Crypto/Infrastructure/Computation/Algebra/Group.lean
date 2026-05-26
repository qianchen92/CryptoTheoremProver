import Crypto.Infrastructure.Computation.Cost.Model
import Mathlib.Algebra.Group.Defs
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Nat.Log

namespace Crypto.Infrastructure.Computation.Algebra.Group

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

/-- Unit cost for a group operation. -/
def opCost : Crypto.Infrastructure.Computation.Cost.Cost :=
  1

/-- Cost model for repeated additive scalar multiplication by a natural number. -/
def nsmulCost (k : Nat) : Crypto.Infrastructure.Computation.Cost.Cost :=
  Nat.clog 2 k

instance (priority := 100) instAddCostOfAddGroup (G : Type uGroup) [AddGroup G] :
    Crypto.Infrastructure.Computation.Cost.AddCost G where
  addCost := opCost

instance (priority := 100) instSubCostOfAddGroup (G : Type uGroup) [AddGroup G] :
    Crypto.Infrastructure.Computation.Cost.SubCost G where
  subCost := opCost

instance (priority := 100) instNegCostOfAddGroup (G : Type uGroup) [AddGroup G] :
    Crypto.Infrastructure.Computation.Cost.NegCost G where
  negCost := 0

instance (priority := 100) instNatSMulCostOfAddGroup (G : Type uGroup) [AddGroup G] :
    Crypto.Infrastructure.Computation.Cost.SMulCost Nat G where
  smulCost := nsmulCost

end Crypto.Infrastructure.Computation.Algebra.Group

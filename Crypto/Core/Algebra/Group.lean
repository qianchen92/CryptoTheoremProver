import Crypto.Core.Cost.Model
import Mathlib.Algebra.Group.Defs
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Nat.Log

namespace Crypto.Core.Algebra.Group

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
def opCost : Crypto.Core.Cost.Cost :=
  1

/-- Cost model for repeated additive scalar multiplication by a natural number. -/
def nsmulCost (k : Nat) : Crypto.Core.Cost.Cost :=
  Nat.clog 2 k

instance (priority := 100) instAddCostOfAddGroup (G : Type uGroup) [AddGroup G] :
    Crypto.Core.Cost.AddCost G where
  addCost := opCost

instance (priority := 100) instSubCostOfAddGroup (G : Type uGroup) [AddGroup G] :
    Crypto.Core.Cost.SubCost G where
  subCost := opCost

instance (priority := 100) instNegCostOfAddGroup (G : Type uGroup) [AddGroup G] :
    Crypto.Core.Cost.NegCost G where
  negCost := 0

instance (priority := 100) instNatSMulCostOfAddGroup (G : Type uGroup) [AddGroup G] :
    Crypto.Core.Cost.SMulCost Nat G where
  smulCost := nsmulCost

end Crypto.Core.Algebra.Group

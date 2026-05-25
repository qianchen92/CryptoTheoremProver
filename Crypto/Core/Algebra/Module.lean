import Crypto.Core.Cost.Model
import Mathlib.Algebra.Module.Defs

namespace Crypto.Core.Algebra.Module

universe uScalar uModule

/-- Default unit cost for a scalar multiplication when no sharper model is provided. -/
def unitSMulCost {R : Type uScalar} (_ : R) : Crypto.Core.Cost.Cost :=
  1

instance (priority := 50) instSMulCostOfModule
    (R : Type uScalar) (M : Type uModule) [Semiring R] [AddCommMonoid M] [Module R M] :
    Crypto.Core.Cost.SMulCost R M where
  smulCost := unitSMulCost

end Crypto.Core.Algebra.Module

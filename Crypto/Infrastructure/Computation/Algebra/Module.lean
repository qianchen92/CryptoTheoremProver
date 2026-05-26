import Crypto.Infrastructure.Computation.Cost.Model
import Mathlib.Algebra.Module.Defs

namespace Crypto.Infrastructure.Computation.Algebra.Module

universe uScalar uModule

/-- Default unit cost for a scalar multiplication when no sharper model is provided. -/
def unitSMulCost {R : Type uScalar} (_ : R) : Crypto.Infrastructure.Computation.Cost.Cost :=
  1

instance (priority := 50) instSMulCostOfModule
    (R : Type uScalar) (M : Type uModule) [Semiring R] [AddCommMonoid M] [Module R M] :
    Crypto.Infrastructure.Computation.Cost.SMulCost R M where
  smulCost := unitSMulCost

end Crypto.Infrastructure.Computation.Algebra.Module

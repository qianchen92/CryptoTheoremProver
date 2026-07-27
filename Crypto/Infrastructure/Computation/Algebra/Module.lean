import Crypto.Infrastructure.Computation.Cost.Model
import Mathlib.Algebra.Module.Defs

namespace Crypto.Infrastructure.Computation.Algebra.Module

open Crypto.Infrastructure.Computation.Cost

universe uScalar uModule

/--
An explicit constant-cost model for scalar multiplication in a module.

The caller chooses this model locally; it is not installed as a global
typeclass instance.
-/
def constantSMulCostModel
    (R : Type uScalar) (M : Type uModule) [Semiring R] [AddCommMonoid M] [Module R M]
    (cost : Cost) :
    SMulCost R M where
  smulCost := fun _ _ => cost

/-- Explicit unit-operation model for scalar multiplication in a module. -/
def unitSMulCostModel
    (R : Type uScalar) (M : Type uModule) [Semiring R] [AddCommMonoid M] [Module R M] :
    SMulCost R M :=
  constantSMulCostModel R M 1

end Crypto.Infrastructure.Computation.Algebra.Module

import Mathlib.Algebra.Group.Defs
import Mathlib.Data.Fintype.Basic

namespace Crypto.Infrastructure.Computation.Algebra.Parameter

universe uGroup

/-- A public description of a finite additive group. -/
structure AdditiveGroupParam where
  Carrier : Type uGroup
  addGroup : AddGroup Carrier
  fintypeCarrier : Fintype Carrier

end Crypto.Infrastructure.Computation.Algebra.Parameter

/-
Scoped projections for additive-group parameters. Activating this scope is an
explicit choice, so parameter projections cannot form global instance diamonds
with concrete carrier instances.
-/
namespace AdditiveGroupParam

scoped instance
    (param : Crypto.Infrastructure.Computation.Algebra.Parameter.AdditiveGroupParam) :
    AddGroup param.Carrier :=
  param.addGroup

scoped instance
    (param : Crypto.Infrastructure.Computation.Algebra.Parameter.AdditiveGroupParam) :
    Fintype param.Carrier :=
  param.fintypeCarrier

end AdditiveGroupParam

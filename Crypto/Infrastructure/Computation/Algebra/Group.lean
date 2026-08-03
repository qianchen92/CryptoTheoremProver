import Mathlib.Algebra.Group.Defs
import Mathlib.Data.Fintype.Basic

namespace Crypto.Infrastructure.Computation.Algebra.Group

universe uGroup

/-- A public description of a finite nonempty additive group. -/
structure AdditiveGroupParam where
  Carrier : Type uGroup
  addGroup : AddGroup Carrier
  fintypeCarrier : Fintype Carrier
  nonemptyCarrier : Nonempty Carrier

scoped[AdditiveGroupParam] attribute [instance]
  Crypto.Infrastructure.Computation.Algebra.Group.AdditiveGroupParam.addGroup
scoped[AdditiveGroupParam] attribute [instance]
  Crypto.Infrastructure.Computation.Algebra.Group.AdditiveGroupParam.fintypeCarrier
scoped[AdditiveGroupParam] attribute [instance]
  Crypto.Infrastructure.Computation.Algebra.Group.AdditiveGroupParam.nonemptyCarrier

end Crypto.Infrastructure.Computation.Algebra.Group

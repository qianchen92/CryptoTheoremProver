import Crypto.Infrastructure.Computation.Algebra.Parameter
import Mathlib.Algebra.Group.Action.Defs

namespace Crypto.Assumption.DL.Parameter

open Crypto.Infrastructure.Computation.Algebra

universe uScalar uGroup

/-- Generator surjectivity supplies the scalar witness needed by sampling. -/
def scalarNonemptyOfGenerator
    {Scalar : Type uScalar} {Carrier : Type uGroup}
    [AddGroup Carrier] [SMul Scalar Carrier]
    (generator : Carrier)
    (generator_generates : ∀ value : Carrier, ∃ scalar : Scalar,
      scalar • generator = value) : Nonempty Scalar := by
  rcases generator_generates 0 with ⟨scalar, _hscalar⟩
  exact ⟨scalar⟩

/--
Shared finite cyclic-action parameter used by discrete-log style problems.

This is the mathematical layer only.  Executable primitive handlers,
distributional laws, and resource bounds belong to the assumption-specific
`PublicParam` records built over this structure.
-/
structure CyclicAction (Scalar : Type uScalar) (Carrier : Type uGroup) where
  addGroup : AddGroup Carrier
  fintypeCarrier : Fintype Carrier
  fintypeScalar : Fintype Scalar
  smul : SMul Scalar Carrier
  generator : Carrier
  generator_generates : ∀ value : Carrier, ∃ scalar : Scalar,
    scalar • generator = value

namespace CyclicAction

/-- The fixed scalar representation selected by this parameter. -/
abbrev Scalar
    {Scalar : Type uScalar} {Carrier : Type uGroup}
    (_pp : CyclicAction Scalar Carrier) := Scalar

/-- The fixed group representation selected by this parameter. -/
abbrev Carrier
    {Scalar : Type uScalar} {Carrier : Type uGroup}
    (_pp : CyclicAction Scalar Carrier) := Carrier

/-- Compatibility projection to the generic finite additive-group parameter. -/
def toAdditiveGroupParam
    {Scalar : Type uScalar} {Carrier : Type uGroup}
    (pp : CyclicAction Scalar Carrier) :
    Crypto.Infrastructure.Computation.Algebra.Parameter.AdditiveGroupParam where
  Carrier := Carrier
  addGroup := pp.addGroup
  fintypeCarrier := pp.fintypeCarrier

/-- Scoped additive-group projection inherited from the finite additive base. -/
abbrev instAddGroup
    {Scalar : Type uScalar} {Carrier : Type uGroup}
    (pp : CyclicAction Scalar Carrier) : AddGroup Carrier :=
  pp.addGroup

/-- Scoped carrier-finiteness projection inherited from the finite additive base. -/
abbrev instFintypeCarrier
    {Scalar : Type uScalar} {Carrier : Type uGroup}
    (pp : CyclicAction Scalar Carrier) : Fintype Carrier :=
  pp.fintypeCarrier

/-- Scoped carrier-nonemptiness projection inherited from the finite additive base. -/
abbrev instNonemptyCarrier
    {Scalar : Type uScalar} {Carrier : Type uGroup}
    (pp : CyclicAction Scalar Carrier) : Nonempty Carrier :=
  ⟨pp.addGroup.zero⟩

end CyclicAction

/--
The stronger DDH parameter extends the shared cyclic-action base with a
commutative scalar monoid and the two action laws.

The action laws are stored against the inherited `smul`, and `mulAction` below
is derived from that same operation. This makes the two projected instances
definitionally coherent rather than introducing a typeclass diamond.
-/
structure DecisionalCyclicAction
    (Scalar : Type uScalar) (Carrier : Type uGroup)
    extends CyclicAction Scalar Carrier where
  commMonoidScalar : CommMonoid Scalar
  one_smul : ∀ value : Carrier,
    smul.smul commMonoidScalar.one value = value
  mul_smul : ∀ (left right : Scalar) (value : Carrier),
    smul.smul (commMonoidScalar.mul left right) value =
      smul.smul left (smul.smul right value)

namespace DecisionalCyclicAction

abbrev Scalar
    {Scalar : Type uScalar} {Carrier : Type uGroup}
    (_pp : DecisionalCyclicAction Scalar Carrier) := Scalar

abbrev Carrier
    {Scalar : Type uScalar} {Carrier : Type uGroup}
    (_pp : DecisionalCyclicAction Scalar Carrier) := Carrier

end DecisionalCyclicAction

/-- The stronger parameter's multiplicative action uses the inherited action. -/
@[instance_reducible] def DecisionalCyclicAction.mulAction
    {Scalar : Type uScalar} {Carrier : Type uGroup}
    (pp : DecisionalCyclicAction Scalar Carrier) :
    @MulAction Scalar Carrier pp.commMonoidScalar.toMonoid := by
  letI : CommMonoid Scalar := pp.commMonoidScalar
  letI : SMul Scalar Carrier := pp.smul
  exact {
    one_smul := pp.one_smul
    mul_smul := pp.mul_smul
  }

end Crypto.Assumption.DL.Parameter

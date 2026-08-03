import Crypto.Infrastructure.Computation.Algebra.Group
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
structure CyclicAction extends
    Crypto.Infrastructure.Computation.Algebra.Group.AdditiveGroupParam.{uGroup} where
  Scalar : Type uScalar
  fintypeScalar : Fintype Scalar
  smul : SMul Scalar Carrier
  generator : Carrier
  generator_generates : ∀ value : Carrier, ∃ scalar : Scalar,
    scalar • generator = value

namespace CyclicAction

/-- Scoped additive-group projection inherited from the finite additive base. -/
abbrev instAddGroup (pp : CyclicAction.{uScalar, uGroup}) : AddGroup pp.Carrier :=
  pp.toAdditiveGroupParam.addGroup

/-- Scoped carrier-finiteness projection inherited from the finite additive base. -/
abbrev instFintypeCarrier (pp : CyclicAction.{uScalar, uGroup}) :
    Fintype pp.Carrier :=
  pp.toAdditiveGroupParam.fintypeCarrier

/-- Scoped carrier-nonemptiness projection inherited from the finite additive base. -/
abbrev instNonemptyCarrier (pp : CyclicAction.{uScalar, uGroup}) :
    Nonempty pp.Carrier :=
  pp.toAdditiveGroupParam.nonemptyCarrier

end CyclicAction

/--
The stronger DDH parameter extends the shared cyclic-action base with a
commutative scalar monoid and the two action laws.

The action laws are stored against the inherited `smul`, and `mulAction` below
is derived from that same operation. This makes the two projected instances
definitionally coherent rather than introducing a typeclass diamond.
-/
structure DecisionalCyclicAction extends CyclicAction.{uScalar, uGroup} where
  commMonoidScalar : CommMonoid Scalar
  one_smul : ∀ value : Carrier,
    smul.smul commMonoidScalar.one value = value
  mul_smul : ∀ (left right : Scalar) (value : Carrier),
    smul.smul (commMonoidScalar.mul left right) value =
      smul.smul left (smul.smul right value)

/-- The stronger parameter's multiplicative action uses the inherited action. -/
@[instance_reducible] def DecisionalCyclicAction.mulAction
    (pp : DecisionalCyclicAction.{uScalar, uGroup}) :
    @MulAction pp.Scalar pp.Carrier pp.commMonoidScalar.toMonoid := by
  letI : CommMonoid pp.Scalar := pp.commMonoidScalar
  letI : SMul pp.Scalar pp.Carrier := pp.smul
  exact {
    one_smul := pp.one_smul
    mul_smul := pp.mul_smul
  }

end Crypto.Assumption.DL.Parameter

import Crypto.Infrastructure.SecurityParameter
import Crypto.Infrastructure.Computation.Algebra.Parameter
import Crypto.Infrastructure.Computation.Algebra.Signature
import Crypto.Infrastructure.Computation.Algebra.Handler
import Crypto.Infrastructure.Computation.Algebra.Laws
import Crypto.Infrastructure.Probability.Uniform
import Crypto.Infrastructure.Computation.Randomized
import CryptoFirstOrder.Algebra.AdditiveGroup

namespace CryptoConstruction.Primitive.Encryption.SymmetricEncryption.OneTimePad

open Crypto.Infrastructure.Computation.Algebra
open Crypto.Infrastructure.Computation.Cost
open scoped CryptoFirstOrder

universe uCost uGroup

variable {M : CostModel.{uCost}}

/-- The mathematical finite additive group underlying an OTP instance. -/
abbrev MathematicalParam :=
  Crypto.Infrastructure.Computation.Algebra.Parameter.AdditiveGroupParam.{uGroup}

/-- Exactly the primitive capabilities used by the one-time pad. -/
inductive Operation (math : MathematicalParam.{uGroup}) :
    Type uGroup → Type uGroup where
  | sampleKey : Operation math math.Carrier
  | add (left right : math.Carrier) : Operation math math.Carrier
  | neg (value : math.Carrier) : Operation math math.Carrier

/-- The typed OTP signature contains no unused scalar capability. -/
def signature (math : MathematicalParam.{uGroup}) : Signature.{uGroup, uGroup} where
  Op := Operation math

/-- Exact cost-erasure laws for an OTP primitive handler. -/
structure ExactLaws
    {math : MathematicalParam.{uGroup}}
    (A : CostedAlgebra M (signature math)) : Prop where
  sampleKey :
    RandCosted.valueDist (A.exec .sampleKey) =
      @Crypto.Infrastructure.Probability.uniformPMF
        math.Carrier math.fintypeCarrier ⟨math.addGroup.zero⟩
  add : ∀ left right,
    RandCosted.valueDist (A.exec (.add left right)) =
      PMF.pure (math.addGroup.add left right)
  neg : ∀ value,
    RandCosted.valueDist (A.exec (.neg value)) =
      PMF.pure (math.addGroup.neg value)

/-- A mathematical OTP parameter equipped with one authoritative exact algebra. -/
structure PublicParam (M : CostModel.{uCost}) extends MathematicalParam.{uGroup} where
  algebra : CostedAlgebra M (signature toAdditiveGroupParam)
  laws : ExactLaws algebra

namespace PublicParam

abbrev instAddGroup (pp : PublicParam M) : AddGroup pp.Carrier :=
  pp.toAdditiveGroupParam.addGroup

abbrev instFintypeCarrier (pp : PublicParam M) : Fintype pp.Carrier :=
  pp.toAdditiveGroupParam.fintypeCarrier

abbrev instNonemptyCarrier (pp : PublicParam M) : Nonempty pp.Carrier :=
  ⟨pp.toAdditiveGroupParam.addGroup.zero⟩

end PublicParam

scoped[OneTimePadParameter] attribute [instance]
  CryptoConstruction.Primitive.Encryption.SymmetricEncryption.OneTimePad.PublicParam.instAddGroup
  CryptoConstruction.Primitive.Encryption.SymmetricEncryption.OneTimePad.PublicParam.instFintypeCarrier
  CryptoConstruction.Primitive.Encryption.SymmetricEncryption.OneTimePad.PublicParam.instNonemptyCarrier

open scoped OneTimePadParameter

/- The object-language carrier used by the reified OTP algorithms. -/
namespace Language

export CryptoFirstOrder.Algebra.AdditiveGroup
  (Base carrierTy Operation signature)

/-- Object-language type of an OTP key. -/
abbrev keyTy := carrierTy

/-- Object-language type of an OTP message. -/
abbrev messageTy := carrierTy

/-- Object-language type of an OTP ciphertext. -/
abbrev ciphertextTy := carrierTy

/-- Interpret the object-language carrier using one concrete OTP parameter. -/
abbrev interpret (pp : PublicParam.{uCost, uGroup} M) : Base → Type uGroup :=
  CryptoFirstOrder.Algebra.AdditiveGroup.interpret pp.Carrier

namespace Operation

abbrev sampleKey : Operation .unit carrierTy :=
  CryptoFirstOrder.Algebra.AdditiveGroup.Operation.sample

export CryptoFirstOrder.Algebra.AdditiveGroup.Operation (add neg)

end Operation

/-- Bind the reusable adapter to the OTP parameter's authoritative handler. -/
noncomputable def handler (pp : PublicParam.{uCost, uGroup} M) :
    CryptoFirstOrder.Algebra.AdditiveGroup.Handler M pp.Carrier where
  sample := pp.algebra.exec .sampleKey
  add := fun left right => pp.algebra.exec (.add left right)
  neg := fun value => pp.algebra.exec (.neg value)

/--
First-order adapter for the parameter's authoritative exact algebra. The
adapter only moves runtime arguments out of operation constructors; it does
not replace or approximate the underlying costed computation.
-/
noncomputable def algebra (pp : PublicParam.{uCost, uGroup} M) :
    CryptoFirstOrder.CostedAlgebra
      M (interpret pp) signature :=
  CryptoFirstOrder.Algebra.AdditiveGroup.algebra (handler pp)

end Language

/-- Standard `AlgebraLaws` package derived from the OTP-specific laws. -/
noncomputable def algebraLaws (pp : PublicParam M) : AlgebraLaws pp.algebra where
  semantics operation :=
    match operation with
    | .sampleKey =>
        Crypto.Infrastructure.Probability.uniformPMF pp.Carrier
    | .add left right => PMF.pure (left + right)
    | .neg value => PMF.pure (-value)
  exec_spec operation := by
    cases operation with
    | sampleKey => exact pp.laws.sampleKey
    | add left right => exact pp.laws.add left right
    | neg value => exact pp.laws.neg value

/-- A security-parameter-indexed family of exact OTP parameters. -/
structure Family (M : CostModel.{uCost}) where
  setup : Crypto.SecPar → RandCosted M (PublicParam M)

/-- A family with one fixed public parameter and an explicit setup cost. -/
noncomputable def Family.ofFixed
    (pp : PublicParam M) (setupCost : M.Cost) : Family M where
  setup := fun _sec => RandCosted.liftCosted ⟨pp, setupCost⟩

/-- Setup distribution obtained only by erasing exact costs. -/
noncomputable def Family.setupDist (F : Family M) (sec : Crypto.SecPar) :
    PMF (PublicParam M) :=
  RandCosted.valueDist (F.setup sec)

/-- Family-level typed setup operation for an exact OTP family. -/
inductive FamilyOperation (F : Family.{uCost, uGroup} M) :
    Type (max uCost (uGroup + 1)) →
      Type (max uCost (uGroup + 1) + 1) where
  | setup (sec : Crypto.SecPar) :
      FamilyOperation F (PublicParam.{uCost, uGroup} M)

/-- The dependent family signature containing the OTP setup primitive. -/
def familySignature (F : Family.{uCost, uGroup} M) : Signature where
  Op := FamilyOperation F

/--
The sole exact family-level handler. The existing `F.setup` computation remains
the authoritative setup primitive; the handler only exposes it to `Program`.
-/
noncomputable def familyAlgebra (F : Family.{uCost, uGroup} M) :
    CostedAlgebra M (familySignature F) where
  exec operation :=
    match operation with
    | .setup sec => F.setup sec

/-- Cost erasure of the family setup handler is exactly `Family.setupDist`. -/
noncomputable def familyAlgebraLaws (F : Family.{uCost, uGroup} M) :
    AlgebraLaws (familyAlgebra F) where
  semantics operation :=
    match operation with
    | .setup sec => F.setupDist sec
  exec_spec operation := by
    cases operation
    rfl

end CryptoConstruction.Primitive.Encryption.SymmetricEncryption.OneTimePad

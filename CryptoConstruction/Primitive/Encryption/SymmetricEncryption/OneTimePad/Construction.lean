import Crypto.Infrastructure.SecurityParameter
import Crypto.Infrastructure.Computation.Algebra.Parameter
import Crypto.Infrastructure.Computation.Algebra.Signature
import Crypto.Infrastructure.Computation.Algebra.Handler
import Crypto.Infrastructure.Computation.Algebra.Laws
import Crypto.Infrastructure.Computation.Algebra.Bounds
import Crypto.Infrastructure.Probability.Uniform
import Crypto.Infrastructure.Computation.Program.Basic
import Crypto.Infrastructure.Computation.Randomized

namespace CryptoConstruction.Primitive.Encryption.SymmetricEncryption.OneTimePad

open Crypto.Infrastructure.Computation
open Crypto.Infrastructure.Computation.Algebra
open Crypto.Infrastructure.Computation.Cost

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

/-- Uniform operation budgets attached to the exact OTP algebra. -/
structure ParamEfficiencyCertificate (pp : PublicParam M) where
  bounds : OperationBounds pp.algebra
  sampleKeyBudget : M.Cost
  sampleKeyBudget_sound :
    M.instPartialOrder.le (bounds.budget Operation.sampleKey) sampleKeyBudget
  addBudget : M.Cost
  addBudget_sound : ∀ left right,
    M.instPartialOrder.le (bounds.budget (Operation.add left right)) addBudget
  negBudget : M.Cost
  negBudget_sound : ∀ value,
    M.instPartialOrder.le (bounds.budget (Operation.neg value)) negBudget

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

/-- OTP setup as a typed family-level program. -/
def setupProgram (F : Family.{uCost, uGroup} M) :
    Program (familyAlgebra F) Crypto.SecPar
      (PublicParam.{uCost, uGroup} M) where
  body sec := .call (.setup sec)

/-- The family-level setup program delegates to the unique exact setup primitive. -/
@[simp] theorem setupProgram_runCosted
    (F : Family.{uCost, uGroup} M) (sec : Crypto.SecPar) :
    Program.runCosted (setupProgram F) sec = F.setup sec :=
  rfl

/-- Global setup efficiency for an OTP family. -/
structure EfficiencyCertificate (F : Family M) where
  setupBudget : Crypto.SecPar → M.Cost
  setupCostBound : Program.CostBound (setupProgram F) setupBudget

/-- Exact setup efficiency for a fixed OTP family. -/
noncomputable def EfficiencyCertificate.ofFixed
    (pp : PublicParam M) (setupCost : M.Cost) :
    EfficiencyCertificate (Family.ofFixed pp setupCost) where
  setupBudget := fun _sec => setupCost
  setupCostBound := by
    intro sec result hresult
    simp only [setupProgram, Program.Code.runCosted, familyAlgebra,
      Family.ofFixed, RandCosted.liftCosted, PMF.mem_support_pure_iff] at hresult
    subst result
    letI := M.instPartialOrder
    exact le_refl setupCost

/-- The authoritative setup program satisfies the supplied global certificate. -/
theorem setup_costBound
    (F : Family M) (certificate : EfficiencyCertificate F) :
    Program.CostBound (setupProgram F) certificate.setupBudget :=
  certificate.setupCostBound

end CryptoConstruction.Primitive.Encryption.SymmetricEncryption.OneTimePad

import Crypto.Infrastructure.Asymptotic.SecurityParameter
import Crypto.Infrastructure.Computation.Algebra.Group
import Crypto.Infrastructure.Computation.Algebra.Signature
import Crypto.Infrastructure.Computation.Distribution
import Crypto.Infrastructure.Computation.Program
import Crypto.Infrastructure.Computation.Randomized

namespace Crypto.Primitive.Encryption.SymmetricEncryption.Instantiations.OneTimePad

open Crypto.Infrastructure.Computation
open Crypto.Infrastructure.Computation.Algebra
open Crypto.Infrastructure.Computation.Cost
open scoped AdditiveGroupParam

universe uCost uGroup

/-- The mathematical finite additive group underlying an OTP instance. -/
abbrev MathematicalParam :=
  Crypto.Infrastructure.Computation.Algebra.Group.AdditiveGroupParam.{uGroup}

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
    {M : CostModel.{uCost}} {math : MathematicalParam.{uGroup}}
    (A : CostedAlgebra M (signature math)) : Prop where
  sampleKey :
    RandCostedT.valueDist (A.exec .sampleKey) =
      Crypto.Infrastructure.Computation.Distribution.uniformPMF math.Carrier
  add : ∀ left right,
    RandCostedT.valueDist (A.exec (.add left right)) =
      PMF.pure (left + right)
  neg : ∀ value,
    RandCostedT.valueDist (A.exec (.neg value)) = PMF.pure (-value)

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
  pp.toAdditiveGroupParam.nonemptyCarrier

end PublicParam

scoped[OneTimePadParameter] attribute [instance]
  Crypto.Primitive.Encryption.SymmetricEncryption.Instantiations.OneTimePad.PublicParam.instAddGroup
  Crypto.Primitive.Encryption.SymmetricEncryption.Instantiations.OneTimePad.PublicParam.instFintypeCarrier
  Crypto.Primitive.Encryption.SymmetricEncryption.Instantiations.OneTimePad.PublicParam.instNonemptyCarrier

open scoped OneTimePadParameter

/-- Standard `AlgebraLaws` package derived from the OTP-specific laws. -/
noncomputable def algebraLaws (pp : PublicParam M) : AlgebraLaws pp.algebra where
  semantics operation :=
    match operation with
    | .sampleKey =>
        Crypto.Infrastructure.Computation.Distribution.uniformPMF pp.Carrier
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
  setup : Crypto.SecPar → RandCostedT M (PublicParam M)

/-- A family with one fixed public parameter and an explicit setup cost. -/
noncomputable def Family.ofFixed
    (pp : PublicParam M) (setupCost : M.Cost) : Family M where
  setup := fun _sec => RandCostedT.liftCosted ⟨pp, setupCost⟩

/-- Setup distribution obtained only by erasing exact costs. -/
noncomputable def Family.setupDist (F : Family M) (sec : Crypto.SecPar) :
    PMF (PublicParam M) :=
  RandCostedT.valueDist (F.setup sec)

/-- Global setup efficiency for an OTP family. -/
structure EfficiencyCertificate (F : Family M) where
  setupBudget : Crypto.SecPar → M.Cost
  setupCostBound :
    RandomizedComputationT.CostBound
      (fun sec (_input : Unit) => F.setup sec) setupBudget

/-- Exact setup efficiency for a fixed OTP family. -/
noncomputable def EfficiencyCertificate.ofFixed
    (pp : PublicParam M) (setupCost : M.Cost) :
    EfficiencyCertificate (Family.ofFixed pp setupCost) where
  setupBudget := fun _sec => setupCost
  setupCostBound := by
    intro sec input result hresult
    simp only [Family.ofFixed, RandCostedT.liftCosted,
      PMF.mem_support_pure_iff] at hresult
    subst result
    letI := M.instPartialOrder
    exact le_refl setupCost

/-- Native setup satisfies the supplied global setup certificate. -/
theorem setup_costBound
    (F : Family M) (certificate : EfficiencyCertificate F) :
    RandomizedComputationT.CostBound
      (fun sec (_input : Unit) => F.setup sec) certificate.setupBudget :=
  certificate.setupCostBound

end Crypto.Primitive.Encryption.SymmetricEncryption.Instantiations.OneTimePad

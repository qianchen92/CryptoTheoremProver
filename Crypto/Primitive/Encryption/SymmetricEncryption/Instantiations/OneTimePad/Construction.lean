import Crypto.Infrastructure.Asymptotic.SecurityParameter
import Crypto.Infrastructure.Computation.Algebra.Backend
import Crypto.Infrastructure.Computation.Algebra.Group
import Crypto.Infrastructure.Computation.Algebra.Signature
import Crypto.Infrastructure.Computation.Randomized

namespace Crypto.Primitive.Encryption.SymmetricEncryption.Instantiations.OneTimePad

open Crypto.Infrastructure.Computation
open Crypto.Infrastructure.Computation.Algebra
open Crypto.Infrastructure.Computation.Cost

universe uGroup

/--
The exact additive operations used by one-time-pad encryption.

This intentionally contains only addition and negation.  In particular, OTP
parameters no longer need to manufacture an unused scalar type or scalar
action in order to use the generic program language.
-/
structure Backend
    (Carrier : Type uGroup) [AddGroup Carrier] where
  add : Carrier → Carrier → Costed Carrier
  add_spec : ∀ left right, (add left right).val = left + right
  neg : Carrier → Costed Carrier
  neg_spec : ∀ value, (neg value).val = -value

namespace Backend

variable {Carrier : Type uGroup} [AddGroup Carrier]

/-- Build exact OTP operations from explicit operand-dependent costs. -/
def ofCostFunctions
    (addCost : Carrier → Carrier → Cost)
    (negCost : Carrier → Cost) :
    Backend Carrier where
  add := fun left right => ⟨left + right, addCost left right⟩
  add_spec := by
    intros
    rfl
  neg := fun value => ⟨-value, negCost value⟩
  neg_spec := by
    intro
    rfl

/-- Build exact OTP operations with a fixed local cost for each operation kind. -/
def ofConstantCosts (addCost negCost : Cost) : Backend Carrier :=
  ofCostFunctions (fun _left _right => addCost) (fun _value => negCost)

@[simp] theorem add_val
    (backend : Backend Carrier) (left right : Carrier) :
    (backend.add left right).val = left + right :=
  backend.add_spec left right

@[simp] theorem neg_val
    (backend : Backend Carrier) (value : Carrier) :
    (backend.neg value).val = -value :=
  backend.neg_spec value

end Backend

/-- Uniform upper bounds for an exact OTP backend. -/
structure BackendBounds
    {Carrier : Type uGroup} [AddGroup Carrier]
    (backend : Backend Carrier) where
  addBudget : Cost
  addCost_le : ∀ left right, (backend.add left right).cost ≤ addBudget
  negBudget : Cost
  negCost_le : ∀ value, (backend.neg value).cost ≤ negBudget

namespace BackendBounds

variable {Carrier : Type uGroup} [AddGroup Carrier]

/-- Exact bounds for a backend constructed with constant local costs. -/
def ofConstantCosts (addCost negCost : Cost) :
    BackendBounds
      (Backend.ofConstantCosts (Carrier := Carrier) addCost negCost) where
  addBudget := addCost
  addCost_le := by
    intros
    rfl
  negBudget := negCost
  negCost_le := by
    intro
    rfl

end BackendBounds

/--
Public parameters for one-time-pad encryption.

The exact additive implementation and native uniform key sampler live beside
the mathematical finite group.  Exact OTP execution therefore needs no
parallel implementation family.
-/
structure PublicParam extends
    Crypto.Infrastructure.Computation.Algebra.Group.AdditiveGroupParam.{uGroup} where
  backend : @Backend Carrier addGroup
  keySampler :
    @UniformSampler Carrier fintypeCarrier nonemptyCarrier
  keySamplerLaws : UniformSamplerLaws keySampler

namespace PublicParam

/-- Scoped additive-group projection for OTP parameters. -/
abbrev instAddGroup (pp : PublicParam.{uGroup}) : AddGroup pp.Carrier :=
  pp.toAdditiveGroupParam.addGroup

/-- Scoped finiteness projection for OTP parameters. -/
abbrev instFintypeCarrier (pp : PublicParam.{uGroup}) : Fintype pp.Carrier :=
  pp.toAdditiveGroupParam.fintypeCarrier

/-- Scoped nonemptiness projection for OTP parameters. -/
abbrev instNonemptyCarrier (pp : PublicParam.{uGroup}) : Nonempty pp.Carrier :=
  pp.toAdditiveGroupParam.nonemptyCarrier

end PublicParam

scoped[OneTimePadParameter] attribute [instance]
  Crypto.Primitive.Encryption.SymmetricEncryption.Instantiations.OneTimePad.PublicParam.instAddGroup
scoped[OneTimePadParameter] attribute [instance]
  Crypto.Primitive.Encryption.SymmetricEncryption.Instantiations.OneTimePad.PublicParam.instFintypeCarrier
scoped[OneTimePadParameter] attribute [instance]
  Crypto.Primitive.Encryption.SymmetricEncryption.Instantiations.OneTimePad.PublicParam.instNonemptyCarrier

open scoped OneTimePadParameter

/-- Local key-sampling and additive-operation bounds used for OTP efficiency. -/
structure ParamEfficiencyCertificate
    (pp : PublicParam.{uGroup}) where
  keySamplerBounds : UniformSamplerBounds pp.keySampler
  additiveBounds : BackendBounds pp.backend

/-- The heterogeneous primitive operations available to an OTP program. -/
inductive Operation (Carrier : Type uGroup) : Type uGroup → Type uGroup where
  | sampleKey : Operation Carrier Carrier
  | add (left right : Carrier) : Operation Carrier Carrier
  | neg (value : Carrier) : Operation Carrier Carrier

/-- The typed OTP primitive signature contains exactly sample, add, and neg. -/
def signature (Carrier : Type uGroup) : Signature.{uGroup, uGroup} where
  Op := Operation Carrier

/-- The sole exact interpreter for OTP primitive operations. -/
noncomputable def costedAlgebra
    (pp : PublicParam.{uGroup}) :
    CostedAlgebra natCostModel (signature pp.Carrier) where
  exec operation :=
    match operation with
    | .sampleKey => pp.keySampler.sample
    | .add left right => RandCosted.liftCosted (pp.backend.add left right)
    | .neg value => RandCosted.liftCosted (pp.backend.neg value)

/-- Mathematical, cost-erased specifications for the exact OTP interpreter. -/
noncomputable def algebraLaws
    (pp : PublicParam.{uGroup}) :
    AlgebraLaws (costedAlgebra pp) where
  semantics operation :=
    match operation with
    | .sampleKey =>
        Crypto.Infrastructure.Computation.Distribution.uniformPMF pp.Carrier
    | .add left right => PMF.pure (left + right)
    | .neg value => PMF.pure (-value)
  exec_spec operation := by
    cases operation with
    | sampleKey => exact pp.keySamplerLaws.sample_spec
    | add left right => simp [costedAlgebra]
    | neg value => simp [costedAlgebra]

/-- Independent primitive bounds induced by a local OTP certificate. -/
noncomputable def operationBounds
    (pp : PublicParam.{uGroup})
    (certificate : ParamEfficiencyCertificate pp) :
    OperationBounds (costedAlgebra pp) where
  budget operation :=
    match operation with
    | .sampleKey => certificate.keySamplerBounds.sampleBudget
    | .add _left _right => certificate.additiveBounds.addBudget
    | .neg _value => certificate.additiveBounds.negBudget
  cost_le operation result hresult := by
    cases operation with
    | sampleKey =>
        exact certificate.keySamplerBounds.cost_le result hresult
    | add left right =>
        simp only [costedAlgebra, RandCosted.liftCosted,
          PMF.mem_support_pure_iff] at hresult
        subst result
        exact certificate.additiveBounds.addCost_le left right
    | neg value =>
        simp only [costedAlgebra, RandCosted.liftCosted,
          PMF.mem_support_pure_iff] at hresult
        subst result
        exact certificate.additiveBounds.negCost_le value

/-- A security-parameter-indexed family of native costed OTP parameters. -/
structure Family where
  setup : Crypto.SecPar → RandCosted PublicParam.{uGroup}

/-- A family with one fixed public parameter and an explicit setup cost. -/
noncomputable def Family.ofFixed
    (pp : PublicParam.{uGroup}) (setupCost : Cost) :
    Family.{uGroup} where
  setup := fun _sec => RandCosted.liftCosted ⟨pp, setupCost⟩

/--
Build one exact OTP public parameter from a member of a type-level group
family and its native implementation components.
-/
def publicParam
    (GroupFamily : Crypto.SecPar → Type uGroup)
    [∀ sec, AddGroup (GroupFamily sec)]
    [∀ sec, Fintype (GroupFamily sec)]
    (backend :
      ∀ sec, Backend (GroupFamily sec))
    (keySampler :
      ∀ sec, UniformSampler (GroupFamily sec))
    (keySamplerLaws :
      ∀ sec, UniformSamplerLaws (keySampler sec))
    (sec : Crypto.SecPar) :
    PublicParam.{uGroup} where
  Carrier := GroupFamily sec
  addGroup := inferInstance
  fintypeCarrier := inferInstance
  nonemptyCarrier := ⟨0⟩
  backend := backend sec
  keySampler := keySampler sec
  keySamplerLaws := keySamplerLaws sec

/--
The native costed OTP family induced by a type-level group family.

Setup cost remains on the same execution path as the exact parameter selected
at the requested security parameter.
-/
noncomputable def Family.ofGroupFamily
    (GroupFamily : Crypto.SecPar → Type uGroup)
    [∀ sec, AddGroup (GroupFamily sec)]
    [∀ sec, Fintype (GroupFamily sec)]
    (backend :
      ∀ sec, Backend (GroupFamily sec))
    (keySampler :
      ∀ sec, UniformSampler (GroupFamily sec))
    (keySamplerLaws :
      ∀ sec, UniformSamplerLaws (keySampler sec))
    (setupCost : Crypto.SecPar → Cost) :
    Family.{uGroup} where
  setup := fun sec =>
    RandCosted.liftCosted
      ⟨publicParam GroupFamily backend keySampler keySamplerLaws sec,
        setupCost sec⟩

/-- The mathematical setup distribution obtained by erasing native setup costs. -/
noncomputable def Family.setupDist
    (F : Family.{uGroup}) (sec : Crypto.SecPar) :
    PMF PublicParam.{uGroup} :=
  RandCosted.valueDist (F.setup sec)

/--
Global setup efficiency for an OTP family.

Local key-generation, encryption, and decryption bounds belong to
`ParamEfficiencyCertificate`; exact family semantics do not depend on either
certificate.
-/
structure EfficiencyCertificate
    (F : Family.{uGroup}) where
  setupBudget : Crypto.SecPar → Cost
  setupCostBound :
    RandomizedComputation.CostBound
      (fun sec (_input : Unit) => F.setup sec) setupBudget

/-- Exact setup efficiency for a fixed OTP family. -/
noncomputable def EfficiencyCertificate.ofFixed
    (pp : PublicParam.{uGroup}) (setupCost : Cost) :
    EfficiencyCertificate (Family.ofFixed pp setupCost) where
  setupBudget := fun _sec => setupCost
  setupCostBound := by
    intro sec input result hresult
    simp only [Family.ofFixed, RandCosted.liftCosted,
      PMF.mem_support_pure_iff] at hresult
    subst result
    rfl

/-- Native setup satisfies the supplied global setup-efficiency certificate. -/
theorem setup_costBound
    (F : Family.{uGroup}) (certificate : EfficiencyCertificate F) :
    RandomizedComputation.CostBound
      (fun sec (_input : Unit) => F.setup sec) certificate.setupBudget :=
  certificate.setupCostBound

end Crypto.Primitive.Encryption.SymmetricEncryption.Instantiations.OneTimePad

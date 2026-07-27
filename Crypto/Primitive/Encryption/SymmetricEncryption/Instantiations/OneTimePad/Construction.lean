import Crypto.Infrastructure.Asymptotic.SecurityParameter
import Crypto.Infrastructure.Computation.Algebra.Backend
import Crypto.Infrastructure.Computation.Randomized

namespace Crypto.Primitive.Encryption.SymmetricEncryption.Instantiations.OneTimePad

open Crypto.Infrastructure.Computation
open Crypto.Infrastructure.Computation.Algebra
open Crypto.Infrastructure.Computation.Cost

universe uGroup

/--
An unused scalar sort for the generic algebraic program interface.

One-time-pad programs use addition and negation but no scalar multiplication.
The identity action supplies the irrelevant scalar operation without imposing
another algebraic requirement on the message group.
-/
inductive UnusedScalar where
  | unit

instance instSMulUnusedScalar {Carrier : Type uGroup} :
    SMul UnusedScalar Carrier where
  smul := fun _ value => value

/--
Public parameters for one-time-pad encryption.

The exact additive implementation and native uniform key sampler live beside
the mathematical finite group.  Exact OTP execution therefore needs no
parallel implementation family.
-/
structure PublicParam where
  Carrier : Type uGroup
  addGroup : AddGroup Carrier
  fintypeCarrier : Fintype Carrier
  backend :
    @AdditiveBackend UnusedScalar Carrier
      addGroup instSMulUnusedScalar
  keySampler :
    @UniformSampler Carrier fintypeCarrier ⟨0⟩

attribute [instance] PublicParam.addGroup
attribute [instance] PublicParam.fintypeCarrier

instance (pp : PublicParam.{uGroup}) : Nonempty pp.Carrier :=
  ⟨0⟩

/-- Local additive-operation bounds used only when proving OTP efficiency. -/
structure ParamEfficiencyCertificate
    (pp : PublicParam.{uGroup}) where
  additiveBounds : AdditiveCostBounds pp.backend

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
      ∀ sec, AdditiveBackend UnusedScalar (GroupFamily sec))
    (keySampler :
      ∀ sec, UniformSampler (GroupFamily sec))
    (sec : Crypto.SecPar) :
    PublicParam.{uGroup} where
  Carrier := GroupFamily sec
  addGroup := inferInstance
  fintypeCarrier := inferInstance
  backend := backend sec
  keySampler := keySampler sec

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
      ∀ sec, AdditiveBackend UnusedScalar (GroupFamily sec))
    (keySampler :
      ∀ sec, UniformSampler (GroupFamily sec))
    (setupCost : Crypto.SecPar → Cost) :
    Family.{uGroup} where
  setup := fun sec =>
    RandCosted.liftCosted
      ⟨publicParam GroupFamily backend keySampler sec, setupCost sec⟩

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

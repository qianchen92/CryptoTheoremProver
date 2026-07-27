import Crypto.Infrastructure.Computation.Algebra.Backend
import Crypto.Infrastructure.Computation.Randomized
import Crypto.Infrastructure.GameBased.Search
import Mathlib.Probability.ProbabilityMassFunction.Monad

namespace Crypto.Assumption.DL

namespace DLog

open Crypto.Infrastructure.Computation
open Crypto.Infrastructure.Computation.Algebra
open Crypto.Infrastructure.Computation.Cost

universe uScalar uGroup

/--
Surjectivity of the generator action supplies the scalar witness required by
uniform sampling.
-/
private def scalarNonemptyOfGenerator
    {Scalar : Type uScalar} {Carrier : Type uGroup}
    [AddGroup Carrier] [SMul Scalar Carrier]
    (generator : Carrier)
    (generator_generates : ∀ x : Carrier, ∃ a : Scalar, a • generator = x) :
    Nonempty Scalar := by
  rcases generator_generates 0 with ⟨scalar, _hscalar⟩
  exact ⟨scalar⟩

/--
Public parameters for a finite additive-group discrete-log instance.

The exact algebra backend and scalar sampler belong to the parameter.
Efficiency bounds are separate certificates and do not affect the assumption.
-/
structure PublicParam where
  Scalar : Type uScalar
  Carrier : Type uGroup
  addGroup : AddGroup Carrier
  fintypeCarrier : Fintype Carrier
  fintypeScalar : Fintype Scalar
  smul : SMul Scalar Carrier
  generator : Carrier
  generator_generates : ∀ x : Carrier, ∃ a : Scalar, a • generator = x
  backend : @AdditiveBackend Scalar Carrier addGroup smul
  scalarSampler :
    @UniformSampler Scalar fintypeScalar
      (@scalarNonemptyOfGenerator
        Scalar Carrier addGroup smul generator generator_generates)

attribute [instance] PublicParam.addGroup
attribute [instance] PublicParam.fintypeCarrier
attribute [instance] PublicParam.fintypeScalar
attribute [instance] PublicParam.smul

instance (pp : PublicParam.{uScalar, uGroup}) : Nonempty pp.Carrier :=
  ⟨0⟩

instance (pp : PublicParam.{uScalar, uGroup}) : Nonempty pp.Scalar :=
  scalarNonemptyOfGenerator pp.generator pp.generator_generates

/-- Local algebraic cost bounds used only when proving DLog efficiency. -/
structure ParamEfficiencyCertificate
    (pp : PublicParam.{uScalar, uGroup}) where
  additiveBounds : AdditiveCostBounds pp.backend

/-- One scalar sample followed by one scalar action generates a DLog challenge. -/
def ParamEfficiencyCertificate.sampleTailBudget
    {pp : PublicParam.{uScalar, uGroup}}
    (certificate : ParamEfficiencyCertificate pp) : Cost :=
  pp.scalarSampler.sampleBudget + certificate.additiveBounds.smulBudget

/-- A security-parameter-indexed family of native costed DLog parameters. -/
structure Family where
  setup : Crypto.SecPar → RandCosted PublicParam.{uScalar, uGroup}

/-- A family with one fixed public parameter and an explicit setup cost. -/
noncomputable def Family.ofFixed
    (pp : PublicParam.{uScalar, uGroup}) (setupCost : Cost) :
    Family.{uScalar, uGroup} where
  setup := fun _sec => RandCosted.liftCosted ⟨pp, setupCost⟩

/-- The mathematical setup distribution obtained by erasing native setup costs. -/
noncomputable def Family.setupDist
    (F : Family.{uScalar, uGroup}) (sec : Crypto.SecPar) :
    PMF PublicParam.{uScalar, uGroup} :=
  RandCosted.valueDist (F.setup sec)

/-- Input given to a discrete-log adversary: public parameters and a challenge element. -/
abbrev ChallengeInput :=
  Sigma fun pp : PublicParam.{uScalar, uGroup} => pp.Carrier

/-- A candidate discrete-log witness for a challenge. -/
abbrev Witness (challenge : ChallengeInput.{uScalar, uGroup}) :=
  challenge.1.Scalar

/-- A witness solves a challenge if it maps the public generator to the challenge element. -/
def IsSolution
    (challenge : ChallengeInput.{uScalar, uGroup}) (witness : Witness challenge) : Prop :=
  witness • challenge.1.generator = challenge.2

noncomputable instance instDecidableIsSolution
    (challenge : ChallengeInput.{uScalar, uGroup}) (witness : Witness challenge) :
    Decidable (IsSolution challenge witness) :=
  Classical.propDecidable _

/-- Costed construction of a DLog challenge from a fixed secret scalar. -/
def challengeComputation
    (pp : PublicParam.{uScalar, uGroup}) (secret : pp.Scalar) :
    Costed ChallengeInput.{uScalar, uGroup} :=
  Costed.map (fun challenge => ⟨pp, challenge⟩)
    (pp.backend.smul secret pp.generator)

/-- Erasing the local scalar-action cost recovers the mathematical DLog challenge. -/
@[simp] theorem challengeComputation_value
    (pp : PublicParam.{uScalar, uGroup}) (secret : pp.Scalar) :
    (challengeComputation pp secret).val =
      ⟨pp, secret • pp.generator⟩ := by
  simp [challengeComputation]

/-- A fixed-secret DLog challenge costs exactly its underlying scalar action. -/
@[simp] theorem challengeComputation_cost
    (pp : PublicParam.{uScalar, uGroup}) (secret : pp.Scalar) :
    (challengeComputation pp secret).cost =
      (pp.backend.smul secret pp.generator).cost := by
  rfl

/-- A fixed-secret challenge satisfies the certified scalar-action budget. -/
theorem challengeComputation_cost_le
    (pp : PublicParam.{uScalar, uGroup})
    (certificate : ParamEfficiencyCertificate pp)
    (secret : pp.Scalar) :
    (challengeComputation pp secret).cost ≤
      certificate.additiveBounds.smulBudget :=
  certificate.additiveBounds.smulCost_le secret pp.generator

/-- The scalar-sampling and scalar-action tail at a fixed DLog parameter. -/
noncomputable def sampleTailComputation
    (pp : PublicParam.{uScalar, uGroup}) :
    RandCosted ChallengeInput.{uScalar, uGroup} :=
  RandCosted.bind pp.scalarSampler.sample fun secret =>
    RandCosted.liftCosted (challengeComputation pp secret)

/-- Every fixed-parameter sample tail satisfies its local efficiency certificate. -/
theorem sampleTailComputation_cost_le
    (pp : PublicParam.{uScalar, uGroup})
    (certificate : ParamEfficiencyCertificate pp) :
    ∀ result, result ∈ (sampleTailComputation pp).support →
      result.cost ≤ certificate.sampleTailBudget := by
  intro result hresult
  simp only [sampleTailComputation, RandCosted.bind] at hresult
  rw [PMF.mem_support_bind_iff] at hresult
  rcases hresult with ⟨sampleResult, hsampleResult, hchallengeResult⟩
  rw [PMF.mem_support_map_iff] at hchallengeResult
  rcases hchallengeResult with ⟨challengeResult, hchallengeResult, hresult⟩
  simp only [RandCosted.liftCosted] at hchallengeResult
  rw [PMF.mem_support_pure_iff] at hchallengeResult
  subst challengeResult
  subst result
  exact Nat.add_le_add
    (pp.scalarSampler.cost_le sampleResult hsampleResult)
    (challengeComputation_cost_le pp certificate sampleResult.val)

/-- Native costed sampling for the DLog search problem, including setup. -/
noncomputable def sampleComputation
    (F : Family.{uScalar, uGroup}) (sec : Crypto.SecPar) :
    RandCosted ChallengeInput.{uScalar, uGroup} :=
  RandCosted.bind (F.setup sec) sampleTailComputation

/-- The mathematical DLog distribution is cost erasure of the native computation. -/
noncomputable def sampleDist
    (F : Family.{uScalar, uGroup}) (sec : Crypto.SecPar) :
    PMF ChallengeInput.{uScalar, uGroup} :=
  RandCosted.valueDist (sampleComputation F sec)

/-- Erasing costs from native DLog sampling gives its mathematical distribution. -/
@[simp] theorem sampleComputation_valueDist
    (F : Family.{uScalar, uGroup}) (sec : Crypto.SecPar) :
    RandCosted.valueDist (sampleComputation F sec) = sampleDist F sec :=
  rfl

/--
Global efficiency bounds for a DLog family.

The exact family and the DLog assumption do not depend on this certificate.
-/
structure EfficiencyCertificate (F : Family.{uScalar, uGroup}) where
  setupBudget : Crypto.SecPar → Cost
  setupCostBound :
    RandomizedComputation.CostBound
      (fun sec (_input : Unit) => F.setup sec) setupBudget
  sampleBudget : Crypto.SecPar → Cost
  sampleCostBound :
    RandomizedComputation.CostBound
      (fun sec (_input : Unit) => sampleComputation F sec)
      sampleBudget

/-- The setup computation satisfies the supplied global efficiency certificate. -/
theorem setup_costBound
    (F : Family.{uScalar, uGroup}) (certificate : EfficiencyCertificate F) :
    RandomizedComputation.CostBound
      (fun sec (_input : Unit) => F.setup sec) certificate.setupBudget :=
  certificate.setupCostBound

/-- DLog sampling satisfies the supplied global efficiency certificate. -/
theorem sampleComputation_costBound
    (F : Family.{uScalar, uGroup}) (certificate : EfficiencyCertificate F) :
    RandomizedComputation.CostBound
      (fun sec (_input : Unit) => sampleComputation F sec)
      certificate.sampleBudget :=
  certificate.sampleCostBound

/-- Exact compositional bounds for a fixed DLog parameter family. -/
noncomputable def EfficiencyCertificate.ofFixed
    (pp : PublicParam.{uScalar, uGroup})
    (paramCertificate : ParamEfficiencyCertificate pp)
    (setupCost : Cost) :
    EfficiencyCertificate (Family.ofFixed pp setupCost) where
  setupBudget := fun _sec => setupCost
  setupCostBound := by
    intro sec input result hresult
    simp only [Family.ofFixed, RandCosted.liftCosted,
      PMF.mem_support_pure_iff] at hresult
    subst result
    rfl
  sampleBudget :=
    fun _sec => setupCost + paramCertificate.sampleTailBudget
  sampleCostBound := by
    intro sec input result hresult
    simp only [sampleComputation, RandCosted.bind] at hresult
    rw [PMF.mem_support_bind_iff] at hresult
    rcases hresult with ⟨setupResult, hsetupResult, htailResult⟩
    rw [PMF.mem_support_map_iff] at htailResult
    rcases htailResult with ⟨tailResult, htailResult, hresult⟩
    subst result
    simp only [Family.ofFixed, RandCosted.liftCosted,
      PMF.mem_support_pure_iff] at hsetupResult
    subst setupResult
    simp only [Costed.bind_cost]
    exact Nat.add_le_add_left
      (sampleTailComputation_cost_le pp paramCertificate
        tailResult htailResult)
      setupCost

/-- The search problem induced by a native costed DLog family. -/
noncomputable def dLogProblem (F : Family.{uScalar, uGroup}) :
    Crypto.Infrastructure.GameBased.Search.Problem.{
      max (uScalar + 1) (uGroup + 1), uScalar} ChallengeInput.{uScalar, uGroup} where
  Witness := Witness
  sample := sampleDist F
  relation := IsSolution
  decidableRelation := instDecidableIsSolution

/-- The discrete-log assumption for a native costed family. -/
def Assumption (F : Family.{uScalar, uGroup}) : Prop :=
  Crypto.Infrastructure.GameBased.Search.Hard (dLogProblem F)

end DLog

end Crypto.Assumption.DL

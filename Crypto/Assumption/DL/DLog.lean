import Crypto.Assumption.DL.Parameter
import Crypto.Infrastructure.Computation.Program
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
Public parameters for a finite additive-group discrete-log instance.

The exact algebra backend and scalar sampler belong to the parameter.
Efficiency bounds are separate certificates and do not affect the assumption.
-/
abbrev PublicParam :=
  Crypto.Assumption.DL.Parameter.CyclicAction.{uScalar, uGroup}

scoped[DLogParameter] attribute [instance]
  Crypto.Assumption.DL.Parameter.CyclicAction.instAddGroup
scoped[DLogParameter] attribute [instance]
  Crypto.Assumption.DL.Parameter.CyclicAction.instFintypeCarrier
scoped[DLogParameter] attribute [instance]
  Crypto.Assumption.DL.Parameter.CyclicAction.fintypeScalar
scoped[DLogParameter] attribute [instance]
  Crypto.Assumption.DL.Parameter.CyclicAction.smul
scoped[DLogParameter] attribute [instance]
  Crypto.Assumption.DL.Parameter.CyclicAction.instNonemptyCarrier

@[instance_reducible] def instNonemptyScalar
    (pp : PublicParam.{uScalar, uGroup}) : Nonempty pp.Scalar :=
  @Crypto.Assumption.DL.Parameter.scalarNonemptyOfGenerator
    pp.Scalar pp.Carrier pp.addGroup pp.smul
    pp.generator pp.generator_generates

scoped[DLogParameter] attribute [instance]
  Crypto.Assumption.DL.DLog.instNonemptyScalar

open scoped DLogParameter

/-- Local sampler and algebraic bounds used only when proving DLog efficiency. -/
structure ParamEfficiencyCertificate
    (pp : PublicParam.{uScalar, uGroup}) where
  scalarSamplerBounds : UniformSamplerBounds pp.scalarSampler
  additiveBounds : AdditiveCostBounds pp.backend

/-- Exactly the typed primitive capabilities used by DLog at one parameter. -/
inductive Op (pp : PublicParam.{uScalar, uGroup}) :
    Type (max uScalar uGroup) → Type (max uScalar uGroup + 1) where
  | sampleScalar : Op pp (ULift.{uGroup} pp.Scalar)
  | smul (scalar : pp.Scalar) (value : pp.Carrier) :
      Op pp (ULift.{uScalar} pp.Carrier)

/-- The dependent typed signature selected by one DLog parameter. -/
def signature (pp : PublicParam.{uScalar, uGroup}) : Signature where
  Op := Op pp

/-- The sole exact interpreter for DLog primitives at one parameter. -/
noncomputable def algebra (pp : PublicParam.{uScalar, uGroup}) :
    CostedAlgebra natCostModel (signature pp) where
  exec operation :=
    match operation with
    | .sampleScalar => RandCosted.map ULift.up pp.scalarSampler.sample
    | .smul scalar value =>
        RandCosted.liftCosted
          (Costed.map ULift.up (pp.backend.smul scalar value))

/-- Mathematical, cost-erased specifications for the exact DLog handler. -/
noncomputable def algebraLaws (pp : PublicParam.{uScalar, uGroup}) :
    AlgebraLaws (algebra pp) where
  semantics operation :=
    match operation with
    | .sampleScalar =>
        PMF.map ULift.up
          (Crypto.Infrastructure.Computation.Distribution.uniformPMF pp.Scalar)
    | .smul scalar value => PMF.pure (ULift.up (scalar • value))
  exec_spec operation := by
    cases operation with
    | sampleScalar =>
        simpa [algebra] using
          congrArg (PMF.map ULift.up) pp.scalarSamplerLaws.sample_spec
    | smul scalar value => simp [algebra]

/-- Independent operation bounds for the exact DLog handler. -/
noncomputable def operationBounds
    (pp : PublicParam.{uScalar, uGroup})
    (certificate : ParamEfficiencyCertificate pp) :
    OperationBounds (algebra pp) where
  budget operation :=
    match operation with
    | .sampleScalar => certificate.scalarSamplerBounds.sampleBudget
    | .smul _ _ => certificate.additiveBounds.smulBudget
  cost_le operation result hresult := by
    cases operation with
    | sampleScalar =>
        simp only [algebra, RandCosted.map, RandCostedT.map] at hresult
        rw [PMF.mem_support_map_iff] at hresult
        rcases hresult with ⟨sampleResult, hsampleResult, hresult⟩
        subst result
        exact certificate.scalarSamplerBounds.cost_le
          sampleResult hsampleResult
    | smul scalar value =>
        simp only [algebra, RandCosted.liftCosted,
          RandCostedT.liftCosted] at hresult
        rw [PMF.mem_support_pure_iff] at hresult
        subst result
        exact certificate.additiveBounds.smulCost_le scalar value

/-- One scalar sample followed by one scalar action generates a DLog challenge. -/
def ParamEfficiencyCertificate.sampleTailBudget
    {pp : PublicParam.{uScalar, uGroup}}
    (certificate : ParamEfficiencyCertificate pp) : Cost :=
  certificate.scalarSamplerBounds.sampleBudget +
    certificate.additiveBounds.smulBudget

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

/--
The family-level typed operations used by complete DLog sampling.

The setup result itself fixes the dependent scalar and carrier types used by
the remaining operations.  The high `ULift`s place those parameter-dependent
types in the same result universe as `PublicParam`; they do not alter values or
costs.
-/
inductive FamilyOp (F : Family.{uScalar, uGroup}) :
    Type (max (uScalar + 1) (uGroup + 1)) →
      Type (max (uScalar + 1) (uGroup + 1) + 1) where
  | setup (sec : Crypto.SecPar) :
      FamilyOp F PublicParam.{uScalar, uGroup}
  | sampleScalar (pp : PublicParam.{uScalar, uGroup}) :
      FamilyOp F
        (ULift.{max (uScalar + 1) (uGroup + 1)} pp.Scalar)
  | smul (pp : PublicParam.{uScalar, uGroup})
      (scalar : pp.Scalar) (value : pp.Carrier) :
      FamilyOp F
        (ULift.{max (uScalar + 1) (uGroup + 1)} pp.Carrier)

/-- The dependent typed signature for complete DLog family computations. -/
def familySignature (F : Family.{uScalar, uGroup}) : Signature where
  Op := FamilyOp F

/--
The sole exact family-level DLog handler.

Parameter-local operations delegate to `algebra pp`; this handler only
dispatches the setup-dependent operation and raises the result universe.
-/
noncomputable def familyAlgebra (F : Family.{uScalar, uGroup}) :
    CostedAlgebra natCostModel (familySignature F) where
  exec operation :=
    match operation with
    | .setup sec => F.setup sec
    | .sampleScalar pp =>
        RandCosted.map (fun result => ULift.up result.down)
          ((algebra pp).exec .sampleScalar)
    | .smul pp scalar value =>
        RandCosted.map (fun result => ULift.up result.down)
          ((algebra pp).exec (.smul scalar value))

/-- Cost-erased specifications for setup and all delegated DLog operations. -/
noncomputable def familyAlgebraLaws (F : Family.{uScalar, uGroup}) :
    AlgebraLaws (familyAlgebra F) where
  semantics operation :=
    match operation with
    | .setup sec => F.setupDist sec
    | .sampleScalar pp =>
        PMF.map (fun result => ULift.up result.down)
          ((algebraLaws pp).semantics Op.sampleScalar)
    | .smul pp scalar value =>
        PMF.map (fun result => ULift.up result.down)
          ((algebraLaws pp).semantics (Op.smul scalar value))
  exec_spec operation := by
    cases operation with
    | setup sec => rfl
    | sampleScalar pp =>
        simp [familyAlgebra, (algebraLaws pp).exec_spec]
    | smul pp scalar value =>
        simp [familyAlgebra, (algebraLaws pp).exec_spec]

/-- Setup itself is a typed family-level program. -/
def setupProgram (F : Family.{uScalar, uGroup}) :
    Program (familyAlgebra F) Crypto.SecPar
      PublicParam.{uScalar, uGroup} where
  body sec := .call (.setup sec)

/-- The typed setup program is exactly the family's native setup computation. -/
@[simp] theorem setupProgram_runCosted
    (F : Family.{uScalar, uGroup}) (sec : Crypto.SecPar) :
    Program.runCosted (setupProgram F) sec = F.setup sec := by
  rfl

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

/-- Fixed-secret DLog challenge generation as a typed primitive program. -/
def challengeProgram (pp : PublicParam.{uScalar, uGroup}) :
    Program (algebra pp) pp.Scalar (ULift.{uScalar} pp.Carrier) where
  body secret := .call (.smul secret pp.generator)

/-- The typed challenge program is the point-mass compatibility computation. -/
@[simp] theorem challengeProgram_runCosted
    (pp : PublicParam.{uScalar, uGroup}) (secret : pp.Scalar) :
    Program.runCosted (challengeProgram pp) secret =
      RandCosted.liftCosted
        (Costed.map ULift.up (pp.backend.smul secret pp.generator)) := by
  rfl

/--
Mapping the typed challenge output back to the public challenge package gives
exactly the legacy deterministic compatibility computation.
-/
@[simp] theorem challengeProgram_runCosted_eq_challengeComputation
    (pp : PublicParam.{uScalar, uGroup}) (secret : pp.Scalar) :
  RandCosted.map (fun challenge => ⟨pp, challenge.down⟩)
        (Program.runCosted (challengeProgram pp) secret) =
      RandCosted.liftCosted (challengeComputation pp secret) := by
  simp [challengeProgram_runCosted, challengeComputation,
    RandCosted.map, RandCostedT.map, RandCosted.liftCosted,
    RandCostedT.liftCosted, Costed.map, CostedT.map, PMF.pure_map]

/-- Scalar sampling and challenge generation as one authoritative program. -/
def sampleTailProgram (pp : PublicParam.{uScalar, uGroup}) :
    Program (algebra pp) Unit (ULift.{uScalar} pp.Carrier) where
  body _input :=
    .bind (.call .sampleScalar) fun secret =>
      .call (.smul secret.down pp.generator)

/-- Structural budget certificate for the single DLog tail program. -/
noncomputable def sampleTailBoundedProgram
    (pp : PublicParam.{uScalar, uGroup})
    (certificate : ParamEfficiencyCertificate pp) :
    Program.BoundedProgram
      (Input := Unit) (Output := ULift.{uScalar} pp.Carrier)
      (operationBounds pp certificate)
      (fun _input => certificate.sampleTailBudget) where
  program := sampleTailProgram pp
  certificate := by
    intro input
    simpa [sampleTailProgram,
      ParamEfficiencyCertificate.sampleTailBudget] using
      Program.Code.Bound.bind
        (Program.Code.Bound.call (A := algebra pp) Op.sampleScalar)
        fun (secret : ULift.{uGroup} pp.Scalar) =>
          Program.Code.Bound.call
            (A := algebra pp) (Op.smul secret.down pp.generator)

/-- The scalar-sampling and scalar-action tail at a fixed DLog parameter. -/
noncomputable def sampleTailComputation
    (pp : PublicParam.{uScalar, uGroup}) :
    RandCosted ChallengeInput.{uScalar, uGroup} :=
  RandCosted.map (fun challenge => ⟨pp, challenge.down⟩)
    (Program.runCosted (sampleTailProgram pp) ())

/-- Every fixed-parameter sample tail satisfies its local efficiency certificate. -/
theorem sampleTailComputation_cost_le
    (pp : PublicParam.{uScalar, uGroup})
    (certificate : ParamEfficiencyCertificate pp) :
    ∀ result, result ∈ (sampleTailComputation pp).support →
      result.cost ≤ certificate.sampleTailBudget := by
  intro result hresult
  simp only [sampleTailComputation, RandCosted.map,
    RandCostedT.map] at hresult
  rw [PMF.mem_support_map_iff] at hresult
  rcases hresult with ⟨challengeResult, hchallengeResult, hresult⟩
  subst result
  exact (sampleTailBoundedProgram pp certificate).costBound ()
    challengeResult hchallengeResult

/--
Complete DLog sampling, including setup and all setup-dependent operations, as
one typed program.

There is deliberately no family-wide `OperationBounds`: setup may choose
parameters with different local certificates.  Parameter-local structural
bounds and the existing family `EfficiencyCertificate` remain the separate
upper-bound layer.
-/
def sampleProgram (F : Family.{uScalar, uGroup}) :
    Program (familyAlgebra F) Crypto.SecPar
      ChallengeInput.{uScalar, uGroup} where
  body sec :=
    .bind (.call (.setup sec)) fun pp =>
      .bind (.call (.sampleScalar pp)) fun secret =>
        .bind (.call (.smul pp secret.down pp.generator)) fun challenge =>
          .pure ⟨pp, challenge.down⟩

/-- Native costed sampling for the DLog search problem, including setup. -/
noncomputable def sampleComputation
    (F : Family.{uScalar, uGroup}) (sec : Crypto.SecPar) :
    RandCosted ChallengeInput.{uScalar, uGroup} :=
  Program.runCosted (sampleProgram F) sec

/--
The full typed program is an exact repackaging of setup followed by the
fixed-parameter tail.  In particular, it preserves both values and every path
cost, not only their erasures or upper bounds.
-/
@[simp] theorem sampleProgram_runCosted_eq_bind_tail
    (F : Family.{uScalar, uGroup}) (sec : Crypto.SecPar) :
    Program.runCosted (sampleProgram F) sec =
      RandCosted.bind (F.setup sec) sampleTailComputation := by
  simp only [Program.runCosted, sampleProgram, Program.Code.runCosted,
    familyAlgebra, sampleTailComputation, sampleTailProgram, algebra,
    RandCosted.map, RandCosted.bind, RandCostedT.map, RandCostedT.bind,
    PMF.map_bind, PMF.bind_map, PMF.map_comp, Function.comp_def]
  apply congrArg (PMF.bind (F.setup sec))
  funext setupResult
  cases setupResult with
  | mk pp setupCost =>
      apply congrArg (PMF.bind pp.scalarSampler.sample)
      funext sampleResult
      cases sampleResult with
      | mk secret sampleCost =>
          cases hsmul : pp.backend.smul secret pp.generator with
          | mk smulValue smulCost =>
              have hvalue : smulValue = secret • pp.generator := by
                simpa using (congrArg Costed.val hsmul).symm
              subst smulValue
              simp [RandCosted.liftCosted, RandCostedT.pure,
                RandCostedT.liftCosted, CostedT.bind, CostedT.map,
                CostedT.pure, PMF.pure_map]

/-- Compatibility form of complete DLog sampling for existing bound proofs. -/
@[simp] theorem sampleComputation_eq_bind_tail
    (F : Family.{uScalar, uGroup}) (sec : Crypto.SecPar) :
    sampleComputation F sec =
      RandCosted.bind (F.setup sec) sampleTailComputation := by
  exact sampleProgram_runCosted_eq_bind_tail F sec

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

/-- The same setup certificate bounds the authoritative typed setup program. -/
theorem setupProgram_costBound
    (F : Family.{uScalar, uGroup}) (certificate : EfficiencyCertificate F) :
    Program.CostBound (setupProgram F) certificate.setupBudget := by
  intro sec result hresult
  exact certificate.setupCostBound sec () result hresult

/-- DLog sampling satisfies the supplied global efficiency certificate. -/
theorem sampleComputation_costBound
    (F : Family.{uScalar, uGroup}) (certificate : EfficiencyCertificate F) :
    RandomizedComputation.CostBound
      (fun sec (_input : Unit) => sampleComputation F sec)
      certificate.sampleBudget :=
  certificate.sampleCostBound

/-- The global sample certificate directly bounds the authoritative full program. -/
theorem sampleProgram_costBound
    (F : Family.{uScalar, uGroup}) (certificate : EfficiencyCertificate F) :
    Program.CostBound (sampleProgram F) certificate.sampleBudget := by
  intro sec result hresult
  exact certificate.sampleCostBound sec () result hresult

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
      RandCostedT.liftCosted,
      PMF.mem_support_pure_iff] at hresult
    subst result
    rfl
  sampleBudget :=
    fun _sec => setupCost + paramCertificate.sampleTailBudget
  sampleCostBound := by
    intro sec input result hresult
    change result ∈
      (sampleComputation (Family.ofFixed pp setupCost) sec).support at hresult
    rw [sampleComputation_eq_bind_tail] at hresult
    simp only [RandCosted.bind, RandCostedT.bind] at hresult
    rw [PMF.mem_support_bind_iff] at hresult
    rcases hresult with ⟨setupResult, hsetupResult, htailResult⟩
    rw [PMF.mem_support_map_iff] at htailResult
    rcases htailResult with ⟨tailResult, htailResult, hresult⟩
    subst result
    simp only [Family.ofFixed, RandCosted.liftCosted,
      RandCostedT.liftCosted,
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

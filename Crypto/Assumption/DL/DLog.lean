import Crypto.Assumption.DL.Parameter
import Crypto.Infrastructure.Computation.Algebra.Signature
import Crypto.Infrastructure.Computation.Algebra.Handler
import Crypto.Infrastructure.Computation.Algebra.Laws
import Crypto.Infrastructure.Computation.Algebra.Bounds
import Crypto.Infrastructure.Probability.Uniform
import Crypto.Infrastructure.Computation.Program.Basic
import Crypto.Infrastructure.GameBased.Search

namespace Crypto.Assumption.DL

namespace DLog

open Crypto.Infrastructure.Computation
open Crypto.Infrastructure.Computation.Algebra
open Crypto.Infrastructure.Computation.Cost

universe uCost uAdversaryCost uScalar uGroup

variable
    {M : CostModel.{uCost}}
    {Scalar : Type uScalar}
    {Carrier : Type uGroup}

/-- The mathematical parameter underlying a cost-aware DLog instance. -/
abbrev MathematicalParam (Scalar : Type uScalar) (Carrier : Type uGroup) :=
  Crypto.Assumption.DL.Parameter.CyclicAction Scalar Carrier

/-- Exactly the typed primitive capabilities used by DLog. -/
inductive Op (math : MathematicalParam Scalar Carrier) :
    Type (max uScalar uGroup) → Type (max uScalar uGroup + 1) where
  | sampleScalar : Op math (ULift.{uGroup} math.Scalar)
  | smul (scalar : math.Scalar) (value : math.Carrier) :
      Op math (ULift.{uScalar} math.Carrier)

/-- The dependent typed signature selected by one mathematical parameter. -/
def signature (math : MathematicalParam Scalar Carrier) : Signature where
  Op := Op math

/-- Exact cost-erasure laws for a DLog primitive handler. -/
structure ExactLaws
    {math : MathematicalParam Scalar Carrier}
    (A : CostedAlgebra M (signature math)) : Prop where
  sampleScalar :
    RandCosted.valueDist (A.exec .sampleScalar) =
      PMF.map ULift.up
        (@Crypto.Infrastructure.Probability.uniformPMF
          math.Scalar math.fintypeScalar
          (@Crypto.Assumption.DL.Parameter.scalarNonemptyOfGenerator
            math.Scalar math.Carrier math.addGroup math.smul
            math.generator math.generator_generates))
  smul : ∀ scalar value,
    RandCosted.valueDist (A.exec (.smul scalar value)) =
      PMF.pure (ULift.up (math.smul.smul scalar value))

/--
A cost-aware DLog public parameter.

The mathematical parameter contains no executable data.  This record adds the
single authoritative typed handler and evidence for its cost erasure.
-/
structure PublicParam
    (M : CostModel.{uCost}) (Scalar : Type uScalar) (Carrier : Type uGroup)
    extends MathematicalParam Scalar Carrier where
  algebra : CostedAlgebra M (signature toCyclicAction)
  laws : ExactLaws algebra

namespace PublicParam

abbrev instAddGroup (pp : PublicParam.{uCost, uScalar, uGroup} M Scalar Carrier) : AddGroup pp.Carrier :=
  pp.toCyclicAction.instAddGroup

abbrev instFintypeCarrier (pp : PublicParam.{uCost, uScalar, uGroup} M Scalar Carrier) : Fintype pp.Carrier :=
  pp.toCyclicAction.instFintypeCarrier

abbrev instNonemptyCarrier (pp : PublicParam.{uCost, uScalar, uGroup} M Scalar Carrier) : Nonempty pp.Carrier :=
  pp.toCyclicAction.instNonemptyCarrier

abbrev instFintypeScalar (pp : PublicParam.{uCost, uScalar, uGroup} M Scalar Carrier) : Fintype pp.Scalar :=
  pp.fintypeScalar

abbrev instSMul (pp : PublicParam.{uCost, uScalar, uGroup} M Scalar Carrier) : SMul pp.Scalar pp.Carrier :=
  pp.smul

end PublicParam

scoped[DLogParameter] attribute [instance]
  Crypto.Assumption.DL.DLog.PublicParam.instAddGroup
  Crypto.Assumption.DL.DLog.PublicParam.instFintypeCarrier
  Crypto.Assumption.DL.DLog.PublicParam.instNonemptyCarrier
  Crypto.Assumption.DL.DLog.PublicParam.instFintypeScalar
  Crypto.Assumption.DL.DLog.PublicParam.instSMul

@[instance_reducible] def instNonemptyScalar
    (pp : PublicParam.{uCost, uScalar, uGroup} M Scalar Carrier) : Nonempty pp.Scalar :=
  @Crypto.Assumption.DL.Parameter.scalarNonemptyOfGenerator
    pp.Scalar pp.Carrier pp.addGroup pp.smul
    pp.generator pp.generator_generates

scoped[DLogParameter] attribute [instance]
  Crypto.Assumption.DL.DLog.instNonemptyScalar

open scoped DLogParameter

/-- The standard algebra-law package derived from the exact DLog laws. -/
noncomputable def algebraLaws (pp : PublicParam.{uCost, uScalar, uGroup} M Scalar Carrier) :
    AlgebraLaws pp.algebra where
  semantics operation :=
    match operation with
    | .sampleScalar =>
        PMF.map ULift.up
          (Crypto.Infrastructure.Probability.uniformPMF pp.Scalar)
    | .smul scalar value => PMF.pure (ULift.up (scalar • value))
  exec_spec operation := by
    cases operation with
    | sampleScalar => exact pp.laws.sampleScalar
    | smul scalar value => exact pp.laws.smul scalar value

/--
Uniform upper bounds attached to the exact algebra, not a second interpreter.
-/
structure ParamEfficiencyCertificate (pp : PublicParam.{uCost, uScalar, uGroup} M Scalar Carrier) where
  bounds : OperationBounds pp.algebra
  sampleScalarBudget : M.Cost
  sampleScalarBudget_sound :
    M.instPartialOrder.le (bounds.budget Op.sampleScalar) sampleScalarBudget
  smulBudget : M.Cost
  smulBudget_sound : ∀ scalar value,
    M.instPartialOrder.le (bounds.budget (Op.smul scalar value)) smulBudget

/-- One scalar sample followed by one scalar action. -/
def ParamEfficiencyCertificate.sampleTailBudget
    {pp : PublicParam.{uCost, uScalar, uGroup} M Scalar Carrier}
    (certificate : ParamEfficiencyCertificate pp) : M.Cost :=
  M.instAddMonoid.add certificate.sampleScalarBudget certificate.smulBudget

/-- A security-parameter-indexed family of cost-aware DLog parameters. -/
structure Family
    (M : CostModel.{uCost}) (Scalar : Type uScalar) (Carrier : Type uGroup) where
  setup : Crypto.SecPar →
    RandCosted M (PublicParam.{uCost, uScalar, uGroup} M Scalar Carrier)

/-- A family with one fixed public parameter and an explicit setup cost. -/
noncomputable def Family.ofFixed
    (pp : PublicParam.{uCost, uScalar, uGroup} M Scalar Carrier) (setupCost : M.Cost) :
    Family M Scalar Carrier where
  setup := fun _sec => RandCosted.liftCosted ⟨pp, setupCost⟩

/-- Setup distribution obtained solely by erasing exact costs. -/
noncomputable def Family.setupDist
    (F : Family M Scalar Carrier) (sec : Crypto.SecPar) :
    PMF (PublicParam.{uCost, uScalar, uGroup} M Scalar Carrier) :=
  RandCosted.valueDist (F.setup sec)

/-- Family-level operations for setup-dependent DLog sampling. -/
inductive FamilyOp (F : Family M Scalar Carrier) :
    Type (max uCost (uScalar + 1) (uGroup + 1)) →
      Type (max uCost (uScalar + 1) (uGroup + 1) + 1) where
  | setup (sec : Crypto.SecPar) :
      FamilyOp F (PublicParam.{uCost, uScalar, uGroup} M Scalar Carrier)
  | sampleScalar (pp : PublicParam.{uCost, uScalar, uGroup} M Scalar Carrier) :
      FamilyOp F
        (ULift.{max uCost (uScalar + 1) (uGroup + 1)} pp.Scalar)
  | smul (pp : PublicParam.{uCost, uScalar, uGroup} M Scalar Carrier)
      (scalar : pp.Scalar) (value : pp.Carrier) :
      FamilyOp F
        (ULift.{max uCost (uScalar + 1) (uGroup + 1)} pp.Carrier)

def familySignature (F : Family M Scalar Carrier) : Signature where
  Op := FamilyOp F

/-- The single exact family handler, delegating parameter operations to `pp.algebra`. -/
noncomputable def familyAlgebra (F : Family M Scalar Carrier) :
    CostedAlgebra M (familySignature F) where
  exec operation :=
    match operation with
    | .setup sec => F.setup sec
    | .sampleScalar pp =>
        RandCosted.map (fun result => ULift.up result.down)
          (pp.algebra.exec .sampleScalar)
    | .smul pp scalar value =>
        RandCosted.map (fun result => ULift.up result.down)
          (pp.algebra.exec (.smul scalar value))

/-- Cost-erased specifications for setup and delegated DLog operations. -/
noncomputable def familyAlgebraLaws (F : Family M Scalar Carrier) :
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
    | sampleScalar pp => simp [familyAlgebra, (algebraLaws pp).exec_spec]
    | smul pp scalar value => simp [familyAlgebra, (algebraLaws pp).exec_spec]

/-- Setup as a typed family-level program. -/
def setupProgram (F : Family M Scalar Carrier) :
    Program (familyAlgebra F) Crypto.SecPar
      (PublicParam.{uCost, uScalar, uGroup} M Scalar Carrier) where
  body sec := .call (.setup sec)

@[simp] theorem setupProgram_runCosted
    (F : Family M Scalar Carrier) (sec : Crypto.SecPar) :
    Program.runCosted (setupProgram F) sec = F.setup sec :=
  rfl

/-- Input to a DLog adversary. -/
abbrev ChallengeInput
    (M : CostModel.{uCost}) (Scalar : Type uScalar) (Carrier : Type uGroup) :=
  Sigma fun pp : PublicParam.{uCost, uScalar, uGroup} M Scalar Carrier => pp.Carrier

/-- A candidate discrete-log witness. -/
abbrev Witness (challenge : ChallengeInput.{uCost, uScalar, uGroup} M Scalar Carrier) :=
  challenge.1.Scalar

def IsSolution (challenge : ChallengeInput.{uCost, uScalar, uGroup} M Scalar Carrier)
    (witness : Witness challenge) : Prop :=
  witness • challenge.1.generator = challenge.2

noncomputable instance instDecidableIsSolution
    (challenge : ChallengeInput.{uCost, uScalar, uGroup} M Scalar Carrier)
    (witness : Witness challenge) :
    Decidable (IsSolution challenge witness) :=
  Classical.propDecidable _

/-- Fixed-secret DLog challenge generation. -/
def challengeProgram (pp : PublicParam.{uCost, uScalar, uGroup} M Scalar Carrier) :
    Program pp.algebra pp.Scalar (ULift.{uScalar} pp.Carrier) where
  body secret := .call (.smul secret pp.generator)

/-- Scalar sampling followed by challenge generation. -/
def sampleTailProgram (pp : PublicParam.{uCost, uScalar, uGroup} M Scalar Carrier) :
    Program pp.algebra Unit (ULift.{uScalar} pp.Carrier) where
  body _input :=
    .bind (.call .sampleScalar) fun secret =>
      .call (.smul secret.down pp.generator)

/-- Structural bound for the exact DLog tail program. -/
noncomputable def sampleTailBoundedProgram
    (pp : PublicParam.{uCost, uScalar, uGroup} M Scalar Carrier)
    (certificate : ParamEfficiencyCertificate pp) :
    Program.BoundedProgram
      (Input := Unit) (Output := ULift.{uScalar} pp.Carrier)
      certificate.bounds (fun _ => certificate.sampleTailBudget) where
  program := sampleTailProgram pp
  certificate := by
    intro input
    simpa [sampleTailProgram,
      ParamEfficiencyCertificate.sampleTailBudget] using
      Program.Code.Bound.bind
        (Program.Code.Bound.weaken
          (Program.Code.Bound.call
            (bounds := certificate.bounds) Op.sampleScalar)
          certificate.sampleScalarBudget_sound)
        fun (secret : ULift.{uGroup} pp.Scalar) =>
          Program.Code.Bound.weaken
            (Program.Code.Bound.call
              (bounds := certificate.bounds)
              (Op.smul secret.down pp.generator))
            (certificate.smulBudget_sound secret.down pp.generator)

/-- Complete setup-dependent DLog sampling. -/
def sampleProgram (F : Family M Scalar Carrier) :
    Program (familyAlgebra F) Crypto.SecPar
      (ChallengeInput.{uCost, uScalar, uGroup} M Scalar Carrier) where
  body sec :=
    .bind (.call (.setup sec)) fun pp =>
      .bind (.call (.sampleScalar pp)) fun secret =>
        .bind (.call (.smul pp secret.down pp.generator)) fun challenge =>
          .pure ⟨pp, challenge.down⟩

/-- The mathematical DLog distribution is exactly cost erasure of `sampleProgram`. -/
noncomputable def sampleDist
    (F : Family M Scalar Carrier) (sec : Crypto.SecPar) :
    PMF (ChallengeInput.{uCost, uScalar, uGroup} M Scalar Carrier) :=
  Program.valueDist (sampleProgram F) sec

/-- Global bounds attach directly to the two authoritative programs. -/
structure EfficiencyCertificate (F : Family M Scalar Carrier) where
  setupBudget : Crypto.SecPar → M.Cost
  setupCostBound : Program.CostBound (setupProgram F) setupBudget
  sampleBudget : Crypto.SecPar → M.Cost
  sampleCostBound : Program.CostBound (sampleProgram F) sampleBudget

theorem setupProgram_costBound
    (F : Family M Scalar Carrier)
    (certificate : EfficiencyCertificate F) :
    Program.CostBound (setupProgram F) certificate.setupBudget :=
  certificate.setupCostBound

theorem sampleProgram_costBound
    (F : Family M Scalar Carrier)
    (certificate : EfficiencyCertificate F) :
    Program.CostBound (sampleProgram F) certificate.sampleBudget :=
  certificate.sampleCostBound

/-- The search problem induced by a cost-aware DLog family. -/
noncomputable def dLogProblem (F : Family M Scalar Carrier) :
    Crypto.Infrastructure.GameBased.Search.Problem
      (ChallengeInput.{uCost, uScalar, uGroup} M Scalar Carrier) where
  Witness := Witness
  sample := sampleDist F
  relation := IsSolution
  decidableRelation := instDecidableIsSolution

/--
The discrete-log assumption against every PPT adversary measured in the
explicit adversary cost model.  The family handler's exact cost model remains
independent of the adversary model.
-/
def Assumption
    (adversaryModel : CostModel.{uAdversaryCost})
    (measure : NatMeasure adversaryModel)
    (F : Family M Scalar Carrier) : Prop :=
  Crypto.Infrastructure.GameBased.Search.Hard
    adversaryModel measure (dLogProblem F)

end DLog

end Crypto.Assumption.DL

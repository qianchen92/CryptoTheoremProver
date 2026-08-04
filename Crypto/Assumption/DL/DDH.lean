import Crypto.Assumption.DL.Parameter
import Crypto.Infrastructure.Computation.Algebra.Signature
import Crypto.Infrastructure.Computation.Algebra.Handler
import Crypto.Infrastructure.Computation.Algebra.Laws
import Crypto.Infrastructure.Computation.Algebra.Bounds
import Crypto.Infrastructure.Probability.Uniform
import Crypto.Infrastructure.Computation.Program.Basic
import Crypto.Infrastructure.GameBased.Distinguishing

namespace Crypto.Assumption.DL

namespace DDH

open Crypto.Infrastructure.Computation
open Crypto.Infrastructure.Computation.Algebra
open Crypto.Infrastructure.Computation.Cost

universe uCost uAdversaryCost uScalar uGroup

variable {M : CostModel.{uCost}}

/-- The mathematical parameter underlying a cost-aware DDH instance. -/
abbrev MathematicalParam :=
  Crypto.Assumption.DL.Parameter.DecisionalCyclicAction.{uScalar, uGroup}

/--
The typed primitive capabilities carried by a DDH parameter.  Carrier addition
and subtraction let ElGamal reuse this same exact handler instead of installing
a second source of primitive costs.
-/
inductive Op (math : MathematicalParam.{uScalar, uGroup}) :
    Type (max uScalar uGroup) → Type (max uScalar uGroup + 1) where
  | sampleScalar : Op math (ULift.{uGroup} math.Scalar)
  | sampleCarrier : Op math (ULift.{uScalar} math.Carrier)
  | smul (scalar : math.Scalar) (value : math.Carrier) :
      Op math (ULift.{uScalar} math.Carrier)
  | add (left right : math.Carrier) :
      Op math (ULift.{uScalar} math.Carrier)
  | sub (left right : math.Carrier) :
      Op math (ULift.{uScalar} math.Carrier)
  | mul (left right : math.Scalar) : Op math (ULift.{uGroup} math.Scalar)

def signature (math : MathematicalParam.{uScalar, uGroup}) : Signature where
  Op := Op math

/-- Exact cost-erasure laws for a DDH primitive handler. -/
structure ExactLaws
    {math : MathematicalParam.{uScalar, uGroup}}
    (A : CostedAlgebra M (signature math)) : Prop where
  sampleScalar :
    RandCosted.valueDist (A.exec .sampleScalar) =
      PMF.map ULift.up
        (@Crypto.Infrastructure.Probability.uniformPMF
          math.Scalar math.fintypeScalar
          ⟨math.commMonoidScalar.one⟩)
  sampleCarrier :
    RandCosted.valueDist (A.exec .sampleCarrier) =
      PMF.map ULift.up
        (@Crypto.Infrastructure.Probability.uniformPMF
          math.Carrier math.fintypeCarrier ⟨math.addGroup.zero⟩)
  smul : ∀ scalar value,
    RandCosted.valueDist (A.exec (.smul scalar value)) =
      PMF.pure (ULift.up (math.smul.smul scalar value))
  add : ∀ left right,
    RandCosted.valueDist (A.exec (.add left right)) =
      PMF.pure (ULift.up (math.addGroup.add left right))
  sub : ∀ left right,
    RandCosted.valueDist (A.exec (.sub left right)) =
      PMF.pure (ULift.up (math.addGroup.sub left right))
  mul : ∀ left right,
    RandCosted.valueDist (A.exec (.mul left right)) =
      PMF.pure (ULift.up (math.commMonoidScalar.mul left right))

/-- A mathematical DDH parameter plus its single authoritative exact handler. -/
structure PublicParam (M : CostModel.{uCost}) extends
    MathematicalParam.{uScalar, uGroup} where
  algebra : CostedAlgebra M (signature toDecisionalCyclicAction)
  laws : ExactLaws algebra

namespace PublicParam

abbrev instAddGroup (pp : PublicParam.{uCost, uScalar, uGroup} M) : AddGroup pp.Carrier :=
  pp.toDecisionalCyclicAction.instAddGroup

abbrev instFintypeCarrier (pp : PublicParam.{uCost, uScalar, uGroup} M) : Fintype pp.Carrier :=
  pp.toDecisionalCyclicAction.instFintypeCarrier

abbrev instNonemptyCarrier (pp : PublicParam.{uCost, uScalar, uGroup} M) : Nonempty pp.Carrier :=
  pp.toDecisionalCyclicAction.instNonemptyCarrier

abbrev instFintypeScalar (pp : PublicParam.{uCost, uScalar, uGroup} M) : Fintype pp.Scalar :=
  pp.fintypeScalar

abbrev instSMul (pp : PublicParam.{uCost, uScalar, uGroup} M) : SMul pp.Scalar pp.Carrier :=
  pp.smul

abbrev instCommMonoidScalar (pp : PublicParam.{uCost, uScalar, uGroup} M) : CommMonoid pp.Scalar :=
  pp.commMonoidScalar

@[instance_reducible] def instMulAction
    (pp : PublicParam.{uCost, uScalar, uGroup} M) :
    @MulAction pp.Scalar pp.Carrier pp.commMonoidScalar.toMonoid :=
  pp.toDecisionalCyclicAction.mulAction

end PublicParam

scoped[DDHParameter] attribute [instance]
  Crypto.Assumption.DL.DDH.PublicParam.instAddGroup
  Crypto.Assumption.DL.DDH.PublicParam.instFintypeCarrier
  Crypto.Assumption.DL.DDH.PublicParam.instNonemptyCarrier
  Crypto.Assumption.DL.DDH.PublicParam.instFintypeScalar
  Crypto.Assumption.DL.DDH.PublicParam.instSMul
  Crypto.Assumption.DL.DDH.PublicParam.instCommMonoidScalar
  Crypto.Assumption.DL.DDH.PublicParam.instMulAction

@[instance_reducible] def instNonemptyScalar
    (pp : PublicParam.{uCost, uScalar, uGroup} M) :
    Nonempty pp.Scalar :=
  ⟨pp.commMonoidScalar.one⟩

scoped[DDHParameter] attribute [instance]
  Crypto.Assumption.DL.DDH.instNonemptyScalar

open scoped DDHParameter

@[simp] theorem PublicParam.mulScalarAction
    (pp : PublicParam.{uCost, uScalar, uGroup} M)
    (leftExp rightExp : pp.Scalar) :
    (leftExp * rightExp) • pp.generator =
      leftExp • (rightExp • pp.generator) :=
  pp.mul_smul leftExp rightExp pp.generator

theorem PublicParam.scalarAction_commutes
    (pp : PublicParam.{uCost, uScalar, uGroup} M)
    (leftExp rightExp : pp.Scalar) :
    leftExp • (rightExp • pp.generator) =
      rightExp • (leftExp • pp.generator) := by
  letI : CommMonoid pp.Scalar := pp.commMonoidScalar
  letI : SMul pp.Scalar pp.Carrier := pp.smul
  calc
    leftExp • (rightExp • pp.generator) =
        (leftExp * rightExp) • pp.generator :=
      (pp.mul_smul leftExp rightExp pp.generator).symm
    _ = (rightExp * leftExp) • pp.generator := by rw [mul_comm]
    _ = rightExp • (leftExp • pp.generator) :=
      pp.mul_smul rightExp leftExp pp.generator

/-- The standard algebra-law package derived from exact DDH laws. -/
noncomputable def algebraLaws (pp : PublicParam.{uCost, uScalar, uGroup} M) :
    AlgebraLaws pp.algebra where
  semantics operation :=
    match operation with
    | .sampleScalar =>
        PMF.map ULift.up
          (Crypto.Infrastructure.Probability.uniformPMF pp.Scalar)
    | .sampleCarrier =>
        PMF.map ULift.up
          (Crypto.Infrastructure.Probability.uniformPMF pp.Carrier)
    | .smul scalar value => PMF.pure (ULift.up (scalar • value))
    | .add left right => PMF.pure (ULift.up (left + right))
    | .sub left right => PMF.pure (ULift.up (left - right))
    | .mul left right => PMF.pure (ULift.up (left * right))
  exec_spec operation := by
    cases operation with
    | sampleScalar => exact pp.laws.sampleScalar
    | sampleCarrier => exact pp.laws.sampleCarrier
    | smul scalar value => exact pp.laws.smul scalar value
    | add left right => exact pp.laws.add left right
    | sub left right => exact pp.laws.sub left right
    | mul left right => exact pp.laws.mul left right

/-- Uniform upper bounds attached to one exact DDH algebra. -/
structure ParamEfficiencyCertificate (pp : PublicParam.{uCost, uScalar, uGroup} M) where
  bounds : OperationBounds pp.algebra
  scalarSampleBudget : M.Cost
  scalarSampleBudget_sound :
    M.instPartialOrder.le (bounds.budget Op.sampleScalar) scalarSampleBudget
  carrierSampleBudget : M.Cost
  carrierSampleBudget_sound :
    M.instPartialOrder.le (bounds.budget Op.sampleCarrier) carrierSampleBudget
  smulBudget : M.Cost
  smulBudget_sound : ∀ scalar value,
    M.instPartialOrder.le (bounds.budget (Op.smul scalar value)) smulBudget
  addBudget : M.Cost
  addBudget_sound : ∀ left right,
    M.instPartialOrder.le (bounds.budget (Op.add left right)) addBudget
  subBudget : M.Cost
  subBudget_sound : ∀ left right,
    M.instPartialOrder.le (bounds.budget (Op.sub left right)) subBudget
  mulBudget : M.Cost
  mulBudget_sound : ∀ left right,
    M.instPartialOrder.le (bounds.budget (Op.mul left right)) mulBudget

namespace ParamEfficiencyCertificate

variable {pp : PublicParam.{uCost, uScalar, uGroup} M}

def realChallengeBudget
    (c : ParamEfficiencyCertificate pp) : M.Cost :=
  M.instAddMonoid.add c.smulBudget
    (M.instAddMonoid.add c.smulBudget
      (M.instAddMonoid.add c.mulBudget
        (M.instAddMonoid.add c.smulBudget M.instAddMonoid.zero)))

def realSampleTailBudget
    (c : ParamEfficiencyCertificate pp) : M.Cost :=
  M.instAddMonoid.add c.scalarSampleBudget
    (M.instAddMonoid.add c.scalarSampleBudget c.realChallengeBudget)

def randomChallengeBudget
    (c : ParamEfficiencyCertificate pp) : M.Cost :=
  M.instAddMonoid.add c.smulBudget
    (M.instAddMonoid.add c.smulBudget M.instAddMonoid.zero)

def randomSampleTailBudget
    (c : ParamEfficiencyCertificate pp) : M.Cost :=
  M.instAddMonoid.add c.scalarSampleBudget
    (M.instAddMonoid.add c.scalarSampleBudget
      (M.instAddMonoid.add c.carrierSampleBudget c.randomChallengeBudget))

end ParamEfficiencyCertificate

/-- A security-parameter-indexed family of cost-aware DDH parameters. -/
structure Family (M : CostModel.{uCost}) where
  setup : Crypto.SecPar →
    RandCosted M (PublicParam.{uCost, uScalar, uGroup} M)

noncomputable def Family.ofFixed
    (pp : PublicParam.{uCost, uScalar, uGroup} M) (setupCost : M.Cost) :
    Family.{uCost, uScalar, uGroup} M where
  setup := fun _sec => RandCosted.liftCosted ⟨pp, setupCost⟩

noncomputable def Family.setupDist
    (F : Family.{uCost, uScalar, uGroup} M) (sec : Crypto.SecPar) :
    PMF (PublicParam.{uCost, uScalar, uGroup} M) :=
  RandCosted.valueDist (F.setup sec)

/-- Family-level operations for setup-dependent DDH sampling. -/
inductive FamilyOp (F : Family.{uCost, uScalar, uGroup} M) :
    Type (max uCost (uScalar + 1) (uGroup + 1)) →
      Type (max uCost (uScalar + 1) (uGroup + 1) + 1) where
  | setup (sec : Crypto.SecPar) :
      FamilyOp F (PublicParam.{uCost, uScalar, uGroup} M)
  | sampleScalar (pp : PublicParam.{uCost, uScalar, uGroup} M) :
      FamilyOp F
        (ULift.{max uCost (uScalar + 1) (uGroup + 1)} pp.Scalar)
  | sampleCarrier (pp : PublicParam.{uCost, uScalar, uGroup} M) :
      FamilyOp F
        (ULift.{max uCost (uScalar + 1) (uGroup + 1)} pp.Carrier)
  | smul (pp : PublicParam.{uCost, uScalar, uGroup} M)
      (scalar : pp.Scalar) (value : pp.Carrier) :
      FamilyOp F
        (ULift.{max uCost (uScalar + 1) (uGroup + 1)} pp.Carrier)
  | add (pp : PublicParam.{uCost, uScalar, uGroup} M)
      (left right : pp.Carrier) :
      FamilyOp F
        (ULift.{max uCost (uScalar + 1) (uGroup + 1)} pp.Carrier)
  | sub (pp : PublicParam.{uCost, uScalar, uGroup} M)
      (left right : pp.Carrier) :
      FamilyOp F
        (ULift.{max uCost (uScalar + 1) (uGroup + 1)} pp.Carrier)
  | mul (pp : PublicParam.{uCost, uScalar, uGroup} M)
      (left right : pp.Scalar) :
      FamilyOp F
        (ULift.{max uCost (uScalar + 1) (uGroup + 1)} pp.Scalar)

def familySignature (F : Family.{uCost, uScalar, uGroup} M) : Signature where
  Op := FamilyOp F

noncomputable def familyAlgebra (F : Family.{uCost, uScalar, uGroup} M) :
    CostedAlgebra M (familySignature F) where
  exec operation :=
    match operation with
    | .setup sec => F.setup sec
    | .sampleScalar pp =>
        RandCosted.map (fun result => ULift.up result.down)
          (pp.algebra.exec .sampleScalar)
    | .sampleCarrier pp =>
        RandCosted.map (fun result => ULift.up result.down)
          (pp.algebra.exec .sampleCarrier)
    | .smul pp scalar value =>
        RandCosted.map (fun result => ULift.up result.down)
          (pp.algebra.exec (.smul scalar value))
    | .add pp left right =>
        RandCosted.map (fun result => ULift.up result.down)
          (pp.algebra.exec (.add left right))
    | .sub pp left right =>
        RandCosted.map (fun result => ULift.up result.down)
          (pp.algebra.exec (.sub left right))
    | .mul pp left right =>
        RandCosted.map (fun result => ULift.up result.down)
          (pp.algebra.exec (.mul left right))

noncomputable def familyAlgebraLaws
    (F : Family.{uCost, uScalar, uGroup} M) :
    AlgebraLaws (familyAlgebra F) where
  semantics operation :=
    match operation with
    | .setup sec => F.setupDist sec
    | .sampleScalar pp =>
        PMF.map (fun result => ULift.up result.down)
          ((algebraLaws pp).semantics Op.sampleScalar)
    | .sampleCarrier pp =>
        PMF.map (fun result => ULift.up result.down)
          ((algebraLaws pp).semantics Op.sampleCarrier)
    | .smul pp scalar value =>
        PMF.map (fun result => ULift.up result.down)
          ((algebraLaws pp).semantics (Op.smul scalar value))
    | .add pp left right =>
        PMF.map (fun result => ULift.up result.down)
          ((algebraLaws pp).semantics (Op.add left right))
    | .sub pp left right =>
        PMF.map (fun result => ULift.up result.down)
          ((algebraLaws pp).semantics (Op.sub left right))
    | .mul pp left right =>
        PMF.map (fun result => ULift.up result.down)
          ((algebraLaws pp).semantics (Op.mul left right))
  exec_spec operation := by
    cases operation with
    | setup sec => rfl
    | sampleScalar pp => simp [familyAlgebra, (algebraLaws pp).exec_spec]
    | sampleCarrier pp => simp [familyAlgebra, (algebraLaws pp).exec_spec]
    | smul pp scalar value => simp [familyAlgebra, (algebraLaws pp).exec_spec]
    | add pp left right => simp [familyAlgebra, (algebraLaws pp).exec_spec]
    | sub pp left right => simp [familyAlgebra, (algebraLaws pp).exec_spec]
    | mul pp left right => simp [familyAlgebra, (algebraLaws pp).exec_spec]

def setupProgram (F : Family.{uCost, uScalar, uGroup} M) :
    Program (familyAlgebra F) Crypto.SecPar
      (PublicParam.{uCost, uScalar, uGroup} M) where
  body sec := .call (.setup sec)

@[simp] theorem setupProgram_runCosted
    (F : Family.{uCost, uScalar, uGroup} M) (sec : Crypto.SecPar) :
    Program.runCosted (setupProgram F) sec = F.setup sec :=
  rfl

/-- A DDH challenge consists of parameters and three carrier elements. -/
structure ChallengeInput (M : CostModel.{uCost}) where
  param : PublicParam.{uCost, uScalar, uGroup} M
  left : param.Carrier
  right : param.Carrier
  shared : param.Carrier

structure ChallengeValues (pp : PublicParam.{uCost, uScalar, uGroup} M) where
  left : pp.Carrier
  right : pp.Carrier
  shared : pp.Carrier

def ChallengeValues.toChallengeInput
    {pp : PublicParam.{uCost, uScalar, uGroup} M}
    (values : ChallengeValues pp) :
    ChallengeInput.{uCost, uScalar, uGroup} M where
  param := pp
  left := values.left
  right := values.right
  shared := values.shared

def realChallenge (pp : PublicParam.{uCost, uScalar, uGroup} M)
    (leftExp rightExp : pp.Scalar) :
    ChallengeInput.{uCost, uScalar, uGroup} M where
  param := pp
  left := leftExp • pp.generator
  right := rightExp • pp.generator
  shared := (leftExp * rightExp) • pp.generator

@[simp] theorem realChallenge_shared_eq_nestedAction
    (pp : PublicParam.{uCost, uScalar, uGroup} M)
    (leftExp rightExp : pp.Scalar) :
    (realChallenge pp leftExp rightExp).shared =
      leftExp • (rightExp • pp.generator) :=
  pp.mulScalarAction leftExp rightExp

def randomChallenge (pp : PublicParam.{uCost, uScalar, uGroup} M)
    (leftExp rightExp : pp.Scalar) (shared : pp.Carrier) :
    ChallengeInput.{uCost, uScalar, uGroup} M where
  param := pp
  left := leftExp • pp.generator
  right := rightExp • pp.generator
  shared := shared

/-- Genuine tuple construction as a typed program. -/
def realChallengeProgram (pp : PublicParam.{uCost, uScalar, uGroup} M) :
    Program pp.algebra (pp.Scalar × pp.Scalar)
      (ULift.{uScalar} (ChallengeValues pp)) where
  body input :=
    .bind (.call (.smul input.1 pp.generator)) fun left =>
      .bind (.call (.smul input.2 pp.generator)) fun right =>
        .bind (.call (.mul input.1 input.2)) fun product =>
          .bind (.call (.smul product.down pp.generator)) fun shared =>
            .pure (ULift.up {
              left := left.down
              right := right.down
              shared := shared.down })

/-- Random tuple construction as a typed program. -/
def randomChallengeProgram (pp : PublicParam.{uCost, uScalar, uGroup} M) :
    Program pp.algebra (pp.Scalar × pp.Scalar × pp.Carrier)
      (ULift.{uScalar} (ChallengeValues pp)) where
  body input :=
    .bind (.call (.smul input.1 pp.generator)) fun left =>
      .bind (.call (.smul input.2.1 pp.generator)) fun right =>
        .pure (ULift.up {
          left := left.down
          right := right.down
          shared := input.2.2 })

noncomputable def realChallengeBoundedProgram
    (pp : PublicParam.{uCost, uScalar, uGroup} M)
    (c : ParamEfficiencyCertificate pp) :
    Program.BoundedProgram
      (Input := pp.Scalar × pp.Scalar)
      (Output := ULift.{uScalar} (ChallengeValues pp)) c.bounds
      (fun _ => c.realChallengeBudget) where
  program := realChallengeProgram pp
  certificate := by
    letI := M.instAddMonoid
    intro input
    simpa [realChallengeProgram,
      ParamEfficiencyCertificate.realChallengeBudget] using
      Program.Code.Bound.bind
        (Program.Code.Bound.weaken
          (Program.Code.Bound.call (bounds := c.bounds)
            (Op.smul input.1 pp.generator))
          (c.smulBudget_sound input.1 pp.generator))
        fun (left : ULift.{uScalar} pp.Carrier) =>
          Program.Code.Bound.bind
            (Program.Code.Bound.weaken
              (Program.Code.Bound.call (bounds := c.bounds)
                (Op.smul input.2 pp.generator))
              (c.smulBudget_sound input.2 pp.generator))
            fun (right : ULift.{uScalar} pp.Carrier) =>
              Program.Code.Bound.bind
                (Program.Code.Bound.weaken
                  (Program.Code.Bound.call (bounds := c.bounds)
                    (Op.mul input.1 input.2))
                  (c.mulBudget_sound input.1 input.2))
                fun (product : ULift.{uGroup} pp.Scalar) =>
                  Program.Code.Bound.bind
                    (Program.Code.Bound.weaken
                      (Program.Code.Bound.call (bounds := c.bounds)
                        (Op.smul product.down pp.generator))
                      (c.smulBudget_sound product.down pp.generator))
                    fun (shared : ULift.{uScalar} pp.Carrier) =>
                      Program.Code.Bound.pure
                        (A := pp.algebra)
                        (ULift.up ({
                          left := left.down
                          right := right.down
                          shared := shared.down } : ChallengeValues pp))

noncomputable def randomChallengeBoundedProgram
    (pp : PublicParam.{uCost, uScalar, uGroup} M)
    (c : ParamEfficiencyCertificate pp) :
    Program.BoundedProgram
      (Input := pp.Scalar × pp.Scalar × pp.Carrier)
      (Output := ULift.{uScalar} (ChallengeValues pp)) c.bounds
      (fun _ => c.randomChallengeBudget) where
  program := randomChallengeProgram pp
  certificate := by
    letI := M.instAddMonoid
    intro input
    simpa [randomChallengeProgram,
      ParamEfficiencyCertificate.randomChallengeBudget] using
      Program.Code.Bound.bind
        (Program.Code.Bound.weaken
          (Program.Code.Bound.call (bounds := c.bounds)
            (Op.smul input.1 pp.generator))
          (c.smulBudget_sound input.1 pp.generator))
        fun (left : ULift.{uScalar} pp.Carrier) =>
          Program.Code.Bound.bind
            (Program.Code.Bound.weaken
              (Program.Code.Bound.call (bounds := c.bounds)
                (Op.smul input.2.1 pp.generator))
              (c.smulBudget_sound input.2.1 pp.generator))
            fun (right : ULift.{uScalar} pp.Carrier) =>
              Program.Code.Bound.pure
                (A := pp.algebra)
                (ULift.up ({
                  left := left.down
                  right := right.down
                  shared := input.2.2 } : ChallengeValues pp))

/-- Genuine local sampling path. -/
def realSampleTailProgram (pp : PublicParam.{uCost, uScalar, uGroup} M) :
    Program pp.algebra Unit (ULift.{uScalar} (ChallengeValues pp)) where
  body _input :=
    .bind (.call .sampleScalar) fun leftExp =>
      .bind (.call .sampleScalar) fun rightExp =>
        (realChallengeProgram pp).body (leftExp.down, rightExp.down)

/-- Random local sampling path. -/
def randomSampleTailProgram (pp : PublicParam.{uCost, uScalar, uGroup} M) :
    Program pp.algebra Unit (ULift.{uScalar} (ChallengeValues pp)) where
  body _input :=
    .bind (.call .sampleScalar) fun leftExp =>
      .bind (.call .sampleScalar) fun rightExp =>
        .bind (.call .sampleCarrier) fun shared =>
          (randomChallengeProgram pp).body
            (leftExp.down, rightExp.down, shared.down)

noncomputable def realSampleTailBoundedProgram
    (pp : PublicParam.{uCost, uScalar, uGroup} M)
    (c : ParamEfficiencyCertificate pp) :
    Program.BoundedProgram
      (Input := Unit) (Output := ULift.{uScalar} (ChallengeValues pp))
      c.bounds (fun _ => c.realSampleTailBudget) where
  program := realSampleTailProgram pp
  certificate := by
    intro input
    simpa [realSampleTailProgram,
      ParamEfficiencyCertificate.realSampleTailBudget] using
      Program.Code.Bound.bind
        (Program.Code.Bound.weaken
          (Program.Code.Bound.call (bounds := c.bounds) Op.sampleScalar)
          c.scalarSampleBudget_sound)
        fun (leftExp : ULift.{uGroup} pp.Scalar) =>
          Program.Code.Bound.bind
            (Program.Code.Bound.weaken
              (Program.Code.Bound.call (bounds := c.bounds) Op.sampleScalar)
              c.scalarSampleBudget_sound)
            fun (rightExp : ULift.{uGroup} pp.Scalar) =>
              (realChallengeBoundedProgram pp c).certificate
                (leftExp.down, rightExp.down)

noncomputable def randomSampleTailBoundedProgram
    (pp : PublicParam.{uCost, uScalar, uGroup} M)
    (c : ParamEfficiencyCertificate pp) :
    Program.BoundedProgram
      (Input := Unit) (Output := ULift.{uScalar} (ChallengeValues pp))
      c.bounds (fun _ => c.randomSampleTailBudget) where
  program := randomSampleTailProgram pp
  certificate := by
    intro input
    simpa [randomSampleTailProgram,
      ParamEfficiencyCertificate.randomSampleTailBudget] using
      Program.Code.Bound.bind
        (Program.Code.Bound.weaken
          (Program.Code.Bound.call (bounds := c.bounds) Op.sampleScalar)
          c.scalarSampleBudget_sound)
        fun (leftExp : ULift.{uGroup} pp.Scalar) =>
          Program.Code.Bound.bind
            (Program.Code.Bound.weaken
              (Program.Code.Bound.call (bounds := c.bounds) Op.sampleScalar)
              c.scalarSampleBudget_sound)
            fun (rightExp : ULift.{uGroup} pp.Scalar) =>
              Program.Code.Bound.bind
                (Program.Code.Bound.weaken
                  (Program.Code.Bound.call (bounds := c.bounds) Op.sampleCarrier)
                  c.carrierSampleBudget_sound)
                fun (shared : ULift.{uScalar} pp.Carrier) =>
                  (randomChallengeBoundedProgram pp c).certificate
                    (leftExp.down, rightExp.down, shared.down)

/-- Complete genuine-DDH sampling. -/
def realSampleProgram (F : Family.{uCost, uScalar, uGroup} M) :
    Program (familyAlgebra F) Crypto.SecPar
      (ChallengeInput.{uCost, uScalar, uGroup} M) where
  body sec :=
    .bind (.call (.setup sec)) fun pp =>
      .bind (.call (.sampleScalar pp)) fun leftExp =>
        .bind (.call (.sampleScalar pp)) fun rightExp =>
          .bind (.call (.smul pp leftExp.down pp.generator)) fun left =>
            .bind (.call (.smul pp rightExp.down pp.generator)) fun right =>
              .bind (.call (.mul pp leftExp.down rightExp.down)) fun product =>
                .bind (.call (.smul pp product.down pp.generator)) fun shared =>
                  .pure {
                    param := pp
                    left := left.down
                    right := right.down
                    shared := shared.down }

/-- Complete random-DDH sampling. -/
def randomSampleProgram (F : Family.{uCost, uScalar, uGroup} M) :
    Program (familyAlgebra F) Crypto.SecPar
      (ChallengeInput.{uCost, uScalar, uGroup} M) where
  body sec :=
    .bind (.call (.setup sec)) fun pp =>
      .bind (.call (.sampleScalar pp)) fun leftExp =>
        .bind (.call (.sampleScalar pp)) fun rightExp =>
          .bind (.call (.sampleCarrier pp)) fun sampledShared =>
            .bind (.call (.smul pp leftExp.down pp.generator)) fun left =>
              .bind (.call (.smul pp rightExp.down pp.generator)) fun right =>
                .pure {
                  param := pp
                  left := left.down
                  right := right.down
                  shared := sampledShared.down }

noncomputable def realSample (F : Family.{uCost, uScalar, uGroup} M) :
    Crypto.SecPar → PMF (ChallengeInput.{uCost, uScalar, uGroup} M) :=
  fun sec => Program.valueDist (realSampleProgram F) sec

noncomputable def randomSample (F : Family.{uCost, uScalar, uGroup} M) :
    Crypto.SecPar → PMF (ChallengeInput.{uCost, uScalar, uGroup} M) :=
  fun sec => Program.valueDist (randomSampleProgram F) sec

/-- Global bounds attach directly to the authoritative DDH programs. -/
structure EfficiencyCertificate (F : Family.{uCost, uScalar, uGroup} M) where
  setupBudget : Crypto.SecPar → M.Cost
  setupCostBound : Program.CostBound (setupProgram F) setupBudget
  realSampleBudget : Crypto.SecPar → M.Cost
  realSampleCostBound : Program.CostBound (realSampleProgram F) realSampleBudget
  randomSampleBudget : Crypto.SecPar → M.Cost
  randomSampleCostBound : Program.CostBound (randomSampleProgram F) randomSampleBudget

theorem setupProgram_costBound
    (F : Family.{uCost, uScalar, uGroup} M)
    (certificate : EfficiencyCertificate F) :
    Program.CostBound (setupProgram F) certificate.setupBudget :=
  certificate.setupCostBound

theorem realSampleProgram_costBound
    (F : Family.{uCost, uScalar, uGroup} M)
    (certificate : EfficiencyCertificate F) :
    Program.CostBound (realSampleProgram F) certificate.realSampleBudget :=
  certificate.realSampleCostBound

theorem randomSampleProgram_costBound
    (F : Family.{uCost, uScalar, uGroup} M)
    (certificate : EfficiencyCertificate F) :
    Program.CostBound (randomSampleProgram F) certificate.randomSampleBudget :=
  certificate.randomSampleCostBound

/-- The distinguishing problem induced by a cost-aware DDH family. -/
noncomputable def ddhProblem (F : Family.{uCost, uScalar, uGroup} M) :
    Crypto.Infrastructure.GameBased.Distinguishing.Problem
      (ChallengeInput.{uCost, uScalar, uGroup} M) where
  left := realSample F
  right := randomSample F

/--
The DDH assumption against every PPT adversary measured in the explicit
adversary cost model.  The family handler's exact cost model remains
independent of the adversary model.
-/
def Assumption
    (adversaryModel : CostModel.{uAdversaryCost})
    (measure : NatMeasure adversaryModel)
    (F : Family.{uCost, uScalar, uGroup} M) : Prop :=
  Crypto.Infrastructure.GameBased.Distinguishing.Hard
    adversaryModel measure (ddhProblem F)

end DDH

end Crypto.Assumption.DL

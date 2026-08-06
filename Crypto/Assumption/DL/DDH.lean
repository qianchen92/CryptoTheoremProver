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

universe uCost uAdversaryCost uParameter uScalar uGroup

variable
    {M : CostModel.{uCost}}
    {Parameter : Type uParameter}
    {Scalar : Type uScalar}
    {Carrier : Type uGroup}

/-- The mathematical parameter underlying a cost-aware DDH instance. -/
abbrev MathematicalParam (Scalar : Type uScalar) (Carrier : Type uGroup) :=
  Crypto.Assumption.DL.Parameter.DecisionalCyclicAction Scalar Carrier

/--
The typed primitive capabilities carried by a DDH parameter.  Carrier addition
and subtraction let ElGamal reuse this same exact handler instead of installing
a second source of primitive costs.
-/
inductive Op (math : MathematicalParam Scalar Carrier) :
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

def signature (math : MathematicalParam Scalar Carrier) : Signature where
  Op := Op math

/-- Exact cost-erasure laws for a DDH primitive handler. -/
structure ExactLaws
    {math : MathematicalParam Scalar Carrier}
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
structure PublicParam
    (M : CostModel.{uCost}) (Scalar : Type uScalar) (Carrier : Type uGroup)
    extends MathematicalParam Scalar Carrier where
  algebra : CostedAlgebra M (signature toDecisionalCyclicAction)
  laws : ExactLaws algebra

namespace PublicParam

abbrev instAddGroup (pp : PublicParam.{uCost, uScalar, uGroup} M Scalar Carrier) : AddGroup pp.Carrier :=
  pp.toDecisionalCyclicAction.instAddGroup

abbrev instFintypeCarrier (pp : PublicParam.{uCost, uScalar, uGroup} M Scalar Carrier) : Fintype pp.Carrier :=
  pp.toDecisionalCyclicAction.instFintypeCarrier

abbrev instNonemptyCarrier (pp : PublicParam.{uCost, uScalar, uGroup} M Scalar Carrier) : Nonempty pp.Carrier :=
  pp.toDecisionalCyclicAction.instNonemptyCarrier

abbrev instFintypeScalar (pp : PublicParam.{uCost, uScalar, uGroup} M Scalar Carrier) : Fintype pp.Scalar :=
  pp.fintypeScalar

abbrev instSMul (pp : PublicParam.{uCost, uScalar, uGroup} M Scalar Carrier) : SMul pp.Scalar pp.Carrier :=
  pp.smul

abbrev instCommMonoidScalar (pp : PublicParam.{uCost, uScalar, uGroup} M Scalar Carrier) : CommMonoid pp.Scalar :=
  pp.commMonoidScalar

@[instance_reducible] def instMulAction
    (pp : PublicParam.{uCost, uScalar, uGroup} M Scalar Carrier) :
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
    (pp : PublicParam.{uCost, uScalar, uGroup} M Scalar Carrier) :
    Nonempty pp.Scalar :=
  ⟨pp.commMonoidScalar.one⟩

scoped[DDHParameter] attribute [instance]
  Crypto.Assumption.DL.DDH.instNonemptyScalar

open scoped DDHParameter

@[simp] theorem PublicParam.mulScalarAction
    (pp : PublicParam.{uCost, uScalar, uGroup} M Scalar Carrier)
    (leftExp rightExp : pp.Scalar) :
    (leftExp * rightExp) • pp.generator =
      leftExp • (rightExp • pp.generator) :=
  pp.mul_smul leftExp rightExp pp.generator

theorem PublicParam.scalarAction_commutes
    (pp : PublicParam.{uCost, uScalar, uGroup} M Scalar Carrier)
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
noncomputable def algebraLaws (pp : PublicParam.{uCost, uScalar, uGroup} M Scalar Carrier) :
    AlgebraLaws pp.algebra where
  semantics operation :=
    match operation with
    | .sampleScalar =>
        PMF.map ULift.up
          (@Crypto.Infrastructure.Probability.uniformPMF
            Scalar pp.fintypeScalar ⟨pp.commMonoidScalar.one⟩)
    | .sampleCarrier =>
        PMF.map ULift.up
          (@Crypto.Infrastructure.Probability.uniformPMF
            Carrier pp.fintypeCarrier ⟨pp.addGroup.zero⟩)
    | .smul scalar value =>
        PMF.pure (ULift.up (pp.smul.smul scalar value))
    | .add left right =>
        PMF.pure (ULift.up (pp.addGroup.add left right))
    | .sub left right =>
        PMF.pure (ULift.up (pp.addGroup.sub left right))
    | .mul left right =>
        PMF.pure (ULift.up (pp.commMonoidScalar.mul left right))
  exec_spec operation := by
    cases operation with
    | sampleScalar => exact pp.laws.sampleScalar
    | sampleCarrier => exact pp.laws.sampleCarrier
    | smul scalar value => exact pp.laws.smul scalar value
    | add left right => exact pp.laws.add left right
    | sub left right => exact pp.laws.sub left right
    | mul left right => exact pp.laws.mul left right

/-- Uniform upper bounds attached to one exact DDH algebra. -/
structure ParamEfficiencyCertificate (pp : PublicParam.{uCost, uScalar, uGroup} M Scalar Carrier) where
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

variable {pp : PublicParam.{uCost, uScalar, uGroup} M Scalar Carrier}

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
structure Family
    (M : CostModel.{uCost})
    (Parameter : Type uParameter) (Scalar : Type uScalar) (Carrier : Type uGroup) where
  publicParam : Parameter → PublicParam M Scalar Carrier
  parameterSec : Parameter → Crypto.SecPar
  setup : Crypto.SecPar → RandCosted M Parameter
  setup_parameterSec : ∀ sec result,
    result ∈ (setup sec).support → parameterSec result.val = sec
  addCost : Parameter → M.Cost
  add_exact : ∀ parameter left right,
    (publicParam parameter).algebra.exec (.add left right) =
      RandCosted.liftCosted
        (⟨ULift.up ((publicParam parameter).addGroup.add left right),
            addCost parameter⟩ : Costed M (ULift.{uScalar} Carrier))
  addBudget : Crypto.SecPar → M.Cost
  addCost_le_addBudget : ∀ parameter,
    M.instPartialOrder.le (addCost parameter)
      (addBudget (parameterSec parameter))

noncomputable def Family.ofFixed
    (pp : PublicParam.{uCost, uScalar, uGroup} M Scalar Carrier)
    (setupCost addCost : M.Cost)
    (add_exact : ∀ left right,
      pp.algebra.exec (.add left right) =
        RandCosted.liftCosted
          (⟨ULift.up (pp.addGroup.add left right), addCost⟩ :
            Costed M (ULift.{uScalar} Carrier))) :
    Family.{uCost, 0, uScalar, uGroup} M Crypto.SecPar Scalar Carrier where
  publicParam := fun _sec => pp
  parameterSec := id
  setup := fun sec => RandCosted.liftCosted ⟨sec, setupCost⟩
  setup_parameterSec := by
    intro sec result hresult
    simp only [RandCosted.liftCosted, PMF.mem_support_pure_iff] at hresult
    simpa using congrArg Costed.val hresult
  addCost := fun _sec => addCost
  add_exact := fun _sec => add_exact
  addBudget := fun _sec => addCost
  addCost_le_addBudget := fun _sec => M.instPartialOrder.le_refl addCost

noncomputable def Family.setupDist
    (F : Family M Parameter Scalar Carrier) (sec : Crypto.SecPar) :
    PMF Parameter :=
  RandCosted.valueDist (F.setup sec)

/-- Every parameter in the cost-erased setup support retains its security tag. -/
theorem Family.parameterSec_eq_of_mem_support_setupDist
    (F : Family M Parameter Scalar Carrier) (sec : Crypto.SecPar)
    (parameter : Parameter) (hparameter : parameter ∈ (F.setupDist sec).support) :
    F.parameterSec parameter = sec := by
  rw [Family.setupDist, RandCosted.valueDist, PMF.mem_support_map_iff] at hparameter
  rcases hparameter with ⟨result, hresult, rfl⟩
  exact F.setup_parameterSec sec result hresult

/-- Family-level operations for setup-dependent DDH sampling. -/
inductive FamilyOp (F : Family M Parameter Scalar Carrier) :
    Type (max uParameter uScalar uGroup) →
      Type (max uCost (uParameter + 1) (uScalar + 1) (uGroup + 1) + 1) where
  | setup (sec : Crypto.SecPar) :
      FamilyOp F (ULift.{max uScalar uGroup} Parameter)
  | sampleScalar (parameter : Parameter) :
      FamilyOp F (ULift.{max uParameter uGroup} Scalar)
  | sampleCarrier (parameter : Parameter) :
      FamilyOp F (ULift.{max uParameter uScalar} Carrier)
  | smul (parameter : Parameter) (scalar : Scalar) (value : Carrier) :
      FamilyOp F (ULift.{max uParameter uScalar} Carrier)
  | add (parameter : Parameter) (left right : Carrier) :
      FamilyOp F (ULift.{max uParameter uScalar} Carrier)
  | sub (parameter : Parameter) (left right : Carrier) :
      FamilyOp F (ULift.{max uParameter uScalar} Carrier)
  | mul (parameter : Parameter) (left right : Scalar) :
      FamilyOp F (ULift.{max uParameter uGroup} Scalar)

def familySignature (F : Family M Parameter Scalar Carrier) : Signature where
  Op := FamilyOp F

noncomputable def familyAlgebra (F : Family M Parameter Scalar Carrier) :
    CostedAlgebra M (familySignature F) where
  exec operation :=
    match operation with
    | .setup sec => RandCosted.map ULift.up (F.setup sec)
    | .sampleScalar parameter =>
        RandCosted.map (fun result => ULift.up result.down)
          ((F.publicParam parameter).algebra.exec .sampleScalar)
    | .sampleCarrier parameter =>
        RandCosted.map (fun result => ULift.up result.down)
          ((F.publicParam parameter).algebra.exec .sampleCarrier)
    | .smul parameter scalar value =>
        RandCosted.map (fun result => ULift.up result.down)
          ((F.publicParam parameter).algebra.exec (.smul scalar value))
    | .add parameter left right =>
        RandCosted.map (fun result => ULift.up result.down)
          ((F.publicParam parameter).algebra.exec (.add left right))
    | .sub parameter left right =>
        RandCosted.map (fun result => ULift.up result.down)
          ((F.publicParam parameter).algebra.exec (.sub left right))
    | .mul parameter left right =>
        RandCosted.map (fun result => ULift.up result.down)
          ((F.publicParam parameter).algebra.exec (.mul left right))

noncomputable def familyAlgebraLaws
    (F : Family M Parameter Scalar Carrier) :
    AlgebraLaws (familyAlgebra F) where
  semantics operation :=
    match operation with
    | .setup sec => PMF.map ULift.up (F.setupDist sec)
    | .sampleScalar parameter =>
        PMF.map (fun result => ULift.up result.down)
          ((algebraLaws (F.publicParam parameter)).semantics Op.sampleScalar)
    | .sampleCarrier parameter =>
        PMF.map (fun result => ULift.up result.down)
          ((algebraLaws (F.publicParam parameter)).semantics Op.sampleCarrier)
    | .smul parameter scalar value =>
        PMF.map (fun result => ULift.up result.down)
          ((algebraLaws (F.publicParam parameter)).semantics (Op.smul scalar value))
    | .add parameter left right =>
        PMF.map (fun result => ULift.up result.down)
          ((algebraLaws (F.publicParam parameter)).semantics (Op.add left right))
    | .sub parameter left right =>
        PMF.map (fun result => ULift.up result.down)
          ((algebraLaws (F.publicParam parameter)).semantics (Op.sub left right))
    | .mul parameter left right =>
        PMF.map (fun result => ULift.up result.down)
          ((algebraLaws (F.publicParam parameter)).semantics (Op.mul left right))
  exec_spec operation := by
    cases operation with
    | setup sec => simp [familyAlgebra, Family.setupDist]
    | sampleScalar parameter =>
        simp [familyAlgebra, (algebraLaws (F.publicParam parameter)).exec_spec]
    | sampleCarrier parameter =>
        simp [familyAlgebra, (algebraLaws (F.publicParam parameter)).exec_spec]
    | smul parameter scalar value =>
        simp [familyAlgebra, (algebraLaws (F.publicParam parameter)).exec_spec]
    | add parameter left right =>
        simp [familyAlgebra, (algebraLaws (F.publicParam parameter)).exec_spec]
    | sub parameter left right =>
        simp [familyAlgebra, (algebraLaws (F.publicParam parameter)).exec_spec]
    | mul parameter left right =>
        simp [familyAlgebra, (algebraLaws (F.publicParam parameter)).exec_spec]

def setupProgram (F : Family M Parameter Scalar Carrier) :
    Program (familyAlgebra F) Crypto.SecPar
      (ULift.{max uScalar uGroup} Parameter) where
  body sec := .call (.setup sec)

@[simp] theorem setupProgram_runCosted
    (F : Family M Parameter Scalar Carrier) (sec : Crypto.SecPar) :
    Program.runCosted (setupProgram F) sec = RandCosted.map ULift.up (F.setup sec) :=
  rfl

/-- A DDH challenge consists of parameters and three carrier elements. -/
structure ChallengeInput (F : Family M Parameter Scalar Carrier) where
  parameter : Parameter
  left : Carrier
  right : Carrier
  shared : Carrier

structure ChallengeValues (pp : PublicParam.{uCost, uScalar, uGroup} M Scalar Carrier) where
  left : pp.Carrier
  right : pp.Carrier
  shared : pp.Carrier

def ChallengeValues.toChallengeInput
    {F : Family M Parameter Scalar Carrier} {parameter : Parameter}
    (values : ChallengeValues (F.publicParam parameter)) :
    ChallengeInput F where
  parameter := parameter
  left := values.left
  right := values.right
  shared := values.shared

def realChallenge
    (F : Family M Parameter Scalar Carrier) (parameter : Parameter)
    (leftExp rightExp : Scalar) : ChallengeInput F :=
  let pp := F.publicParam parameter
  {
    parameter := parameter
    left := pp.smul.smul leftExp pp.generator
    right := pp.smul.smul rightExp pp.generator
    shared := pp.smul.smul (pp.commMonoidScalar.mul leftExp rightExp) pp.generator
  }

@[simp] theorem realChallenge_shared_eq_nestedAction
    (F : Family M Parameter Scalar Carrier) (parameter : Parameter)
    (leftExp rightExp : Scalar) :
    (realChallenge F parameter leftExp rightExp).shared =
      (F.publicParam parameter).smul.smul leftExp
        ((F.publicParam parameter).smul.smul rightExp
          (F.publicParam parameter).generator) :=
  (F.publicParam parameter).mul_smul leftExp rightExp
    (F.publicParam parameter).generator

def randomChallenge
    (F : Family M Parameter Scalar Carrier) (parameter : Parameter)
    (leftExp rightExp : Scalar) (shared : Carrier) : ChallengeInput F where
  parameter := parameter
  left := (F.publicParam parameter).smul.smul leftExp
    (F.publicParam parameter).generator
  right := (F.publicParam parameter).smul.smul rightExp
    (F.publicParam parameter).generator
  shared := shared

/-- Genuine tuple construction as a typed program. -/
def realChallengeProgram (pp : PublicParam.{uCost, uScalar, uGroup} M Scalar Carrier) :
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
def randomChallengeProgram (pp : PublicParam.{uCost, uScalar, uGroup} M Scalar Carrier) :
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
    (pp : PublicParam.{uCost, uScalar, uGroup} M Scalar Carrier)
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
    (pp : PublicParam.{uCost, uScalar, uGroup} M Scalar Carrier)
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
def realSampleTailProgram (pp : PublicParam.{uCost, uScalar, uGroup} M Scalar Carrier) :
    Program pp.algebra Unit (ULift.{uScalar} (ChallengeValues pp)) where
  body _input :=
    .bind (.call .sampleScalar) fun leftExp =>
      .bind (.call .sampleScalar) fun rightExp =>
        (realChallengeProgram pp).body (leftExp.down, rightExp.down)

/-- Random local sampling path. -/
def randomSampleTailProgram (pp : PublicParam.{uCost, uScalar, uGroup} M Scalar Carrier) :
    Program pp.algebra Unit (ULift.{uScalar} (ChallengeValues pp)) where
  body _input :=
    .bind (.call .sampleScalar) fun leftExp =>
      .bind (.call .sampleScalar) fun rightExp =>
        .bind (.call .sampleCarrier) fun shared =>
          (randomChallengeProgram pp).body
            (leftExp.down, rightExp.down, shared.down)

noncomputable def realSampleTailBoundedProgram
    (pp : PublicParam.{uCost, uScalar, uGroup} M Scalar Carrier)
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
    (pp : PublicParam.{uCost, uScalar, uGroup} M Scalar Carrier)
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
def realSampleProgram (F : Family M Parameter Scalar Carrier) :
    Program (familyAlgebra F) Crypto.SecPar
      (ULift.{uScalar} (ChallengeInput F)) where
  body sec :=
    .bind (.call (.setup sec)) fun liftedParameter =>
      let parameter := liftedParameter.down
      let pp := F.publicParam parameter
      .bind (.call (.sampleScalar parameter)) fun leftExp =>
        .bind (.call (.sampleScalar parameter)) fun rightExp =>
          .bind (.call (.smul parameter leftExp.down pp.generator)) fun left =>
            .bind (.call (.smul parameter rightExp.down pp.generator)) fun right =>
              .bind (.call (.mul parameter leftExp.down rightExp.down)) fun product =>
                .bind (.call (.smul parameter product.down pp.generator)) fun shared =>
                  .pure (ULift.up {
                    parameter := parameter
                    left := left.down
                    right := right.down
                    shared := shared.down })

/-- Complete random-DDH sampling. -/
def randomSampleProgram (F : Family M Parameter Scalar Carrier) :
    Program (familyAlgebra F) Crypto.SecPar
      (ULift.{uScalar} (ChallengeInput F)) where
  body sec :=
    .bind (.call (.setup sec)) fun liftedParameter =>
      let parameter := liftedParameter.down
      let pp := F.publicParam parameter
      .bind (.call (.sampleScalar parameter)) fun leftExp =>
        .bind (.call (.sampleScalar parameter)) fun rightExp =>
          .bind (.call (.sampleCarrier parameter)) fun sampledShared =>
            .bind (.call (.smul parameter leftExp.down pp.generator)) fun left =>
              .bind (.call (.smul parameter rightExp.down pp.generator)) fun right =>
                .pure (ULift.up {
                  parameter := parameter
                  left := left.down
                  right := right.down
                  shared := sampledShared.down })

noncomputable def realSample (F : Family M Parameter Scalar Carrier) :
    Crypto.SecPar → PMF (ChallengeInput F) :=
  fun sec => PMF.map ULift.down (Program.valueDist (realSampleProgram F) sec)

noncomputable def randomSample (F : Family M Parameter Scalar Carrier) :
    Crypto.SecPar → PMF (ChallengeInput F) :=
  fun sec => PMF.map ULift.down (Program.valueDist (randomSampleProgram F) sec)

/-- Cost erasure exposes genuine DDH sampling as setup followed by two uniform
scalar samples. -/
theorem realSample_eq
    (F : Family M Parameter Scalar Carrier) (sec : Crypto.SecPar) :
    realSample F sec =
      PMF.bind (F.setupDist sec) fun parameter =>
        let pp := F.publicParam parameter
        PMF.bind
            (@Crypto.Infrastructure.Probability.uniformPMF
              Scalar pp.fintypeScalar ⟨pp.commMonoidScalar.one⟩) fun a =>
          PMF.bind
              (@Crypto.Infrastructure.Probability.uniformPMF
                Scalar pp.fintypeScalar ⟨pp.commMonoidScalar.one⟩) fun b =>
            PMF.pure (realChallenge F parameter a b) := by
  unfold realSample
  change PMF.map ULift.down
    (Program.Code.valueDist ((realSampleProgram F).body sec)) = _
  simp only [realSampleProgram, Program.Code.valueDist_bind,
    Program.Code.valueDist_call_eq (familyAlgebraLaws F),
    Program.Code.valueDist_pure, familyAlgebraLaws, algebraLaws,
    Family.setupDist, PMF.map_bind, PMF.bind_map, PMF.pure_bind, PMF.pure_map]
  simp only [realChallenge]
  congr 1
  funext setupResult
  cases setupResult with
  | mk parameter setupCost =>
      simp [PMF.map_bind, PMF.pure_map, Function.comp_apply]

/-- Cost erasure exposes random DDH sampling as setup, two uniform scalar
samples, and one independent uniform carrier sample. -/
theorem randomSample_eq
    (F : Family M Parameter Scalar Carrier) (sec : Crypto.SecPar) :
    randomSample F sec =
      PMF.bind (F.setupDist sec) fun parameter =>
        let pp := F.publicParam parameter
        PMF.bind
            (@Crypto.Infrastructure.Probability.uniformPMF
              Scalar pp.fintypeScalar ⟨pp.commMonoidScalar.one⟩) fun a =>
          PMF.bind
              (@Crypto.Infrastructure.Probability.uniformPMF
                Scalar pp.fintypeScalar ⟨pp.commMonoidScalar.one⟩) fun b =>
            PMF.bind
                (@Crypto.Infrastructure.Probability.uniformPMF
                  Carrier pp.fintypeCarrier ⟨pp.addGroup.zero⟩) fun z =>
              PMF.pure (randomChallenge F parameter a b z) := by
  unfold randomSample
  change PMF.map ULift.down
    (Program.Code.valueDist ((randomSampleProgram F).body sec)) = _
  simp only [randomSampleProgram, Program.Code.valueDist_bind,
    Program.Code.valueDist_call_eq (familyAlgebraLaws F),
    Program.Code.valueDist_pure, familyAlgebraLaws, algebraLaws,
    Family.setupDist, PMF.map_bind, PMF.bind_map, PMF.pure_bind, PMF.pure_map]
  simp only [randomChallenge]
  congr 1
  funext setupResult
  cases setupResult with
  | mk parameter setupCost =>
      simp [PMF.map_bind, PMF.pure_map, Function.comp_apply]

/-- A genuine DDH challenge in the sample support has the setup security tag. -/
theorem parameterSec_eq_of_mem_support_realSample
    (F : Family M Parameter Scalar Carrier) (sec : Crypto.SecPar)
    (challenge : ChallengeInput F)
    (hchallenge : challenge ∈ (realSample F sec).support) :
    F.parameterSec challenge.parameter = sec := by
  rw [realSample_eq] at hchallenge
  rw [PMF.mem_support_bind_iff] at hchallenge
  rcases hchallenge with ⟨parameter, hparameter, hchallenge⟩
  dsimp only at hchallenge
  rw [PMF.mem_support_bind_iff] at hchallenge
  rcases hchallenge with ⟨a, _ha, hchallenge⟩
  rw [PMF.mem_support_bind_iff] at hchallenge
  rcases hchallenge with ⟨b, _hb, hchallenge⟩
  simp only [PMF.mem_support_pure_iff] at hchallenge
  subst challenge
  exact F.parameterSec_eq_of_mem_support_setupDist sec parameter hparameter

/-- A random DDH challenge in the sample support has the setup security tag. -/
theorem parameterSec_eq_of_mem_support_randomSample
    (F : Family M Parameter Scalar Carrier) (sec : Crypto.SecPar)
    (challenge : ChallengeInput F)
    (hchallenge : challenge ∈ (randomSample F sec).support) :
    F.parameterSec challenge.parameter = sec := by
  rw [randomSample_eq] at hchallenge
  rw [PMF.mem_support_bind_iff] at hchallenge
  rcases hchallenge with ⟨parameter, hparameter, hchallenge⟩
  dsimp only at hchallenge
  rw [PMF.mem_support_bind_iff] at hchallenge
  rcases hchallenge with ⟨a, _ha, hchallenge⟩
  rw [PMF.mem_support_bind_iff] at hchallenge
  rcases hchallenge with ⟨b, _hb, hchallenge⟩
  rw [PMF.mem_support_bind_iff] at hchallenge
  rcases hchallenge with ⟨z, _hz, hchallenge⟩
  simp only [PMF.mem_support_pure_iff] at hchallenge
  subst challenge
  exact F.parameterSec_eq_of_mem_support_setupDist sec parameter hparameter

/-- Global bounds attach directly to the authoritative DDH programs. -/
structure EfficiencyCertificate (F : Family M Parameter Scalar Carrier) where
  setupBudget : Crypto.SecPar → M.Cost
  setupCostBound : Program.CostBound (setupProgram F) setupBudget
  realSampleBudget : Crypto.SecPar → M.Cost
  realSampleCostBound : Program.CostBound (realSampleProgram F) realSampleBudget
  randomSampleBudget : Crypto.SecPar → M.Cost
  randomSampleCostBound : Program.CostBound (randomSampleProgram F) randomSampleBudget

theorem setupProgram_costBound
    (F : Family M Parameter Scalar Carrier)
    (certificate : EfficiencyCertificate F) :
    Program.CostBound (setupProgram F) certificate.setupBudget :=
  certificate.setupCostBound

theorem realSampleProgram_costBound
    (F : Family M Parameter Scalar Carrier)
    (certificate : EfficiencyCertificate F) :
    Program.CostBound (realSampleProgram F) certificate.realSampleBudget :=
  certificate.realSampleCostBound

theorem randomSampleProgram_costBound
    (F : Family M Parameter Scalar Carrier)
    (certificate : EfficiencyCertificate F) :
    Program.CostBound (randomSampleProgram F) certificate.randomSampleBudget :=
  certificate.randomSampleCostBound

/-- The distinguishing problem induced by a cost-aware DDH family. -/
noncomputable def ddhProblem (F : Family M Parameter Scalar Carrier) :
    Crypto.Infrastructure.GameBased.Distinguishing.Problem
      (ChallengeInput F) where
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
    (F : Family M Parameter Scalar Carrier) : Prop :=
  Crypto.Infrastructure.GameBased.Distinguishing.Hard
    adversaryModel measure (ddhProblem F)

end DDH

end Crypto.Assumption.DL

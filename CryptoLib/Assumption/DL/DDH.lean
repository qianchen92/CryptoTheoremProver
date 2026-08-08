import CryptoLib.Assumption.DL.Parameter
import CryptoLib.Algebra.Generic.Signature
import CryptoLib.Algebra.Generic.Handler
import CryptoLib.Algebra.Generic.Laws
import CryptoLib.Algebra.Generic.Bounds
import CryptoLib.Core.Infrastructure.Probability.Uniform
import CryptoLib.Core.Infrastructure.GameBased.Distinguishing

namespace CryptoLib.Assumption.DL

namespace DDH

open CryptoLib.Core.Infrastructure.Computation
open CryptoLib.Algebra.Generic
open CryptoLib.Core.Infrastructure.Computation.Cost

universe uCost uAdversaryCost uParameter uScalar uGroup

variable
    {M : CostModel.{uCost}}
    {Parameter : Type uParameter}
    {Scalar : Type uScalar}
    {Carrier : Type uGroup}

/-- The mathematical parameter underlying a cost-aware DDH instance. -/
abbrev MathematicalParam (Scalar : Type uScalar) (Carrier : Type uGroup) :=
  CryptoLib.Assumption.DL.Parameter.DecisionalCyclicAction Scalar Carrier

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
        (@CryptoLib.Core.Infrastructure.Probability.uniformPMF
          math.Scalar math.fintypeScalar
          ⟨math.commMonoidScalar.one⟩)
  sampleCarrier :
    RandCosted.valueDist (A.exec .sampleCarrier) =
      PMF.map ULift.up
        (@CryptoLib.Core.Infrastructure.Probability.uniformPMF
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
  CryptoLib.Assumption.DL.DDH.PublicParam.instAddGroup
  CryptoLib.Assumption.DL.DDH.PublicParam.instFintypeCarrier
  CryptoLib.Assumption.DL.DDH.PublicParam.instNonemptyCarrier
  CryptoLib.Assumption.DL.DDH.PublicParam.instFintypeScalar
  CryptoLib.Assumption.DL.DDH.PublicParam.instSMul
  CryptoLib.Assumption.DL.DDH.PublicParam.instCommMonoidScalar
  CryptoLib.Assumption.DL.DDH.PublicParam.instMulAction

@[instance_reducible] def instNonemptyScalar
    (pp : PublicParam.{uCost, uScalar, uGroup} M Scalar Carrier) :
    Nonempty pp.Scalar :=
  ⟨pp.commMonoidScalar.one⟩

scoped[DDHParameter] attribute [instance]
  CryptoLib.Assumption.DL.DDH.instNonemptyScalar

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
          (@CryptoLib.Core.Infrastructure.Probability.uniformPMF
            Scalar pp.fintypeScalar ⟨pp.commMonoidScalar.one⟩)
    | .sampleCarrier =>
        PMF.map ULift.up
          (@CryptoLib.Core.Infrastructure.Probability.uniformPMF
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
  parameterSec : Parameter → CryptoLib.Core.SecPar
  setup : CryptoLib.Core.SecPar → RandCosted M Parameter
  setup_parameterSec : ∀ sec result,
    result ∈ (setup sec).support → parameterSec result.val = sec
  addCost : Parameter → M.Cost
  add_exact : ∀ parameter left right,
    (publicParam parameter).algebra.exec (.add left right) =
      RandCosted.liftCosted
        (⟨ULift.up ((publicParam parameter).addGroup.add left right),
            addCost parameter⟩ : Costed M (ULift.{uScalar} Carrier))
  addBudget : CryptoLib.Core.SecPar → M.Cost
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
    Family.{uCost, 0, uScalar, uGroup} M CryptoLib.Core.SecPar Scalar Carrier where
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
    (F : Family M Parameter Scalar Carrier) (sec : CryptoLib.Core.SecPar) :
    PMF Parameter :=
  RandCosted.valueDist (F.setup sec)

/-- Every parameter in the cost-erased setup support retains its security tag. -/
theorem Family.parameterSec_eq_of_mem_support_setupDist
    (F : Family M Parameter Scalar Carrier) (sec : CryptoLib.Core.SecPar)
    (parameter : Parameter) (hparameter : parameter ∈ (F.setupDist sec).support) :
    F.parameterSec parameter = sec := by
  rw [Family.setupDist, RandCosted.valueDist, PMF.mem_support_map_iff] at hparameter
  rcases hparameter with ⟨result, hresult, rfl⟩
  exact F.setup_parameterSec sec result hresult

/-- Family-level operations for setup-dependent DDH sampling. -/
inductive FamilyOp (F : Family M Parameter Scalar Carrier) :
    Type (max uParameter uScalar uGroup) →
      Type (max uCost (uParameter + 1) (uScalar + 1) (uGroup + 1) + 1) where
  | setup (sec : CryptoLib.Core.SecPar) :
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

/-
The executable first-order programs are kept in the separate
`CryptoLib.Assumption.Program.DL.DDH` adapter. This module keeps the
mathematical challenge and cost-erased distributions.
-/

noncomputable def realSample (F : Family M Parameter Scalar Carrier) :
    CryptoLib.Core.SecPar → PMF (ChallengeInput F) :=
  fun sec => PMF.bind (F.setupDist sec) fun parameter =>
    let pp := F.publicParam parameter
    PMF.bind
        (@CryptoLib.Core.Infrastructure.Probability.uniformPMF
          Scalar pp.fintypeScalar ⟨pp.commMonoidScalar.one⟩) fun a =>
      PMF.bind
          (@CryptoLib.Core.Infrastructure.Probability.uniformPMF
            Scalar pp.fintypeScalar ⟨pp.commMonoidScalar.one⟩) fun b =>
        PMF.pure (realChallenge F parameter a b)

noncomputable def randomSample (F : Family M Parameter Scalar Carrier) :
    CryptoLib.Core.SecPar → PMF (ChallengeInput F) :=
  fun sec => PMF.bind (F.setupDist sec) fun parameter =>
    let pp := F.publicParam parameter
    PMF.bind
        (@CryptoLib.Core.Infrastructure.Probability.uniformPMF
          Scalar pp.fintypeScalar ⟨pp.commMonoidScalar.one⟩) fun a =>
      PMF.bind
          (@CryptoLib.Core.Infrastructure.Probability.uniformPMF
            Scalar pp.fintypeScalar ⟨pp.commMonoidScalar.one⟩) fun b =>
        PMF.bind
            (@CryptoLib.Core.Infrastructure.Probability.uniformPMF
              Carrier pp.fintypeCarrier ⟨pp.addGroup.zero⟩) fun z =>
          PMF.pure (randomChallenge F parameter a b z)

theorem realSample_eq
    (F : Family M Parameter Scalar Carrier) (sec : CryptoLib.Core.SecPar) :
    realSample F sec =
      PMF.bind (F.setupDist sec) fun parameter =>
        let pp := F.publicParam parameter
        PMF.bind
            (@CryptoLib.Core.Infrastructure.Probability.uniformPMF
              Scalar pp.fintypeScalar ⟨pp.commMonoidScalar.one⟩) fun a =>
          PMF.bind
              (@CryptoLib.Core.Infrastructure.Probability.uniformPMF
                Scalar pp.fintypeScalar ⟨pp.commMonoidScalar.one⟩) fun b =>
            PMF.pure (realChallenge F parameter a b) :=
  rfl

theorem randomSample_eq
    (F : Family M Parameter Scalar Carrier) (sec : CryptoLib.Core.SecPar) :
    randomSample F sec =
      PMF.bind (F.setupDist sec) fun parameter =>
        let pp := F.publicParam parameter
        PMF.bind
            (@CryptoLib.Core.Infrastructure.Probability.uniformPMF
              Scalar pp.fintypeScalar ⟨pp.commMonoidScalar.one⟩) fun a =>
          PMF.bind
              (@CryptoLib.Core.Infrastructure.Probability.uniformPMF
                Scalar pp.fintypeScalar ⟨pp.commMonoidScalar.one⟩) fun b =>
            PMF.bind
                (@CryptoLib.Core.Infrastructure.Probability.uniformPMF
                  Carrier pp.fintypeCarrier ⟨pp.addGroup.zero⟩) fun z =>
              PMF.pure (randomChallenge F parameter a b z) :=
  rfl

theorem parameterSec_eq_of_mem_support_realSample
    (F : Family M Parameter Scalar Carrier) (sec : CryptoLib.Core.SecPar)
    (challenge : ChallengeInput F)
    (hchallenge : challenge ∈ (realSample F sec).support) :
    F.parameterSec challenge.parameter = sec := by
  rw [realSample_eq] at hchallenge
  rw [PMF.mem_support_bind_iff] at hchallenge
  rcases hchallenge with ⟨parameter, hparameter, hchallenge⟩
  rw [PMF.mem_support_bind_iff] at hchallenge
  rcases hchallenge with ⟨a, _ha, hchallenge⟩
  rw [PMF.mem_support_bind_iff] at hchallenge
  rcases hchallenge with ⟨b, _hb, hchallenge⟩
  simp only [PMF.mem_support_pure_iff] at hchallenge
  subst challenge
  exact F.parameterSec_eq_of_mem_support_setupDist sec parameter hparameter

theorem parameterSec_eq_of_mem_support_randomSample
    (F : Family M Parameter Scalar Carrier) (sec : CryptoLib.Core.SecPar)
    (challenge : ChallengeInput F)
    (hchallenge : challenge ∈ (randomSample F sec).support) :
    F.parameterSec challenge.parameter = sec := by
  rw [randomSample_eq] at hchallenge
  rw [PMF.mem_support_bind_iff] at hchallenge
  rcases hchallenge with ⟨parameter, hparameter, hchallenge⟩
  rw [PMF.mem_support_bind_iff] at hchallenge
  rcases hchallenge with ⟨a, _ha, hchallenge⟩
  rw [PMF.mem_support_bind_iff] at hchallenge
  rcases hchallenge with ⟨b, _hb, hchallenge⟩
  rw [PMF.mem_support_bind_iff] at hchallenge
  rcases hchallenge with ⟨z, _hz, hchallenge⟩
  simp only [PMF.mem_support_pure_iff] at hchallenge
  subst challenge
  exact F.parameterSec_eq_of_mem_support_setupDist sec parameter hparameter

/- The distinguishing problem induced by a cost-aware DDH family. -/
noncomputable def ddhProblem (F : Family M Parameter Scalar Carrier) :
    CryptoLib.Core.Infrastructure.GameBased.Distinguishing.Problem
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
  CryptoLib.Core.Infrastructure.GameBased.Distinguishing.Hard
    adversaryModel measure (ddhProblem F)

end DDH

end CryptoLib.Assumption.DL

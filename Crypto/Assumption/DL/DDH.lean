import Crypto.Assumption.DL.Parameter
import Crypto.Infrastructure.Computation.Program
import Crypto.Infrastructure.Computation.Randomized
import Crypto.Infrastructure.GameBased.Indistinguishability
import Mathlib.Probability.ProbabilityMassFunction.Monad

namespace Crypto.Assumption.DL

namespace DDH

open Crypto.Infrastructure.Computation
open Crypto.Infrastructure.Computation.Algebra
open Crypto.Infrastructure.Computation.Cost

universe uScalar uGroup

/--
Public parameters for a finite additive-group DDH instance.

This compatibility name is the stronger shared cyclic-action parameter. The
algebraic backends, sampler laws, and exact samplers remain part of the
parameter, while efficiency bounds stay in separate certificates.
-/
abbrev PublicParam :=
  Crypto.Assumption.DL.Parameter.DecisionalCyclicAction.{uScalar, uGroup}

scoped[DDHParameter] attribute [instance]
  Crypto.Assumption.DL.Parameter.CyclicAction.instAddGroup
scoped[DDHParameter] attribute [instance]
  Crypto.Assumption.DL.Parameter.CyclicAction.instFintypeCarrier
scoped[DDHParameter] attribute [instance]
  Crypto.Assumption.DL.Parameter.CyclicAction.fintypeScalar
scoped[DDHParameter] attribute [instance]
  Crypto.Assumption.DL.Parameter.CyclicAction.instNonemptyCarrier
scoped[DDHParameter] attribute [instance]
  Crypto.Assumption.DL.Parameter.DecisionalCyclicAction.commMonoidScalar
scoped[DDHParameter] attribute [instance]
  Crypto.Assumption.DL.Parameter.DecisionalCyclicAction.mulAction

@[instance_reducible] def instNonemptyScalar
    (pp : PublicParam.{uScalar, uGroup}) : Nonempty pp.Scalar :=
  ⟨pp.commMonoidScalar.one⟩

scoped[DDHParameter] attribute [instance]
  Crypto.Assumption.DL.DDH.instNonemptyScalar

open scoped DDHParameter

/-- Scalar multiplication respects multiplication in the scalar monoid. -/
@[simp] theorem PublicParam.mulScalarAction
    (pp : PublicParam.{uScalar, uGroup}) (leftExp rightExp : pp.Scalar) :
    (leftExp * rightExp) • pp.generator =
      leftExp • (rightExp • pp.generator) :=
  mul_smul leftExp rightExp pp.generator

/-- Scalar actions commute because the scalar monoid is commutative. -/
theorem PublicParam.compatibleScalarAction
    (pp : PublicParam.{uScalar, uGroup}) (leftExp rightExp : pp.Scalar) :
    leftExp • (rightExp • pp.generator) =
      rightExp • (leftExp • pp.generator) := by
  rw [← mul_smul, mul_comm, mul_smul]

/-- Local sampler and algebraic bounds used only when proving DDH efficiency. -/
structure ParamEfficiencyCertificate
    (pp : PublicParam.{uScalar, uGroup}) where
  scalarSamplerBounds : UniformSamplerBounds pp.scalarSampler
  carrierSamplerBounds : UniformSamplerBounds pp.carrierSampler
  additiveBounds : AdditiveCostBounds pp.backend
  scalarMulBounds : MultiplicativeCostBounds pp.scalarMulBackend

/-- Exactly the dependent typed primitive capabilities used by DDH. -/
inductive Op (pp : PublicParam.{uScalar, uGroup}) :
    Type (max uScalar uGroup) → Type (max uScalar uGroup + 1) where
  | sampleScalar : Op pp (ULift.{uGroup} pp.Scalar)
  | sampleCarrier : Op pp (ULift.{uScalar} pp.Carrier)
  | smul (scalar : pp.Scalar) (value : pp.Carrier) :
      Op pp (ULift.{uScalar} pp.Carrier)
  | mul (left right : pp.Scalar) : Op pp (ULift.{uGroup} pp.Scalar)

/-- The typed primitive signature selected by one DDH parameter. -/
def signature (pp : PublicParam.{uScalar, uGroup}) : Signature where
  Op := Op pp

/-- The sole exact interpreter for DDH primitives at one parameter. -/
noncomputable def algebra (pp : PublicParam.{uScalar, uGroup}) :
    CostedAlgebra natCostModel (signature pp) where
  exec operation :=
    match operation with
    | .sampleScalar => RandCosted.map ULift.up pp.scalarSampler.sample
    | .sampleCarrier => RandCosted.map ULift.up pp.carrierSampler.sample
    | .smul scalar value =>
        RandCosted.liftCosted
          (Costed.map ULift.up (pp.backend.smul scalar value))
    | .mul left right =>
        RandCosted.liftCosted
          (Costed.map ULift.up (pp.scalarMulBackend.mul left right))

/-- Mathematical, cost-erased specifications for the exact DDH handler. -/
noncomputable def algebraLaws (pp : PublicParam.{uScalar, uGroup}) :
    AlgebraLaws (algebra pp) where
  semantics operation :=
    match operation with
    | .sampleScalar =>
        PMF.map ULift.up
          (Crypto.Infrastructure.Computation.Distribution.uniformPMF pp.Scalar)
    | .sampleCarrier =>
        PMF.map ULift.up
          (Crypto.Infrastructure.Computation.Distribution.uniformPMF pp.Carrier)
    | .smul scalar value => PMF.pure (ULift.up (scalar • value))
    | .mul left right => PMF.pure (ULift.up (left * right))
  exec_spec operation := by
    cases operation with
    | sampleScalar =>
        simpa [algebra] using
          congrArg (PMF.map ULift.up) pp.scalarSamplerLaws.sample_spec
    | sampleCarrier =>
        simpa [algebra] using
          congrArg (PMF.map ULift.up) pp.carrierSamplerLaws.sample_spec
    | smul scalar value => simp [algebra]
    | mul left right => simp [algebra]

/-- Independent operation bounds for the exact DDH handler. -/
noncomputable def operationBounds
    (pp : PublicParam.{uScalar, uGroup})
    (certificate : ParamEfficiencyCertificate pp) :
    OperationBounds (algebra pp) where
  budget operation :=
    match operation with
    | .sampleScalar => certificate.scalarSamplerBounds.sampleBudget
    | .sampleCarrier => certificate.carrierSamplerBounds.sampleBudget
    | .smul _ _ => certificate.additiveBounds.smulBudget
    | .mul _ _ => certificate.scalarMulBounds.mulBudget
  cost_le operation result hresult := by
    cases operation with
    | sampleScalar =>
        simp only [algebra, RandCosted.map, RandCostedT.map] at hresult
        rw [PMF.mem_support_map_iff] at hresult
        rcases hresult with ⟨sampleResult, hsampleResult, hresult⟩
        subst result
        exact certificate.scalarSamplerBounds.cost_le
          sampleResult hsampleResult
    | sampleCarrier =>
        simp only [algebra, RandCosted.map, RandCostedT.map] at hresult
        rw [PMF.mem_support_map_iff] at hresult
        rcases hresult with ⟨sampleResult, hsampleResult, hresult⟩
        subst result
        exact certificate.carrierSamplerBounds.cost_le
          sampleResult hsampleResult
    | smul scalar value =>
        simp only [algebra, RandCosted.liftCosted,
          RandCostedT.liftCosted] at hresult
        rw [PMF.mem_support_pure_iff] at hresult
        subst result
        exact certificate.additiveBounds.smulCost_le scalar value
    | mul left right =>
        simp only [algebra, RandCosted.liftCosted,
          RandCostedT.liftCosted] at hresult
        rw [PMF.mem_support_pure_iff] at hresult
        subst result
        exact certificate.scalarMulBounds.mulCost_le left right

/-- Three scalar actions and one scalar multiplication generate a real DDH tuple. -/
def ParamEfficiencyCertificate.realChallengeBudget
    {pp : PublicParam.{uScalar, uGroup}}
    (certificate : ParamEfficiencyCertificate pp) : Cost :=
  certificate.additiveBounds.smulBudget +
    certificate.additiveBounds.smulBudget +
    certificate.scalarMulBounds.mulBudget +
    certificate.additiveBounds.smulBudget

/-- Two scalar samples followed by real-tuple generation. -/
def ParamEfficiencyCertificate.realSampleTailBudget
    {pp : PublicParam.{uScalar, uGroup}}
    (certificate : ParamEfficiencyCertificate pp) : Cost :=
  certificate.scalarSamplerBounds.sampleBudget +
    certificate.scalarSamplerBounds.sampleBudget +
    certificate.realChallengeBudget

/-- Two scalar actions generate the public exponents in a random DDH tuple. -/
def ParamEfficiencyCertificate.randomChallengeBudget
    {pp : PublicParam.{uScalar, uGroup}}
    (certificate : ParamEfficiencyCertificate pp) : Cost :=
  certificate.additiveBounds.smulBudget +
    certificate.additiveBounds.smulBudget

/-- Two scalar samples, one group sample, and random-tuple construction. -/
def ParamEfficiencyCertificate.randomSampleTailBudget
    {pp : PublicParam.{uScalar, uGroup}}
    (certificate : ParamEfficiencyCertificate pp) : Cost :=
  certificate.scalarSamplerBounds.sampleBudget +
    certificate.scalarSamplerBounds.sampleBudget +
    certificate.carrierSamplerBounds.sampleBudget +
    certificate.randomChallengeBudget

/-- A security-parameter-indexed family of native costed DDH public parameters. -/
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
The family-level typed operations used by complete DDH sampling.

Setup selects the dependent scalar and carrier types for every later call.
The high `ULift`s only place those result types in the same universe as the
public parameter; the family handler preserves their values and exact costs.
-/
inductive FamilyOp (F : Family.{uScalar, uGroup}) :
    Type (max (uScalar + 1) (uGroup + 1)) →
      Type (max (uScalar + 1) (uGroup + 1) + 1) where
  | setup (sec : Crypto.SecPar) :
      FamilyOp F PublicParam.{uScalar, uGroup}
  | sampleScalar (pp : PublicParam.{uScalar, uGroup}) :
      FamilyOp F
        (ULift.{max (uScalar + 1) (uGroup + 1)} pp.Scalar)
  | sampleCarrier (pp : PublicParam.{uScalar, uGroup}) :
      FamilyOp F
        (ULift.{max (uScalar + 1) (uGroup + 1)} pp.Carrier)
  | smul (pp : PublicParam.{uScalar, uGroup})
      (scalar : pp.Scalar) (value : pp.Carrier) :
      FamilyOp F
        (ULift.{max (uScalar + 1) (uGroup + 1)} pp.Carrier)
  | mul (pp : PublicParam.{uScalar, uGroup})
      (left right : pp.Scalar) :
      FamilyOp F
        (ULift.{max (uScalar + 1) (uGroup + 1)} pp.Scalar)

/-- The dependent typed signature for complete DDH family computations. -/
def familySignature (F : Family.{uScalar, uGroup}) : Signature where
  Op := FamilyOp F

/--
The sole exact family-level DDH handler.

All parameter-local operations delegate to `algebra pp`; this handler adds
only setup-dependent dispatch and result-universe lifting.
-/
noncomputable def familyAlgebra (F : Family.{uScalar, uGroup}) :
    CostedAlgebra natCostModel (familySignature F) where
  exec operation :=
    match operation with
    | .setup sec => F.setup sec
    | .sampleScalar pp =>
        RandCosted.map (fun result => ULift.up result.down)
          ((algebra pp).exec .sampleScalar)
    | .sampleCarrier pp =>
        RandCosted.map (fun result => ULift.up result.down)
          ((algebra pp).exec .sampleCarrier)
    | .smul pp scalar value =>
        RandCosted.map (fun result => ULift.up result.down)
          ((algebra pp).exec (.smul scalar value))
    | .mul pp left right =>
        RandCosted.map (fun result => ULift.up result.down)
          ((algebra pp).exec (.mul left right))

/-- Cost-erased specifications for setup and all delegated DDH operations. -/
noncomputable def familyAlgebraLaws (F : Family.{uScalar, uGroup}) :
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
    | .mul pp left right =>
        PMF.map (fun result => ULift.up result.down)
          ((algebraLaws pp).semantics (Op.mul left right))
  exec_spec operation := by
    cases operation with
    | setup sec => rfl
    | sampleScalar pp =>
        simp [familyAlgebra, (algebraLaws pp).exec_spec]
    | sampleCarrier pp =>
        simp [familyAlgebra, (algebraLaws pp).exec_spec]
    | smul pp scalar value =>
        simp [familyAlgebra, (algebraLaws pp).exec_spec]
    | mul pp left right =>
        simp [familyAlgebra, (algebraLaws pp).exec_spec]

/-- Setup itself is a typed DDH family-level program. -/
def setupProgram (F : Family.{uScalar, uGroup}) :
    Program (familyAlgebra F) Crypto.SecPar
      PublicParam.{uScalar, uGroup} where
  body sec := .call (.setup sec)

/-- The typed setup program is exactly the family's native setup computation. -/
@[simp] theorem setupProgram_runCosted
    (F : Family.{uScalar, uGroup}) (sec : Crypto.SecPar) :
    Program.runCosted (setupProgram F) sec = F.setup sec := by
  rfl

/-- A DDH challenge consists of public parameters and three group elements. -/
structure ChallengeInput where
  param : PublicParam.{uScalar, uGroup}
  left : param.Carrier
  right : param.Carrier
  shared : param.Carrier

/-- The three same-parameter carrier values manipulated inside a DDH program. -/
structure ChallengeValues (pp : PublicParam.{uScalar, uGroup}) where
  left : pp.Carrier
  right : pp.Carrier
  shared : pp.Carrier

/-- Package fixed-parameter program output into the public dependent challenge. -/
def ChallengeValues.toChallengeInput
    {pp : PublicParam.{uScalar, uGroup}} (values : ChallengeValues pp) :
    ChallengeInput.{uScalar, uGroup} where
  param := pp
  left := values.left
  right := values.right
  shared := values.shared

/-- The mathematical genuine DDH tuple generated by two exponents. -/
def realChallenge
    (pp : PublicParam.{uScalar, uGroup}) (leftExp rightExp : pp.Scalar) :
    ChallengeInput.{uScalar, uGroup} where
  param := pp
  left := leftExp • pp.generator
  right := rightExp • pp.generator
  shared := (leftExp * rightExp) • pp.generator

@[simp] theorem realChallenge_shared_eq_nestedAction
    (pp : PublicParam.{uScalar, uGroup}) (leftExp rightExp : pp.Scalar) :
    (realChallenge pp leftExp rightExp).shared =
      leftExp • (rightExp • pp.generator) :=
  pp.mulScalarAction leftExp rightExp

/-- The mathematical random DDH tuple with an independently sampled third element. -/
def randomChallenge
    (pp : PublicParam.{uScalar, uGroup})
    (leftExp rightExp : pp.Scalar) (shared : pp.Carrier) :
    ChallengeInput.{uScalar, uGroup} where
  param := pp
  left := leftExp • pp.generator
  right := rightExp • pp.generator
  shared := shared

/-- Genuine DDH tuple construction as a typed primitive program. -/
def realChallengeProgram (pp : PublicParam.{uScalar, uGroup}) :
    Program (algebra pp) (pp.Scalar × pp.Scalar)
      (ULift.{uScalar} (ChallengeValues pp)) where
  body input :=
    .bind (.call (.smul input.1 pp.generator)) fun left =>
      .bind (.call (.smul input.2 pp.generator)) fun right =>
        .bind (.call (.mul input.1 input.2)) fun product =>
          .bind (.call (.smul product.down pp.generator)) fun shared =>
            .pure
              (ULift.up
                {
                  left := left.down
                  right := right.down
                  shared := shared.down
                })

/-- Random DDH tuple construction as a typed primitive program. -/
def randomChallengeProgram (pp : PublicParam.{uScalar, uGroup}) :
    Program (algebra pp) (pp.Scalar × pp.Scalar × pp.Carrier)
      (ULift.{uScalar} (ChallengeValues pp)) where
  body input :=
    .bind (.call (.smul input.1 pp.generator)) fun left =>
      .bind (.call (.smul input.2.1 pp.generator)) fun right =>
        .pure
          (ULift.up
            {
              left := left.down
              right := right.down
              shared := input.2.2
            })

/-- Structural budget certificate for genuine tuple construction. -/
noncomputable def realChallengeBoundedProgram
    (pp : PublicParam.{uScalar, uGroup})
    (certificate : ParamEfficiencyCertificate pp) :
    Program.BoundedProgram
      (Input := pp.Scalar × pp.Scalar)
      (Output := ULift.{uScalar} (ChallengeValues pp))
      (operationBounds pp certificate)
      (fun _input => certificate.realChallengeBudget) where
  program := realChallengeProgram pp
  certificate := by
    intro input
    simpa [realChallengeProgram,
      ParamEfficiencyCertificate.realChallengeBudget, add_assoc] using
      Program.Code.Bound.bind
        (Program.Code.Bound.call
          (A := algebra pp) (Op.smul input.1 pp.generator))
        fun (left : ULift.{uScalar} pp.Carrier) =>
          Program.Code.Bound.bind
            (Program.Code.Bound.call
              (A := algebra pp) (Op.smul input.2 pp.generator))
            fun (right : ULift.{uScalar} pp.Carrier) =>
              Program.Code.Bound.bind
                (Program.Code.Bound.call
                  (A := algebra pp) (Op.mul input.1 input.2))
                fun (product : ULift.{uGroup} pp.Scalar) =>
                  Program.Code.Bound.bind
                    (Program.Code.Bound.call
                      (A := algebra pp)
                      (Op.smul product.down pp.generator))
                    fun (shared : ULift.{uScalar} pp.Carrier) =>
                      Program.Code.Bound.pure
                        (A := algebra pp)
                        (ULift.up
                          ({
                            left := left.down
                            right := right.down
                            shared := shared.down
                          } : ChallengeValues pp))

/-- Structural budget certificate for random tuple construction. -/
noncomputable def randomChallengeBoundedProgram
    (pp : PublicParam.{uScalar, uGroup})
    (certificate : ParamEfficiencyCertificate pp) :
    Program.BoundedProgram
      (Input := pp.Scalar × pp.Scalar × pp.Carrier)
      (Output := ULift.{uScalar} (ChallengeValues pp))
      (operationBounds pp certificate)
      (fun _input => certificate.randomChallengeBudget) where
  program := randomChallengeProgram pp
  certificate := by
    intro input
    simpa [randomChallengeProgram,
      ParamEfficiencyCertificate.randomChallengeBudget,
      add_assoc] using
      Program.Code.Bound.bind
        (Program.Code.Bound.call
          (A := algebra pp) (Op.smul input.1 pp.generator))
        fun (left : ULift.{uScalar} pp.Carrier) =>
          Program.Code.Bound.bind
            (Program.Code.Bound.call
              (A := algebra pp) (Op.smul input.2.1 pp.generator))
            fun (right : ULift.{uScalar} pp.Carrier) =>
              Program.Code.Bound.pure
                (A := algebra pp)
                (ULift.up
                  ({
                    left := left.down
                    right := right.down
                    shared := input.2.2
                  } : ChallengeValues pp))

/--
Costed construction of a genuine DDH tuple.

All algebraic operations are taken directly from the public parameter.
-/
def realChallengeComputation
    (pp : PublicParam.{uScalar, uGroup})
    (leftExp rightExp : pp.Scalar) :
    Costed ChallengeInput.{uScalar, uGroup} :=
  Costed.bind (pp.backend.smul leftExp pp.generator) fun left =>
    Costed.bind (pp.backend.smul rightExp pp.generator) fun right =>
      Costed.bind (pp.scalarMulBackend.mul leftExp rightExp) fun product =>
        Costed.bind (pp.backend.smul product pp.generator) fun shared =>
          Costed.pure
            {
              param := pp
              left := left
              right := right
              shared := shared
            }

/-- Erasing operation costs recovers the mathematical real DDH tuple. -/
@[simp] theorem realChallengeComputation_value
    (pp : PublicParam.{uScalar, uGroup})
    (leftExp rightExp : pp.Scalar) :
    (realChallengeComputation pp leftExp rightExp).val =
      realChallenge pp leftExp rightExp := by
  simp [realChallengeComputation, Costed.bind, realChallenge]

/-- The exact path cost records all three scalar actions and scalar multiplication. -/
@[simp] theorem realChallengeComputation_cost
    (pp : PublicParam.{uScalar, uGroup})
    (leftExp rightExp : pp.Scalar) :
    (realChallengeComputation pp leftExp rightExp).cost =
      (pp.backend.smul leftExp pp.generator).cost +
        (pp.backend.smul rightExp pp.generator).cost +
        (pp.scalarMulBackend.mul leftExp rightExp).cost +
        (pp.backend.smul (leftExp * rightExp) pp.generator).cost := by
  simp [realChallengeComputation, CostedT.bind, CostedT.pure,
    add_assoc]

/-- Every genuine DDH tuple construction satisfies its parameter-local budget. -/
theorem realChallengeComputation_cost_le
    (pp : PublicParam.{uScalar, uGroup})
    (certificate : ParamEfficiencyCertificate pp)
    (leftExp rightExp : pp.Scalar) :
    (realChallengeComputation pp leftExp rightExp).cost ≤
      certificate.realChallengeBudget := by
  rw [realChallengeComputation_cost]
  simpa [ParamEfficiencyCertificate.realChallengeBudget, add_assoc] using
    Nat.add_le_add
      (certificate.additiveBounds.smulCost_le leftExp pp.generator)
      (Nat.add_le_add
        (certificate.additiveBounds.smulCost_le rightExp pp.generator)
        (Nat.add_le_add
          (certificate.scalarMulBounds.mulCost_le leftExp rightExp)
          (certificate.additiveBounds.smulCost_le
            (leftExp * rightExp) pp.generator)))

/--
Mapping the typed real-tuple output back to the public challenge package gives
exactly the legacy deterministic compatibility computation.
-/
@[simp] theorem realChallengeProgram_runCosted
    (pp : PublicParam.{uScalar, uGroup})
    (leftExp rightExp : pp.Scalar) :
    RandCosted.map
        (fun values => ChallengeValues.toChallengeInput values.down)
        (Program.runCosted (realChallengeProgram pp) (leftExp, rightExp)) =
      RandCosted.liftCosted
        (realChallengeComputation pp leftExp rightExp) := by
  simp [Program.runCosted, realChallengeProgram, Program.Code.runCosted,
    algebra, realChallengeComputation, RandCosted.map, RandCostedT.map,
    RandCosted.liftCosted, RandCostedT.liftCosted, Costed.bind,
    CostedT.bind, CostedT.map, PMF.pure_bind, PMF.pure_map,
    ChallengeValues.toChallengeInput]

/-- Sampling both exponents and constructing a real tuple as one program. -/
def realSampleTailProgram (pp : PublicParam.{uScalar, uGroup}) :
    Program (algebra pp) Unit
      (ULift.{uScalar} (ChallengeValues pp)) where
  body _input :=
    .bind (.call .sampleScalar) fun leftExp =>
      .bind (.call .sampleScalar) fun rightExp =>
        (realChallengeProgram pp).body (leftExp.down, rightExp.down)

/-- Structural budget certificate for the single genuine-sample tail program. -/
noncomputable def realSampleTailBoundedProgram
    (pp : PublicParam.{uScalar, uGroup})
    (certificate : ParamEfficiencyCertificate pp) :
    Program.BoundedProgram
      (Input := Unit)
      (Output := ULift.{uScalar} (ChallengeValues pp))
      (operationBounds pp certificate)
      (fun _input => certificate.realSampleTailBudget) where
  program := realSampleTailProgram pp
  certificate := by
    intro input
    simpa [realSampleTailProgram,
      realChallengeBoundedProgram,
      ParamEfficiencyCertificate.realSampleTailBudget,
      add_assoc] using
      Program.Code.Bound.bind
        (Program.Code.Bound.call (A := algebra pp) Op.sampleScalar)
        fun (leftExp : ULift.{uGroup} pp.Scalar) =>
          Program.Code.Bound.bind
            (Program.Code.Bound.call (A := algebra pp) Op.sampleScalar)
            fun (rightExp : ULift.{uGroup} pp.Scalar) =>
              (realChallengeBoundedProgram pp certificate).certificate
                (leftExp.down, rightExp.down)

/-- The two exponent samples plus real-tuple construction at a fixed parameter. -/
noncomputable def realSampleTailComputation
    (pp : PublicParam.{uScalar, uGroup}) :
    RandCosted ChallengeInput.{uScalar, uGroup} :=
  RandCosted.map
    (fun values => ChallengeValues.toChallengeInput values.down)
    (Program.runCosted (realSampleTailProgram pp) ())

/-- Every fixed-parameter real-sample tail satisfies its compositional budget. -/
theorem realSampleTailComputation_cost_le
    (pp : PublicParam.{uScalar, uGroup})
    (certificate : ParamEfficiencyCertificate pp) :
    ∀ result, result ∈ (realSampleTailComputation pp).support →
      result.cost ≤ certificate.realSampleTailBudget := by
  intro result hresult
  simp only [realSampleTailComputation, RandCosted.map,
    RandCostedT.map] at hresult
  rw [PMF.mem_support_map_iff] at hresult
  rcases hresult with ⟨values, hvalues, hresult⟩
  subst result
  exact (realSampleTailBoundedProgram pp certificate).costBound ()
    values hvalues

/--
Complete genuine-DDH sampling, including setup and every setup-dependent
primitive, as one typed program.

There is deliberately no family-wide `OperationBounds`: setup may choose
parameters with different local certificates.  Parameter-local structural
bounds and the existing family `EfficiencyCertificate` remain the separate
upper-bound layer.
-/
def realSampleProgram (F : Family.{uScalar, uGroup}) :
    Program (familyAlgebra F) Crypto.SecPar
      ChallengeInput.{uScalar, uGroup} where
  body sec :=
    .bind (.call (.setup sec)) fun pp =>
      .bind (.call (.sampleScalar pp)) fun leftExp =>
        .bind (.call (.sampleScalar pp)) fun rightExp =>
          .bind (.call (.smul pp leftExp.down pp.generator)) fun left =>
            .bind (.call (.smul pp rightExp.down pp.generator)) fun right =>
              .bind (.call (.mul pp leftExp.down rightExp.down)) fun product =>
                .bind (.call (.smul pp product.down pp.generator)) fun shared =>
                  .pure
                    {
                      param := pp
                      left := left.down
                      right := right.down
                      shared := shared.down
                    }

/-- Costed generation of a genuine DDH challenge, including setup and sampling. -/
noncomputable def realSampleComputation
    (F : Family.{uScalar, uGroup}) (sec : Crypto.SecPar) :
    RandCosted ChallengeInput.{uScalar, uGroup} :=
  Program.runCosted (realSampleProgram F) sec

/--
The full genuine-sample program is exactly setup followed by the existing
fixed-parameter tail, including every path cost.
-/
@[simp] theorem realSampleProgram_runCosted_eq_bind_tail
    (F : Family.{uScalar, uGroup}) (sec : Crypto.SecPar) :
    Program.runCosted (realSampleProgram F) sec =
      RandCosted.bind (F.setup sec) realSampleTailComputation := by
  simp only [Program.runCosted, realSampleProgram, Program.Code.runCosted,
    familyAlgebra, realSampleTailComputation, realSampleTailProgram,
    realChallengeProgram, algebra, RandCosted.map, RandCosted.bind,
    RandCostedT.map, RandCostedT.bind, PMF.map_bind, PMF.bind_map,
    PMF.map_comp, Function.comp_def]
  apply congrArg (PMF.bind (F.setup sec))
  funext setupResult
  cases setupResult with
  | mk pp setupCost =>
      apply congrArg (PMF.bind pp.scalarSampler.sample)
      funext leftSample
      cases leftSample with
      | mk leftExp leftSampleCost =>
          apply congrArg (PMF.bind pp.scalarSampler.sample)
          funext rightSample
          cases rightSample with
          | mk rightExp rightSampleCost =>
              cases hleft : pp.backend.smul leftExp pp.generator with
              | mk leftValue leftCost =>
                  have hleftValue : leftValue = leftExp • pp.generator := by
                    simpa using (congrArg Costed.val hleft).symm
                  subst leftValue
                  cases hright : pp.backend.smul rightExp pp.generator with
                  | mk rightValue rightCost =>
                      have hrightValue :
                          rightValue = rightExp • pp.generator := by
                        simpa using (congrArg Costed.val hright).symm
                      subst rightValue
                      cases hproduct :
                          pp.scalarMulBackend.mul leftExp rightExp with
                      | mk productValue productCost =>
                          have hproductValue :
                              productValue = leftExp * rightExp := by
                            simpa using
                              (congrArg Costed.val hproduct).symm
                          subst productValue
                          cases hshared :
                              pp.backend.smul (leftExp * rightExp)
                                pp.generator with
                          | mk sharedValue sharedCost =>
                              have hsharedValue :
                                  sharedValue =
                                    (leftExp * rightExp) • pp.generator := by
                                simpa using
                                  (congrArg Costed.val hshared).symm
                              subst sharedValue
                              simp [RandCosted.liftCosted,
                                RandCostedT.pure,
                                RandCostedT.liftCosted, CostedT.bind,
                                CostedT.map, CostedT.pure, PMF.pure_map,
                                ChallengeValues.toChallengeInput]

/-- Compatibility form of genuine DDH sampling for existing bound proofs. -/
@[simp] theorem realSampleComputation_eq_bind_tail
    (F : Family.{uScalar, uGroup}) (sec : Crypto.SecPar) :
    realSampleComputation F sec =
      RandCosted.bind (F.setup sec) realSampleTailComputation := by
  exact realSampleProgram_runCosted_eq_bind_tail F sec

/--
The real DDH distribution is obtained only by erasing costs from the native
costed computation.
-/
noncomputable def realSample
    (F : Family.{uScalar, uGroup}) :
    Crypto.SecPar → PMF ChallengeInput.{uScalar, uGroup} :=
  fun sec => RandCosted.valueDist (realSampleComputation F sec)

@[simp] theorem realSampleComputation_valueDist
    (F : Family.{uScalar, uGroup}) (sec : Crypto.SecPar) :
    RandCosted.valueDist (realSampleComputation F sec) = realSample F sec :=
  rfl

/-- Costed construction of a random DDH tuple from fixed sampled values. -/
def randomChallengeComputation
    (pp : PublicParam.{uScalar, uGroup})
    (leftExp rightExp : pp.Scalar) (sampledShared : pp.Carrier) :
    Costed ChallengeInput.{uScalar, uGroup} :=
  Costed.bind (pp.backend.smul leftExp pp.generator) fun left =>
    Costed.bind (pp.backend.smul rightExp pp.generator) fun right =>
      Costed.pure
        {
          param := pp
          left := left
          right := right
          shared := sampledShared
        }

/-- Erasing operation costs recovers the mathematical random DDH tuple. -/
@[simp] theorem randomChallengeComputation_value
    (pp : PublicParam.{uScalar, uGroup})
    (leftExp rightExp : pp.Scalar) (sampledShared : pp.Carrier) :
    (randomChallengeComputation pp leftExp rightExp sampledShared).val =
      randomChallenge pp leftExp rightExp sampledShared := by
  simp [randomChallengeComputation, Costed.bind, randomChallenge]

/-- The exact random-tuple construction cost is its two scalar actions. -/
@[simp] theorem randomChallengeComputation_cost
    (pp : PublicParam.{uScalar, uGroup})
    (leftExp rightExp : pp.Scalar) (sampledShared : pp.Carrier) :
    (randomChallengeComputation pp leftExp rightExp sampledShared).cost =
      (pp.backend.smul leftExp pp.generator).cost +
        (pp.backend.smul rightExp pp.generator).cost :=
  rfl

/-- Random DDH tuple construction satisfies its parameter-local budget. -/
theorem randomChallengeComputation_cost_le
    (pp : PublicParam.{uScalar, uGroup})
    (certificate : ParamEfficiencyCertificate pp)
    (leftExp rightExp : pp.Scalar) (sampledShared : pp.Carrier) :
    (randomChallengeComputation pp leftExp rightExp sampledShared).cost ≤
      certificate.randomChallengeBudget :=
  Nat.add_le_add
    (certificate.additiveBounds.smulCost_le leftExp pp.generator)
    (certificate.additiveBounds.smulCost_le rightExp pp.generator)

/--
Mapping the typed random-tuple output back to the public challenge package
gives exactly the legacy deterministic compatibility computation.
-/
@[simp] theorem randomChallengeProgram_runCosted
    (pp : PublicParam.{uScalar, uGroup})
    (leftExp rightExp : pp.Scalar) (sampledShared : pp.Carrier) :
    RandCosted.map
        (fun values => ChallengeValues.toChallengeInput values.down)
        (Program.runCosted (randomChallengeProgram pp)
          (leftExp, rightExp, sampledShared)) =
      RandCosted.liftCosted
        (randomChallengeComputation pp leftExp rightExp sampledShared) := by
  simp [Program.runCosted, randomChallengeProgram, Program.Code.runCosted,
    algebra, randomChallengeComputation, RandCosted.map, RandCostedT.map,
    RandCosted.liftCosted, RandCostedT.liftCosted, Costed.bind,
    CostedT.bind, CostedT.map, PMF.pure_bind, PMF.pure_map,
    ChallengeValues.toChallengeInput]

/-- Sampling all random values and constructing a random tuple as one program. -/
def randomSampleTailProgram (pp : PublicParam.{uScalar, uGroup}) :
    Program (algebra pp) Unit
      (ULift.{uScalar} (ChallengeValues pp)) where
  body _input :=
    .bind (.call .sampleScalar) fun leftExp =>
      .bind (.call .sampleScalar) fun rightExp =>
        .bind (.call .sampleCarrier) fun sampledShared =>
          (randomChallengeProgram pp).body
            (leftExp.down, rightExp.down, sampledShared.down)

/-- Structural budget certificate for the single random-sample tail program. -/
noncomputable def randomSampleTailBoundedProgram
    (pp : PublicParam.{uScalar, uGroup})
    (certificate : ParamEfficiencyCertificate pp) :
    Program.BoundedProgram
      (Input := Unit)
      (Output := ULift.{uScalar} (ChallengeValues pp))
      (operationBounds pp certificate)
      (fun _input => certificate.randomSampleTailBudget) where
  program := randomSampleTailProgram pp
  certificate := by
    intro input
    simpa [randomSampleTailProgram,
      randomChallengeBoundedProgram,
      ParamEfficiencyCertificate.randomSampleTailBudget,
      add_assoc] using
      Program.Code.Bound.bind
        (Program.Code.Bound.call (A := algebra pp) Op.sampleScalar)
        fun (leftExp : ULift.{uGroup} pp.Scalar) =>
          Program.Code.Bound.bind
            (Program.Code.Bound.call (A := algebra pp) Op.sampleScalar)
            fun (rightExp : ULift.{uGroup} pp.Scalar) =>
              Program.Code.Bound.bind
                (Program.Code.Bound.call (A := algebra pp) Op.sampleCarrier)
                fun (sampledShared : ULift.{uScalar} pp.Carrier) =>
                  (randomChallengeBoundedProgram pp certificate).certificate
                    (leftExp.down, rightExp.down, sampledShared.down)

/-- The fixed-parameter randomized DDH sampling tail. -/
noncomputable def randomSampleTailComputation
    (pp : PublicParam.{uScalar, uGroup}) :
    RandCosted ChallengeInput.{uScalar, uGroup} :=
  RandCosted.map
    (fun values => ChallengeValues.toChallengeInput values.down)
    (Program.runCosted (randomSampleTailProgram pp) ())

/-- Every fixed-parameter random-sample tail satisfies its compositional budget. -/
theorem randomSampleTailComputation_cost_le
    (pp : PublicParam.{uScalar, uGroup})
    (certificate : ParamEfficiencyCertificate pp) :
    ∀ result, result ∈ (randomSampleTailComputation pp).support →
      result.cost ≤ certificate.randomSampleTailBudget := by
  intro result hresult
  simp only [randomSampleTailComputation, RandCosted.map,
    RandCostedT.map] at hresult
  rw [PMF.mem_support_map_iff] at hresult
  rcases hresult with ⟨values, hvalues, hresult⟩
  subst result
  exact (randomSampleTailBoundedProgram pp certificate).costBound ()
    values hvalues

/--
Complete random-DDH sampling, including setup and every setup-dependent
primitive, as one typed program.
-/
def randomSampleProgram (F : Family.{uScalar, uGroup}) :
    Program (familyAlgebra F) Crypto.SecPar
      ChallengeInput.{uScalar, uGroup} where
  body sec :=
    .bind (.call (.setup sec)) fun pp =>
      .bind (.call (.sampleScalar pp)) fun leftExp =>
        .bind (.call (.sampleScalar pp)) fun rightExp =>
          .bind (.call (.sampleCarrier pp)) fun sampledShared =>
            .bind (.call (.smul pp leftExp.down pp.generator)) fun left =>
              .bind (.call (.smul pp rightExp.down pp.generator)) fun right =>
                .pure
                  {
                    param := pp
                    left := left.down
                    right := right.down
                    shared := sampledShared.down
                  }

/-- Costed generation of a random DDH challenge, including setup and sampling. -/
noncomputable def randomSampleComputation
    (F : Family.{uScalar, uGroup}) (sec : Crypto.SecPar) :
    RandCosted ChallengeInput.{uScalar, uGroup} :=
  Program.runCosted (randomSampleProgram F) sec

/--
The full random-sample program is exactly setup followed by the existing
fixed-parameter tail, including every path cost.
-/
@[simp] theorem randomSampleProgram_runCosted_eq_bind_tail
    (F : Family.{uScalar, uGroup}) (sec : Crypto.SecPar) :
    Program.runCosted (randomSampleProgram F) sec =
      RandCosted.bind (F.setup sec) randomSampleTailComputation := by
  simp only [Program.runCosted, randomSampleProgram, Program.Code.runCosted,
    familyAlgebra, randomSampleTailComputation, randomSampleTailProgram,
    randomChallengeProgram, algebra, RandCosted.map, RandCosted.bind,
    RandCostedT.map, RandCostedT.bind, PMF.map_bind, PMF.bind_map,
    PMF.map_comp, Function.comp_def]
  apply congrArg (PMF.bind (F.setup sec))
  funext setupResult
  cases setupResult with
  | mk pp setupCost =>
      apply congrArg (PMF.bind pp.scalarSampler.sample)
      funext leftSample
      cases leftSample with
      | mk leftExp leftSampleCost =>
          apply congrArg (PMF.bind pp.scalarSampler.sample)
          funext rightSample
          cases rightSample with
          | mk rightExp rightSampleCost =>
              apply congrArg (PMF.bind pp.carrierSampler.sample)
              funext carrierSample
              cases carrierSample with
              | mk sampledShared carrierSampleCost =>
                  cases hleft : pp.backend.smul leftExp pp.generator with
                  | mk leftValue leftCost =>
                      have hleftValue :
                          leftValue = leftExp • pp.generator := by
                        simpa using (congrArg Costed.val hleft).symm
                      subst leftValue
                      cases hright :
                          pp.backend.smul rightExp pp.generator with
                      | mk rightValue rightCost =>
                          have hrightValue :
                              rightValue = rightExp • pp.generator := by
                            simpa using
                              (congrArg Costed.val hright).symm
                          subst rightValue
                          simp [RandCosted.liftCosted,
                            RandCostedT.pure, RandCostedT.liftCosted,
                            CostedT.bind, CostedT.map, CostedT.pure,
                            PMF.pure_map,
                            ChallengeValues.toChallengeInput]

/-- Compatibility form of random DDH sampling for existing bound proofs. -/
@[simp] theorem randomSampleComputation_eq_bind_tail
    (F : Family.{uScalar, uGroup}) (sec : Crypto.SecPar) :
    randomSampleComputation F sec =
      RandCosted.bind (F.setup sec) randomSampleTailComputation := by
  exact randomSampleProgram_runCosted_eq_bind_tail F sec

/--
The random DDH distribution is obtained only by erasing costs from the native
costed computation.
-/
noncomputable def randomSample
    (F : Family.{uScalar, uGroup}) :
    Crypto.SecPar → PMF ChallengeInput.{uScalar, uGroup} :=
  fun sec => RandCosted.valueDist (randomSampleComputation F sec)

@[simp] theorem randomSampleComputation_valueDist
    (F : Family.{uScalar, uGroup}) (sec : Crypto.SecPar) :
    RandCosted.valueDist (randomSampleComputation F sec) =
      randomSample F sec :=
  rfl

/--
Global efficiency bounds for a DDH family.

The exact family and the DDH assumption do not depend on this certificate.
-/
structure EfficiencyCertificate (F : Family.{uScalar, uGroup}) where
  setupBudget : Crypto.SecPar → Cost
  setupCostBound :
    RandomizedComputation.CostBound
      (fun sec (_input : Unit) => F.setup sec) setupBudget
  realSampleBudget : Crypto.SecPar → Cost
  realSampleCostBound :
    RandomizedComputation.CostBound
      (fun sec (_input : Unit) => realSampleComputation F sec)
      realSampleBudget
  randomSampleBudget : Crypto.SecPar → Cost
  randomSampleCostBound :
    RandomizedComputation.CostBound
      (fun sec (_input : Unit) => randomSampleComputation F sec)
      randomSampleBudget

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

/-- Genuine-DDH sampling satisfies the supplied global efficiency certificate. -/
theorem realSampleComputation_costBound
    (F : Family.{uScalar, uGroup}) (certificate : EfficiencyCertificate F) :
    RandomizedComputation.CostBound
      (fun sec (_input : Unit) => realSampleComputation F sec)
      certificate.realSampleBudget :=
  certificate.realSampleCostBound

/-- The global real-sample certificate bounds the authoritative full program. -/
theorem realSampleProgram_costBound
    (F : Family.{uScalar, uGroup}) (certificate : EfficiencyCertificate F) :
    Program.CostBound (realSampleProgram F)
      certificate.realSampleBudget := by
  intro sec result hresult
  exact certificate.realSampleCostBound sec () result hresult

/-- Random-DDH sampling satisfies the supplied global efficiency certificate. -/
theorem randomSampleComputation_costBound
    (F : Family.{uScalar, uGroup}) (certificate : EfficiencyCertificate F) :
    RandomizedComputation.CostBound
      (fun sec (_input : Unit) => randomSampleComputation F sec)
      certificate.randomSampleBudget :=
  certificate.randomSampleCostBound

/-- The global random-sample certificate bounds the authoritative full program. -/
theorem randomSampleProgram_costBound
    (F : Family.{uScalar, uGroup}) (certificate : EfficiencyCertificate F) :
    Program.CostBound (randomSampleProgram F)
      certificate.randomSampleBudget := by
  intro sec result hresult
  exact certificate.randomSampleCostBound sec () result hresult

/-- Exact compositional bounds for a fixed DDH parameter family. -/
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
  realSampleBudget :=
    fun _sec => setupCost + paramCertificate.realSampleTailBudget
  realSampleCostBound := by
    intro sec input result hresult
    change result ∈
      (realSampleComputation (Family.ofFixed pp setupCost) sec).support
        at hresult
    rw [realSampleComputation_eq_bind_tail] at hresult
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
      (realSampleTailComputation_cost_le pp paramCertificate
        tailResult htailResult)
      setupCost
  randomSampleBudget :=
    fun _sec => setupCost + paramCertificate.randomSampleTailBudget
  randomSampleCostBound := by
    intro sec input result hresult
    change result ∈
      (randomSampleComputation (Family.ofFixed pp setupCost) sec).support
        at hresult
    rw [randomSampleComputation_eq_bind_tail] at hresult
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
      (randomSampleTailComputation_cost_le pp paramCertificate
        tailResult htailResult)
      setupCost

/-- The distinguishing problem induced by a native costed DDH family. -/
noncomputable def ddhProblem
    (F : Family.{uScalar, uGroup}) :
    Crypto.Infrastructure.GameBased.Distinguishing.Problem
      ChallengeInput.{uScalar, uGroup} where
  left := realSample F
  right := randomSample F

/-- The Decisional Diffie-Hellman assumption for a native costed family. -/
def Assumption (F : Family.{uScalar, uGroup}) : Prop :=
  Crypto.Infrastructure.GameBased.Distinguishing.Hard (ddhProblem F)

end DDH

end Crypto.Assumption.DL

import CryptoLib.Core.Assumption.DL.DLog
import CryptoLib.Core.Infrastructure.Probability.Uniform
import Mathlib.Data.ZMod.Basic

namespace CryptoLib.Test.Assumption.DL.DLog

open scoped DLogParameter

open CryptoLib.Core.Assumption.DL.DLog
open CryptoLib.Core.Infrastructure.Complexity
open CryptoLib.Core.Infrastructure.Computation
open CryptoLib.Core.Infrastructure.Computation.Algebra
open CryptoLib.Core.Infrastructure.Computation.Cost

universe uAdversaryCost

/-- The mathematical parameter contains no execution backend or sampler. -/
def testMath : MathematicalParam (ZMod 2) (ZMod 2) where
  addGroup := inferInstance
  fintypeCarrier := inferInstance
  fintypeScalar := inferInstance
  smul := inferInstance
  generator := 1
  generator_generates := by
    intro value
    exact ⟨value, by simp⟩

/-- One exact typed handler is the sole source of DLog path costs. -/
noncomputable def testAlgebra :
    CostedAlgebra CostModel.nat (signature testMath) where
  exec operation :=
    match operation with
    | .sampleScalar =>
        RandCosted.sampleWithCost
          (PMF.map ULift.up
            (@CryptoLib.Core.Infrastructure.Probability.uniformPMF
              testMath.Scalar testMath.fintypeScalar
              (@CryptoLib.Core.Assumption.DL.Parameter.scalarNonemptyOfGenerator
                testMath.Scalar testMath.Carrier testMath.addGroup testMath.smul
                testMath.generator testMath.generator_generates)))
          (fun _ => 2)
    | .smul scalar value =>
        RandCosted.liftCosted
          (⟨ULift.up (testMath.smul.smul scalar value), 11⟩ :
            Costed CostModel.nat (ULift testMath.Carrier))

noncomputable def testLaws : ExactLaws testAlgebra where
  sampleScalar := RandCosted.valueDist_sampleWithCost _ _
  smul _scalar _value := RandCosted.valueDist_liftCosted _

noncomputable def testPublicParam :
    PublicParam CostModel.nat (ZMod 2) (ZMod 2) where
  toCyclicAction := testMath
  algebra := testAlgebra
  laws := testLaws

noncomputable def testBounds : OperationBounds testAlgebra where
  budget operation :=
    match operation with
    | .sampleScalar => 2
    | .smul _ _ => 11
  cost_le operation result hresult := by
    cases operation with
    | sampleScalar =>
        simp only [testAlgebra, RandCosted.sampleWithCost] at hresult
        rw [PMF.mem_support_map_iff] at hresult
        rcases hresult with ⟨value, _hvalue, hresult⟩
        subst result
        exact Nat.le_refl 2
    | smul scalar value =>
        simp only [testAlgebra, RandCosted.liftCosted] at hresult
        rw [PMF.mem_support_pure_iff] at hresult
        subst result
        exact Nat.le_refl 11

noncomputable def testParamEfficiency :
    ParamEfficiencyCertificate testPublicParam where
  bounds := testBounds
  sampleScalarBudget := 2
  sampleScalarBudget_sound := Nat.le_refl 2
  smulBudget := 11
  smulBudget_sound := by intros; exact Nat.le_refl 11

noncomputable def testFamily : Family CostModel.nat (ZMod 2) (ZMod 2) :=
  Family.ofFixed testPublicParam 3

example : Prop := Assumption CostModel.nat NatMeasure.nat testFamily

/-- Algorithm and adversary costs are independent parameters of the assumption. -/
example (adversaryModel : CostModel.{uAdversaryCost})
    (measure : NatMeasure adversaryModel) : Prop :=
  Assumption adversaryModel measure testFamily

example (sec : CryptoLib.Core.SecPar) :
    Program.runCosted (setupProgram testFamily) sec = testFamily.setup sec :=
  setupProgram_runCosted testFamily sec

/-- The problem distribution is exactly the erasure of the sole sample program. -/
example (sec : CryptoLib.Core.SecPar) :
    Program.valueDist (sampleProgram testFamily) sec =
      (dLogProblem testFamily).sample sec :=
  rfl

example :
    CryptoLib.Core.Infrastructure.Computation.Program.Code.valueDist
        (A := testPublicParam.algebra) (.call Op.sampleScalar) =
      (algebraLaws testPublicParam).semantics Op.sampleScalar :=
  CryptoLib.Core.Infrastructure.Computation.Program.Code.valueDist_call_eq
    (algebraLaws testPublicParam) Op.sampleScalar

/-- The exact typed tail has the expected `2 + 11` structural bound. -/
example :
    Program.CostBound (sampleTailProgram testPublicParam) (fun _ => 13) :=
  (sampleTailBoundedProgram testPublicParam testParamEfficiency).costBound

/-- A fixed challenge receives exactly the handler's scalar-action cost. -/
example (secret : testPublicParam.Scalar) :
    Program.runCosted (challengeProgram testPublicParam) secret =
      PMF.pure
        (⟨ULift.up (testPublicParam.smul.smul secret testPublicParam.generator), 11⟩ :
          Costed CostModel.nat (ULift testPublicParam.Carrier)) :=
  rfl

/-! ## Host-computation admission regression -/

/-- Choice extracts a mathematically guaranteed logarithm without an algorithm. -/
noncomputable def chosenLog
    (challenge : ChallengeInput CostModel.nat (ZMod 2) (ZMod 2)) :
    Witness challenge :=
  Classical.choose (challenge.1.generator_generates challenge.2)

theorem chosenLog_isSolution
    (challenge : ChallengeInput CostModel.nat (ZMod 2) (ZMod 2)) :
    IsSolution challenge (chosenLog challenge) :=
  Classical.choose_spec (challenge.1.generator_generates challenge.2)

/--
The annotation layer can still describe this host function at zero annotated
cost; it deliberately does not call the result PPT.
-/
noncomputable def chosenLogTimedMachine :
    TimedMachine CostModel.nat NatMeasure.nat
      (fun _sec => ChallengeInput CostModel.nat (ZMod 2) (ZMod 2))
      (fun _sec challenge => Witness challenge) :=
  TimedMachine.ofFunction CostModel.nat NatMeasure.nat
    (fun _sec challenge => chosenLog challenge)

example : chosenLogTimedMachine.runtime = fun _sec => 0 := rfl

/-- The only promotion route exposes the exact external admission obligation. -/
noncomputable def chosenLogPPTMachine_of_admission
    (admission : PPTAdmissible CostModel.nat NatMeasure.nat
      chosenLogTimedMachine.run
      chosenLogTimedMachine.runtime) :
    PPTMachine CostModel.nat NatMeasure.nat
      (fun _sec => ChallengeInput CostModel.nat (ZMod 2) (ZMod 2))
      (fun _sec challenge => Witness challenge) :=
  PPTMachine.ofAdmittedTimedMachine chosenLogTimedMachine
    CryptoLib.Core.Infrastructure.Asymptotic.IsPolyBounded.zero admission

/-- The former zero-cost automatic promotion is no longer an available API. -/
example : True := by
  fail_if_success
    have _adversary :
        PPTMachine CostModel.nat NatMeasure.nat
          (fun _sec => ChallengeInput CostModel.nat (ZMod 2) (ZMod 2))
          (fun _sec challenge => Witness challenge) :=
      PPTMachine.ofFunction CostModel.nat NatMeasure.nat
        (fun _sec challenge => chosenLog challenge)
  trivial

end CryptoLib.Test.Assumption.DL.DLog

import Crypto.Assumption.DL.DDH
import Mathlib.Data.ZMod.Basic

namespace CryptoTest.Assumption.DL.DDH

open scoped DDHParameter

open Crypto.Assumption.DL.DDH
open Crypto.Infrastructure.Computation
open Crypto.Infrastructure.Computation.Algebra
open Crypto.Infrastructure.Computation.Cost

/-- The DDH mathematical parameter contains no costed operations or samplers. -/
def testMath : MathematicalParam where
  Scalar := ZMod 2
  Carrier := ZMod 2
  addGroup := inferInstance
  fintypeCarrier := inferInstance
  nonemptyCarrier := inferInstance
  fintypeScalar := inferInstance
  smul := inferInstance
  commMonoidScalar := inferInstance
  one_smul := by
    intro value
    exact one_smul (ZMod 2) value
  mul_smul := by
    intro left right value
    exact mul_smul left right value
  generator := 1
  generator_generates := by
    intro value
    exact ⟨value, by simp⟩

/-- The single typed algebra assigns all exact DDH primitive costs. -/
noncomputable def testAlgebra :
    CostedAlgebra CostModel.nat (signature testMath) where
  exec operation :=
    match operation with
    | .sampleScalar =>
        RandCostedT.sampleWithCost
          (PMF.map ULift.up
            (@Crypto.Infrastructure.Computation.Distribution.uniformPMF
              testMath.Scalar testMath.fintypeScalar
              ⟨testMath.commMonoidScalar.one⟩))
          (fun _ => 2)
    | .sampleCarrier =>
        RandCostedT.sampleWithCost
          (PMF.map ULift.up
            (@Crypto.Infrastructure.Computation.Distribution.uniformPMF
              testMath.Carrier testMath.fintypeCarrier
              testMath.nonemptyCarrier))
          (fun _ => 4)
    | .smul scalar value =>
        RandCostedT.liftCosted
          (⟨ULift.up (testMath.smul.smul scalar value), 11⟩ :
            CostedT CostModel.nat (ULift testMath.Carrier))
    | .add left right =>
        RandCostedT.liftCosted
          (⟨ULift.up (testMath.addGroup.add left right), 5⟩ :
            CostedT CostModel.nat (ULift testMath.Carrier))
    | .sub left right =>
        RandCostedT.liftCosted
          (⟨ULift.up (testMath.addGroup.sub left right), 6⟩ :
            CostedT CostModel.nat (ULift testMath.Carrier))
    | .mul left right =>
        RandCostedT.liftCosted
          (⟨ULift.up (testMath.commMonoidScalar.mul left right), 13⟩ :
            CostedT CostModel.nat (ULift testMath.Scalar))

noncomputable def testLaws : ExactLaws testAlgebra where
  sampleScalar := RandCostedT.valueDist_sampleWithCost _ _
  sampleCarrier := RandCostedT.valueDist_sampleWithCost _ _
  smul _scalar _value := RandCostedT.valueDist_liftCosted _
  add _left _right := RandCostedT.valueDist_liftCosted _
  sub _left _right := RandCostedT.valueDist_liftCosted _
  mul _left _right := RandCostedT.valueDist_liftCosted _

noncomputable def testPublicParam : PublicParam CostModel.nat where
  toDecisionalCyclicAction := testMath
  algebra := testAlgebra
  laws := testLaws

noncomputable def testBounds : OperationBounds testAlgebra where
  budget operation :=
    match operation with
    | .sampleScalar => 2
    | .sampleCarrier => 4
    | .smul _ _ => 11
    | .add _ _ => 5
    | .sub _ _ => 6
    | .mul _ _ => 13
  cost_le operation result hresult := by
    cases operation with
    | sampleScalar =>
        simp only [testAlgebra, RandCostedT.sampleWithCost] at hresult
        rw [PMF.mem_support_map_iff] at hresult
        rcases hresult with ⟨value, _hvalue, hresult⟩
        subst result
        exact Nat.le_refl 2
    | sampleCarrier =>
        simp only [testAlgebra, RandCostedT.sampleWithCost] at hresult
        rw [PMF.mem_support_map_iff] at hresult
        rcases hresult with ⟨value, _hvalue, hresult⟩
        subst result
        exact Nat.le_refl 4
    | smul scalar value =>
        simp only [testAlgebra, RandCostedT.liftCosted] at hresult
        rw [PMF.mem_support_pure_iff] at hresult
        subst result
        exact Nat.le_refl 11
    | add left right =>
        simp only [testAlgebra, RandCostedT.liftCosted] at hresult
        rw [PMF.mem_support_pure_iff] at hresult
        subst result
        exact Nat.le_refl 5
    | sub left right =>
        simp only [testAlgebra, RandCostedT.liftCosted] at hresult
        rw [PMF.mem_support_pure_iff] at hresult
        subst result
        exact Nat.le_refl 6
    | mul left right =>
        simp only [testAlgebra, RandCostedT.liftCosted] at hresult
        rw [PMF.mem_support_pure_iff] at hresult
        subst result
        exact Nat.le_refl 13

noncomputable def testParamEfficiency :
    ParamEfficiencyCertificate testPublicParam where
  bounds := testBounds
  scalarSampleBudget := 2
  scalarSampleBudget_sound := Nat.le_refl 2
  carrierSampleBudget := 4
  carrierSampleBudget_sound := Nat.le_refl 4
  smulBudget := 11
  smulBudget_sound := by intros; exact Nat.le_refl 11
  addBudget := 5
  addBudget_sound := by intros; exact Nat.le_refl 5
  subBudget := 6
  subBudget_sound := by intros; exact Nat.le_refl 6
  mulBudget := 13
  mulBudget_sound := by intros; exact Nat.le_refl 13

noncomputable def testFamily : Family CostModel.nat :=
  Family.ofFixed testPublicParam 3

example : Prop := Assumption testFamily

example (sec : Crypto.SecPar) :
    Program.runCosted (setupProgram testFamily) sec = testFamily.setup sec :=
  setupProgram_runCosted testFamily sec

/-- Both games are defined directly by erasing their authoritative programs. -/
example (sec : Crypto.SecPar) :
    Program.valueDist (realSampleProgram testFamily) sec =
      (ddhProblem testFamily).left sec :=
  rfl

example (sec : Crypto.SecPar) :
    Program.valueDist (randomSampleProgram testFamily) sec =
      (ddhProblem testFamily).right sec :=
  rfl

example :
    Program.Code.valueDist
        (A := testPublicParam.algebra) (.call Op.sampleCarrier) =
      (algebraLaws testPublicParam).semantics Op.sampleCarrier :=
  Program.Code.valueDist_call_eq (algebraLaws testPublicParam) Op.sampleCarrier

/-- Genuine and random fixed-exponent programs retain their exact bounds. -/
example :
    Program.CostBound
      (realChallengeProgram testPublicParam) (fun _ => 46) :=
  (realChallengeBoundedProgram testPublicParam testParamEfficiency).costBound

example :
    Program.CostBound
      (randomChallengeProgram testPublicParam) (fun _ => 22) :=
  (randomChallengeBoundedProgram testPublicParam testParamEfficiency).costBound

/-- Sampling adds two scalar samples, and the random game adds one carrier sample. -/
example :
    Program.CostBound
      (realSampleTailProgram testPublicParam) (fun _ => 50) :=
  (realSampleTailBoundedProgram testPublicParam testParamEfficiency).costBound

example :
    Program.CostBound
      (randomSampleTailProgram testPublicParam) (fun _ => 30) :=
  (randomSampleTailBoundedProgram testPublicParam testParamEfficiency).costBound

end CryptoTest.Assumption.DL.DDH

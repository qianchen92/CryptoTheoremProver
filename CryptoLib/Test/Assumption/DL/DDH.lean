import CryptoLib.Assumption.DL.DDH
import CryptoLib.Core.Infrastructure.Probability.Uniform
import Mathlib.Data.ZMod.Basic

namespace CryptoLib.Test.Assumption.DL.DDH

open scoped DDHParameter
open CryptoLib.Assumption.DL.DDH
open CryptoLib.Core.Infrastructure.Computation
open CryptoLib.Algebra.Generic
open CryptoLib.Core.Infrastructure.Computation.Cost

universe uAdversaryCost

def testMath : MathematicalParam (ZMod 2) (ZMod 2) where
  addGroup := inferInstance
  fintypeCarrier := inferInstance
  fintypeScalar := inferInstance
  smul := inferInstance
  commMonoidScalar := inferInstance
  one_smul := by intro value; exact one_smul (ZMod 2) value
  mul_smul := by intro left right value; exact mul_smul left right value
  generator := 1
  generator_generates := by
    intro value
    exact ⟨value, by simp⟩

noncomputable def testAlgebra :
    CostedAlgebra CostModel.nat (signature testMath) where
  exec operation :=
    match operation with
    | .sampleScalar =>
        RandCosted.sampleWithCost
          (PMF.map ULift.up
            (@CryptoLib.Core.Infrastructure.Probability.uniformPMF
              testMath.Scalar testMath.fintypeScalar
              ⟨testMath.commMonoidScalar.one⟩)) (fun _ => 2)
    | .sampleCarrier =>
        RandCosted.sampleWithCost
          (PMF.map ULift.up
            (@CryptoLib.Core.Infrastructure.Probability.uniformPMF
              testMath.Carrier testMath.fintypeCarrier
              ⟨testMath.addGroup.zero⟩)) (fun _ => 4)
    | .smul scalar value =>
        RandCosted.liftCosted
          ⟨ULift.up (testMath.smul.smul scalar value), 11⟩
    | .add left right =>
        RandCosted.liftCosted
          ⟨ULift.up (testMath.addGroup.add left right), 5⟩
    | .sub left right =>
        RandCosted.liftCosted
          ⟨ULift.up (testMath.addGroup.sub left right), 6⟩
    | .mul left right =>
        RandCosted.liftCosted
          ⟨ULift.up (testMath.commMonoidScalar.mul left right), 13⟩

noncomputable def testLaws : ExactLaws testAlgebra where
  sampleScalar := RandCosted.valueDist_sampleWithCost _ _
  sampleCarrier := RandCosted.valueDist_sampleWithCost _ _
  smul _ _ := RandCosted.valueDist_liftCosted _
  add _ _ := RandCosted.valueDist_liftCosted _
  sub _ _ := RandCosted.valueDist_liftCosted _
  mul _ _ := RandCosted.valueDist_liftCosted _

noncomputable def testPublicParam :
    PublicParam CostModel.nat (ZMod 2) (ZMod 2) where
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
        simp only [testAlgebra, RandCosted.sampleWithCost] at hresult
        rw [PMF.mem_support_map_iff] at hresult
        rcases hresult with ⟨value, _hvalue, hresult⟩
        subst result
        exact Nat.le_refl 2
    | sampleCarrier =>
        simp only [testAlgebra, RandCosted.sampleWithCost] at hresult
        rw [PMF.mem_support_map_iff] at hresult
        rcases hresult with ⟨value, _hvalue, hresult⟩
        subst result
        exact Nat.le_refl 4
    | smul scalar value =>
        simp only [testAlgebra, RandCosted.liftCosted] at hresult
        rw [PMF.mem_support_pure_iff] at hresult
        subst result
        exact Nat.le_refl 11
    | add left right =>
        simp only [testAlgebra, RandCosted.liftCosted] at hresult
        rw [PMF.mem_support_pure_iff] at hresult
        subst result
        exact Nat.le_refl 5
    | sub left right =>
        simp only [testAlgebra, RandCosted.liftCosted] at hresult
        rw [PMF.mem_support_pure_iff] at hresult
        subst result
        exact Nat.le_refl 6
    | mul left right =>
        simp only [testAlgebra, RandCosted.liftCosted] at hresult
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

noncomputable def testFamily :
    Family CostModel.nat CryptoLib.Core.SecPar (ZMod 2) (ZMod 2) :=
  Family.ofFixed testPublicParam 3 5 (by intros; rfl)

example : Prop := Assumption CostModel.nat NatMeasure.nat testFamily

example (adversaryModel : CostModel.{uAdversaryCost})
    (measure : NatMeasure adversaryModel) : Prop :=
  Assumption adversaryModel measure testFamily

example (sec : CryptoLib.Core.SecPar) :
    (ddhProblem testFamily).left sec = realSample testFamily sec := by
  rfl

example (sec : CryptoLib.Core.SecPar) :
    (ddhProblem testFamily).right sec = randomSample testFamily sec := by
  rfl

end CryptoLib.Test.Assumption.DL.DDH

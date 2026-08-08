import CryptoLib.Assumption.DL.DLog
import CryptoLib.Core.Infrastructure.Probability.Uniform
import Mathlib.Data.ZMod.Basic

namespace CryptoLib.Test.Assumption.DL.DLog

open scoped DLogParameter
open CryptoLib.Assumption.DL.DLog
open CryptoLib.Core.Infrastructure.Complexity
open CryptoLib.Core.Infrastructure.Computation
open CryptoLib.Algebra.Generic
open CryptoLib.Core.Infrastructure.Computation.Cost

universe uAdversaryCost

def testMath : MathematicalParam (ZMod 2) (ZMod 2) where
  addGroup := inferInstance
  fintypeCarrier := inferInstance
  fintypeScalar := inferInstance
  smul := inferInstance
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
              (@CryptoLib.Assumption.DL.Parameter.scalarNonemptyOfGenerator
                testMath.Scalar testMath.Carrier testMath.addGroup testMath.smul
                testMath.generator testMath.generator_generates))) (fun _ => 2)
    | .smul scalar value =>
        RandCosted.liftCosted
          ⟨ULift.up (testMath.smul.smul scalar value), 11⟩

noncomputable def testLaws : ExactLaws testAlgebra where
  sampleScalar := RandCosted.valueDist_sampleWithCost _ _
  smul _ _ := RandCosted.valueDist_liftCosted _

noncomputable def testPublicParam :
    PublicParam CostModel.nat (ZMod 2) (ZMod 2) where
  toCyclicAction := testMath
  algebra := testAlgebra
  laws := testLaws

noncomputable def testFamily : Family CostModel.nat (ZMod 2) (ZMod 2) :=
  Family.ofFixed testPublicParam 3

example : Prop := Assumption CostModel.nat NatMeasure.nat testFamily

example (adversaryModel : CostModel.{uAdversaryCost})
    (measure : NatMeasure adversaryModel) : Prop :=
  Assumption adversaryModel measure testFamily

noncomputable def chosenLog
    (challenge : ChallengeInput CostModel.nat (ZMod 2) (ZMod 2)) :
    Witness challenge :=
  Classical.choose (challenge.1.generator_generates challenge.2)

theorem chosenLog_isSolution
    (challenge : ChallengeInput CostModel.nat (ZMod 2) (ZMod 2)) :
    IsSolution challenge (chosenLog challenge) :=
  Classical.choose_spec (challenge.1.generator_generates challenge.2)

noncomputable def chosenLogTimedMachine :
    TimedMachine CostModel.nat NatMeasure.nat
      (fun _sec => ChallengeInput CostModel.nat (ZMod 2) (ZMod 2))
      (fun _sec challenge => Witness challenge) :=
  TimedMachine.ofFunction CostModel.nat NatMeasure.nat
    (fun _sec challenge => chosenLog challenge)

example : chosenLogTimedMachine.runtime = fun _sec => 0 := rfl

end CryptoLib.Test.Assumption.DL.DLog

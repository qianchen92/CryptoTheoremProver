import Crypto.Assumption.DL.DDH
import Mathlib.Data.ZMod.Basic

namespace CryptoTest.Assumption.DL.DDH

open scoped DDHParameter

open Crypto.Assumption.DL.DDH
open Crypto.Infrastructure.Computation
open Crypto.Infrastructure.Computation.Algebra
open Crypto.Infrastructure.Computation.Cost

/-- A concrete two-element DDH parameter whose operations carry their own costs. -/
noncomputable def testPublicParam : PublicParam where
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
  backend := AdditiveBackend.ofConstantCosts 5 7 6 11
  scalarMulBackend := MultiplicativeBackend.ofConstantCost 13
  scalarSampler := UniformSampler.ofConstantCost 2
  scalarSamplerLaws := UniformSamplerLaws.ofConstantCost 2
  carrierSampler := UniformSampler.ofConstantCost 4
  carrierSamplerLaws := UniformSamplerLaws.ofConstantCost 4

/-- Local sampler and operation bounds certified once for the concrete parameter. -/
noncomputable def testParamEfficiency :
    ParamEfficiencyCertificate testPublicParam where
  scalarSamplerBounds := UniformSamplerBounds.ofConstantCost 2
  carrierSamplerBounds := UniformSamplerBounds.ofConstantCost 4
  additiveBounds := AdditiveCostBounds.ofConstantCosts 5 7 6 11
  scalarMulBounds := MultiplicativeCostBounds.ofConstantCost 13

/-- A native costed DDH family with one fixed public parameter. -/
noncomputable def testFamily : Family :=
  Family.ofFixed testPublicParam 3

/-- The exact compositional efficiency certificate for `testFamily`. -/
noncomputable def testEfficiency : EfficiencyCertificate testFamily :=
  EfficiencyCertificate.ofFixed testPublicParam testParamEfficiency 3

/-- The DDH assumption itself depends only on the exact costed family. -/
example : Prop :=
  Assumption testFamily

/-- A real DDH sample distribution is the erasure of its costed computation. -/
example (sec : Crypto.SecPar) :
    RandCosted.valueDist (realSampleComputation testFamily sec) =
      realSample testFamily sec :=
  realSampleComputation_valueDist testFamily sec

/-- A random DDH sample distribution is the erasure of its costed computation. -/
example (sec : Crypto.SecPar) :
    RandCosted.valueDist (randomSampleComputation testFamily sec) =
      randomSample testFamily sec :=
  randomSampleComputation_valueDist testFamily sec

/-- Setup is dispatched by the family-level typed program without alteration. -/
example (sec : Crypto.SecPar) :
    Program.runCosted (setupProgram testFamily) sec = testFamily.setup sec :=
  setupProgram_runCosted testFamily sec

/-- The full genuine path is exactly setup followed by the typed local tail. -/
example (sec : Crypto.SecPar) :
    Program.runCosted (realSampleProgram testFamily) sec =
      RandCosted.bind (testFamily.setup sec) realSampleTailComputation :=
  realSampleProgram_runCosted_eq_bind_tail testFamily sec

/-- The full random path is exactly setup followed by the typed local tail. -/
example (sec : Crypto.SecPar) :
    Program.runCosted (randomSampleProgram testFamily) sec =
      RandCosted.bind (testFamily.setup sec) randomSampleTailComputation :=
  randomSampleProgram_runCosted_eq_bind_tail testFamily sec

/-- Erasing the full typed genuine path gives the unchanged DDH real game. -/
example (sec : Crypto.SecPar) :
    Program.valueDist (realSampleProgram testFamily) sec =
      realSample testFamily sec :=
  rfl

/-- Erasing the full typed random path gives the unchanged DDH random game. -/
example (sec : Crypto.SecPar) :
    Program.valueDist (randomSampleProgram testFamily) sec =
      randomSample testFamily sec :=
  rfl

/-- Family-level setup erasure is specified independently of execution. -/
example (sec : Crypto.SecPar) :
    Program.Code.valueDist
        (A := familyAlgebra testFamily)
        (.call (FamilyOp.setup sec)) =
      (familyAlgebraLaws testFamily).semantics (FamilyOp.setup sec) :=
  Program.Code.valueDist_call_eq (familyAlgebraLaws testFamily)
    (FamilyOp.setup sec)

/-- A dependent carrier sample uses the delegated family erasure law. -/
example :
    Program.Code.valueDist
        (A := familyAlgebra testFamily)
        (.call (FamilyOp.sampleCarrier testPublicParam)) =
      (familyAlgebraLaws testFamily).semantics
        (FamilyOp.sampleCarrier testPublicParam) :=
  Program.Code.valueDist_call_eq (familyAlgebraLaws testFamily)
    (FamilyOp.sampleCarrier testPublicParam)

/-- The authoritative typed real path is the exact 46-unit compatibility path. -/
example (leftExp rightExp : testPublicParam.Scalar) :
    (RandCosted.map
        (fun values => ChallengeValues.toChallengeInput values.down)
        (Program.runCosted (realChallengeProgram testPublicParam)
          (leftExp, rightExp)) =
      RandCosted.liftCosted
        (realChallengeComputation testPublicParam leftExp rightExp)) ∧
      (realChallengeComputation testPublicParam leftExp rightExp).cost = 46 :=
  ⟨realChallengeProgram_runCosted testPublicParam leftExp rightExp, rfl⟩

/-- The authoritative typed random path is the exact 22-unit compatibility path. -/
example (leftExp rightExp : testPublicParam.Scalar)
    (sampledShared : testPublicParam.Carrier) :
    (RandCosted.map
        (fun values => ChallengeValues.toChallengeInput values.down)
        (Program.runCosted (randomChallengeProgram testPublicParam)
          (leftExp, rightExp, sampledShared)) =
      RandCosted.liftCosted
        (randomChallengeComputation testPublicParam leftExp rightExp
          sampledShared)) ∧
      (randomChallengeComputation testPublicParam leftExp rightExp
        sampledShared).cost = 22 :=
  ⟨randomChallengeProgram_runCosted testPublicParam leftExp rightExp
      sampledShared, rfl⟩

/-- Typed genuine and random tails retain their exact structural budgets. -/
example :
    Program.CostBound
      (realSampleTailProgram testPublicParam) (fun _input => 50) :=
  (realSampleTailBoundedProgram
    testPublicParam testParamEfficiency).costBound

example :
    Program.CostBound
      (randomSampleTailProgram testPublicParam) (fun _input => 30) :=
  (randomSampleTailBoundedProgram
    testPublicParam testParamEfficiency).costBound

/-- Dependent scalar-operation dispatch uses the separate erasure laws. -/
example :
    Program.Code.valueDist
        (A := algebra testPublicParam) (.call Op.sampleScalar) =
      (algebraLaws testPublicParam).semantics Op.sampleScalar :=
  Program.Code.valueDist_call_eq (algebraLaws testPublicParam) Op.sampleScalar

/-- Full real and random sampling paths satisfy their global budgets. -/
example :
    Crypto.Infrastructure.Computation.RandomizedComputation.CostBound
      (fun sec (_input : Unit) => testFamily.setup sec)
      (fun _sec => 3) :=
  setup_costBound testFamily testEfficiency

example :
    Program.CostBound (setupProgram testFamily) (fun _sec => 3) :=
  setupProgram_costBound testFamily testEfficiency

example :
    Crypto.Infrastructure.Computation.RandomizedComputation.CostBound
      (fun sec (_input : Unit) => realSampleComputation testFamily sec)
      (fun _sec => 53) :=
  realSampleComputation_costBound testFamily testEfficiency

example :
    Program.CostBound (realSampleProgram testFamily) (fun _sec => 53) :=
  realSampleProgram_costBound testFamily testEfficiency

example :
    Crypto.Infrastructure.Computation.RandomizedComputation.CostBound
      (fun sec (_input : Unit) => randomSampleComputation testFamily sec)
      (fun _sec => 33) :=
  randomSampleComputation_costBound testFamily testEfficiency

example :
    Program.CostBound (randomSampleProgram testFamily) (fun _sec => 33) :=
  randomSampleProgram_costBound testFamily testEfficiency

end CryptoTest.Assumption.DL.DDH

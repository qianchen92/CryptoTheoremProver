import Crypto.Assumption.DL.DLog
import Mathlib.Data.ZMod.Basic

namespace CryptoTest.Assumption.DL.DLog

open scoped DLogParameter

open Crypto.Assumption.DL.DLog
open Crypto.Infrastructure.Computation
open Crypto.Infrastructure.Computation.Algebra
open Crypto.Infrastructure.Computation.Cost

/-- A concrete two-element DLog parameter whose operations carry their own costs. -/
noncomputable def testPublicParam : PublicParam where
  Scalar := ZMod 2
  Carrier := ZMod 2
  addGroup := inferInstance
  fintypeCarrier := inferInstance
  nonemptyCarrier := inferInstance
  fintypeScalar := inferInstance
  smul := inferInstance
  generator := 1
  generator_generates := by
    intro value
    exact ⟨value, by simp⟩
  backend := AdditiveBackend.ofConstantCosts 5 7 6 11
  scalarSampler := UniformSampler.ofConstantCost 2
  scalarSamplerLaws := UniformSamplerLaws.ofConstantCost 2

/-- Local sampler and operation bounds certified once for the concrete parameter. -/
noncomputable def testParamEfficiency :
    ParamEfficiencyCertificate testPublicParam where
  scalarSamplerBounds := UniformSamplerBounds.ofConstantCost 2
  additiveBounds := AdditiveCostBounds.ofConstantCosts 5 7 6 11

/-- A native costed DLog family with one fixed public parameter. -/
noncomputable def testFamily : Family :=
  Family.ofFixed testPublicParam 3

/-- The exact compositional efficiency certificate for `testFamily`. -/
noncomputable def testEfficiency : EfficiencyCertificate testFamily :=
  EfficiencyCertificate.ofFixed testPublicParam testParamEfficiency 3

/-- The DLog assumption itself depends only on the exact costed family. -/
example : Prop :=
  Assumption testFamily

/-- Cost erasure is definitionally the DLog search-problem sampler. -/
example (sec : Crypto.SecPar) :
    RandCosted.valueDist (sampleComputation testFamily sec) =
      (dLogProblem testFamily).sample sec :=
  sampleComputation_valueDist testFamily sec

/-- Setup is dispatched by the family-level typed program without alteration. -/
example (sec : Crypto.SecPar) :
    Program.runCosted (setupProgram testFamily) sec = testFamily.setup sec :=
  setupProgram_runCosted testFamily sec

/-- The full setup-dependent program preserves the exact legacy bind path. -/
example (sec : Crypto.SecPar) :
    Program.runCosted (sampleProgram testFamily) sec =
      RandCosted.bind (testFamily.setup sec) sampleTailComputation :=
  sampleProgram_runCosted_eq_bind_tail testFamily sec

/-- Erasing the full typed program gives the unchanged DLog sampler. -/
example (sec : Crypto.SecPar) :
    Program.valueDist (sampleProgram testFamily) sec =
      (dLogProblem testFamily).sample sec :=
  rfl

/-- Family-level setup erasure is specified independently of execution. -/
example (sec : Crypto.SecPar) :
    Program.Code.valueDist
        (A := familyAlgebra testFamily)
        (.call (FamilyOp.setup sec)) =
      (familyAlgebraLaws testFamily).semantics (FamilyOp.setup sec) :=
  Program.Code.valueDist_call_eq (familyAlgebraLaws testFamily)
    (FamilyOp.setup sec)

/-- Delegated dependent sampling also satisfies the family-level erasure law. -/
example :
    Program.Code.valueDist
        (A := familyAlgebra testFamily)
        (.call (FamilyOp.sampleScalar testPublicParam)) =
      (familyAlgebraLaws testFamily).semantics
        (FamilyOp.sampleScalar testPublicParam) :=
  Program.Code.valueDist_call_eq (familyAlgebraLaws testFamily)
    (FamilyOp.sampleScalar testPublicParam)

/-- The authoritative typed path is the exact 11-unit compatibility computation. -/
example (secret : testPublicParam.Scalar) :
    (RandCosted.map (fun challenge => ⟨testPublicParam, challenge.down⟩)
        (Program.runCosted (challengeProgram testPublicParam) secret) =
      RandCosted.liftCosted
        (challengeComputation testPublicParam secret)) ∧
      (challengeComputation testPublicParam secret).cost = 11 :=
  ⟨challengeProgram_runCosted_eq_challengeComputation
      testPublicParam secret, rfl⟩

/-- The typed DLog tail itself carries the exact structural 13-unit bound. -/
example :
    Program.CostBound (sampleTailProgram testPublicParam) (fun _input => 13) :=
  (sampleTailBoundedProgram testPublicParam testParamEfficiency).costBound

/-- Dispatching the dependent scalar sampler obeys its separate erasure law. -/
example :
    Program.Code.valueDist
        (A := algebra testPublicParam) (.call Op.sampleScalar) =
      (algebraLaws testPublicParam).semantics Op.sampleScalar :=
  Program.Code.valueDist_call_eq (algebraLaws testPublicParam) Op.sampleScalar

/-- Setup and complete sampling satisfy their separate global bounds. -/
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
      (fun sec (_input : Unit) => sampleComputation testFamily sec)
      (fun _sec => 16) :=
  sampleComputation_costBound testFamily testEfficiency

example :
    Program.CostBound (sampleProgram testFamily) (fun _sec => 16) :=
  sampleProgram_costBound testFamily testEfficiency

end CryptoTest.Assumption.DL.DLog

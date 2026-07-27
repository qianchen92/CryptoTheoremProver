import Crypto.Assumption.DL.DLog
import Mathlib.Data.ZMod.Basic

namespace CryptoTest.Assumption.DL.DLog

open Crypto.Assumption.DL.DLog
open Crypto.Infrastructure.Computation.Algebra
open Crypto.Infrastructure.Computation.Cost

/-- A concrete two-element DLog parameter whose operations carry their own costs. -/
noncomputable def testPublicParam : PublicParam where
  Scalar := ZMod 2
  Carrier := ZMod 2
  addGroup := inferInstance
  fintypeCarrier := inferInstance
  fintypeScalar := inferInstance
  smul := inferInstance
  generator := 1
  generator_generates := by
    intro value
    exact ⟨value, by simp⟩
  backend := AdditiveBackend.ofConstantCosts 5 7 6 11
  scalarSampler := UniformSampler.ofConstantCost 2

/-- Local operation bounds certified once for the concrete parameter. -/
noncomputable def testParamEfficiency :
    ParamEfficiencyCertificate testPublicParam where
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

/-- The generated group element inherits the parameter backend's scalar-action cost. -/
example (secret : testPublicParam.Scalar) :
    (challengeComputation testPublicParam secret).cost = 11 :=
  rfl

/-- Setup and complete sampling satisfy their separate global bounds. -/
example :
    Crypto.Infrastructure.Computation.RandomizedComputation.CostBound
      (fun sec (_input : Unit) => testFamily.setup sec)
      (fun _sec => 3) :=
  setup_costBound testFamily testEfficiency

example :
    Crypto.Infrastructure.Computation.RandomizedComputation.CostBound
      (fun sec (_input : Unit) => sampleComputation testFamily sec)
      (fun _sec => 16) :=
  sampleComputation_costBound testFamily testEfficiency

end CryptoTest.Assumption.DL.DLog

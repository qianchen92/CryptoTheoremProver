import Crypto.Assumption.DL.DDH
import Mathlib.Data.ZMod.Basic

namespace CryptoTest.Assumption.DL.DDH

open Crypto.Assumption.DL.DDH
open Crypto.Infrastructure.Computation.Algebra
open Crypto.Infrastructure.Computation.Cost

/-- A concrete two-element DDH parameter whose operations carry their own costs. -/
noncomputable def testPublicParam : PublicParam where
  Scalar := ZMod 2
  Carrier := ZMod 2
  addGroup := inferInstance
  fintypeCarrier := inferInstance
  fintypeScalar := inferInstance
  commMonoidScalar := inferInstance
  mulAction := inferInstance
  generator := 1
  generator_generates := by
    intro value
    exact ⟨value, by simp⟩
  backend := AdditiveBackend.ofConstantCosts 5 7 6 11
  scalarMulBackend := MultiplicativeBackend.ofConstantCost 13
  scalarSampler := UniformSampler.ofConstantCost 2
  carrierSampler := UniformSampler.ofConstantCost 4

/-- Local operation bounds certified once for the concrete parameter. -/
noncomputable def testParamEfficiency :
    ParamEfficiencyCertificate testPublicParam where
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

/-- The scalar product is included in the exact 46-unit real-tuple cost. -/
example (leftExp rightExp : testPublicParam.Scalar) :
    (realChallengeComputation testPublicParam leftExp rightExp).cost = 46 :=
  rfl

/-- Full real and random sampling paths satisfy their global budgets. -/
example :
    Crypto.Infrastructure.Computation.RandomizedComputation.CostBound
      (fun sec (_input : Unit) => testFamily.setup sec)
      (fun _sec => 3) :=
  setup_costBound testFamily testEfficiency

example :
    Crypto.Infrastructure.Computation.RandomizedComputation.CostBound
      (fun sec (_input : Unit) => realSampleComputation testFamily sec)
      (fun _sec => 53) :=
  realSampleComputation_costBound testFamily testEfficiency

example :
    Crypto.Infrastructure.Computation.RandomizedComputation.CostBound
      (fun sec (_input : Unit) => randomSampleComputation testFamily sec)
      (fun _sec => 33) :=
  randomSampleComputation_costBound testFamily testEfficiency

end CryptoTest.Assumption.DL.DDH

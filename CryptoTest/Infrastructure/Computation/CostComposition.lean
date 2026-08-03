import Crypto.Infrastructure.Computation.Algebra.Operation
import Crypto.Infrastructure.Computation.Cost.Distribution
import Crypto.Infrastructure.Computation.Program

namespace CryptoTest.Infrastructure.Computation.CostComposition

open Crypto.Infrastructure.Computation
open Crypto.Infrastructure.Computation.Cost

/-- A shared writer result is charged once before its value is reused. -/
def sharedAddition : CostedT CostModel.nat Nat := do
  let value ← (⟨4, 2⟩ : CostedT CostModel.nat Nat)
  (⟨value + value, 3⟩ : CostedT CostModel.nat Nat)

@[simp] theorem sharedAddition_value : sharedAddition.val = 8 :=
  rfl

@[simp] theorem sharedAddition_cost : sharedAddition.cost = 5 :=
  rfl

/-- Addition is interpreted directly by a typed exact algebra. -/
noncomputable def integerAddAlgebra :
    Crypto.Infrastructure.Computation.Algebra.CostedAlgebra
      CostModel.nat
      (Crypto.Infrastructure.Computation.Algebra.AddOperation.signature Int) :=
  Crypto.Infrastructure.Computation.Algebra.AddOperation.algebra
    CostModel.nat (fun _left _right => 1)

/-- Scalar multiplication has an independent, operand-dependent exact algebra. -/
noncomputable def integerSMulAlgebra :
    Crypto.Infrastructure.Computation.Algebra.CostedAlgebra
      CostModel.nat
      (Crypto.Infrastructure.Computation.Algebra.SMulOperation.signature Nat Int) :=
  Crypto.Infrastructure.Computation.Algebra.SMulOperation.algebra
    CostModel.nat (fun scalar _value => scalar)

@[simp] theorem directIntegerAlgebra_costs :
    Crypto.Infrastructure.Computation.Program.Code.runCosted
        (A := integerAddAlgebra) (.call (.add 2 3)) =
          RandCostedT.liftCosted
            (⟨5, 1⟩ : CostedT CostModel.nat Int) ∧
      Crypto.Infrastructure.Computation.Program.Code.runCosted
        (A := integerSMulAlgebra) (.call (.smul 7 5)) =
          RandCostedT.liftCosted
            (⟨35, 7⟩ : CostedT CostModel.nat Int) :=
  ⟨rfl, rfl⟩

/-- `do` notation for `RandCostedT` selects the writer bind and adds both path costs. -/
noncomputable def twoStageRandomized : RandCostedT CostModel.nat Nat := do
  let first ← RandCostedT.liftCosted
    (⟨5, 2⟩ : CostedT CostModel.nat Nat)
  let second ← RandCostedT.liftCosted
    (⟨7, 3⟩ : CostedT CostModel.nat Nat)
  pure (first + second)

theorem twoStageRandomized_eq :
    twoStageRandomized =
      PMF.pure (⟨12, 5⟩ : CostedT CostModel.nat Nat) := by
  change
    RandCostedT.bind
      (RandCostedT.liftCosted
        (⟨5, 2⟩ : CostedT CostModel.nat Nat))
      (fun first =>
        RandCostedT.bind
          (RandCostedT.liftCosted
            (⟨7, 3⟩ : CostedT CostModel.nat Nat))
          (fun second => RandCostedT.pure CostModel.nat (first + second))) =
      PMF.pure (⟨12, 5⟩ : CostedT CostModel.nat Nat)
  simp only [RandCostedT.bind, RandCostedT.liftCosted,
    RandCostedT.pure, PMF.pure_bind]
  rw [PMF.pure_map, PMF.pure_map]
  rfl

@[simp] theorem twoStageRandomized_valueDist :
    RandCostedT.valueDist twoStageRandomized = PMF.pure 12 := by
  rw [twoStageRandomized_eq]
  exact PMF.pure_map
    (f := fun result : CostedT CostModel.nat Nat => result.val)
    (⟨12, 5⟩ : CostedT CostModel.nat Nat)

/-- Explicit sampling cost is retained on the sampled path. -/
noncomputable def explicitlyCostedSample : RandCostedT CostModel.nat Nat :=
  RandCostedT.sampleWithCost (PMF.pure 7) (fun value => value + 1)

theorem explicitlyCostedSample_eq :
    explicitlyCostedSample =
      PMF.pure (⟨7, 8⟩ : CostedT CostModel.nat Nat) := by
  exact PMF.pure_map
    (f := fun value : Nat =>
      (⟨value, value + 1⟩ : CostedT CostModel.nat Nat)) 7

@[simp] theorem explicitlyCostedSample_valueDist :
    RandCostedT.valueDist explicitlyCostedSample = PMF.pure 7 := by
  simp [explicitlyCostedSample]

end CryptoTest.Infrastructure.Computation.CostComposition

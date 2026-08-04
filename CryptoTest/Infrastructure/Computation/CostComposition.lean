import Crypto.Infrastructure.Computation.Algebra.Operation
import Crypto.Infrastructure.Computation.Cost.Randomized
import Crypto.Infrastructure.Computation.Program.Basic

namespace CryptoTest.Infrastructure.Computation.CostComposition

open Crypto.Infrastructure.Computation
open Crypto.Infrastructure.Computation.Cost

/-- A shared writer result is charged once before its value is reused. -/
def sharedAddition : Costed CostModel.nat Nat := do
  let value ← (⟨4, 2⟩ : Costed CostModel.nat Nat)
  (⟨value + value, 3⟩ : Costed CostModel.nat Nat)

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
          RandCosted.liftCosted
            (⟨5, 1⟩ : Costed CostModel.nat Int) ∧
      Crypto.Infrastructure.Computation.Program.Code.runCosted
        (A := integerSMulAlgebra) (.call (.smul 7 5)) =
          RandCosted.liftCosted
            (⟨35, 7⟩ : Costed CostModel.nat Int) :=
  ⟨rfl, rfl⟩

/-- `do` notation for `RandCosted` selects the writer bind and adds both path costs. -/
noncomputable def twoStageRandomized : RandCosted CostModel.nat Nat := do
  let first ← RandCosted.liftCosted
    (⟨5, 2⟩ : Costed CostModel.nat Nat)
  let second ← RandCosted.liftCosted
    (⟨7, 3⟩ : Costed CostModel.nat Nat)
  pure (first + second)

theorem twoStageRandomized_eq :
    twoStageRandomized =
      PMF.pure (⟨12, 5⟩ : Costed CostModel.nat Nat) := by
  change
    RandCosted.bind
      (RandCosted.liftCosted
        (⟨5, 2⟩ : Costed CostModel.nat Nat))
      (fun first =>
        RandCosted.bind
          (RandCosted.liftCosted
            (⟨7, 3⟩ : Costed CostModel.nat Nat))
          (fun second => RandCosted.pure CostModel.nat (first + second))) =
      PMF.pure (⟨12, 5⟩ : Costed CostModel.nat Nat)
  simp only [RandCosted.bind, RandCosted.liftCosted,
    RandCosted.pure, PMF.pure_bind]
  rw [PMF.pure_map, PMF.pure_map]
  rfl

@[simp] theorem twoStageRandomized_valueDist :
    RandCosted.valueDist twoStageRandomized = PMF.pure 12 := by
  rw [twoStageRandomized_eq]
  exact PMF.pure_map
    (f := fun result : Costed CostModel.nat Nat => result.val)
    (⟨12, 5⟩ : Costed CostModel.nat Nat)

/-- Explicit sampling cost is retained on the sampled path. -/
noncomputable def explicitlyCostedSample : RandCosted CostModel.nat Nat :=
  RandCosted.sampleWithCost (PMF.pure 7) (fun value => value + 1)

theorem explicitlyCostedSample_eq :
    explicitlyCostedSample =
      PMF.pure (⟨7, 8⟩ : Costed CostModel.nat Nat) := by
  exact PMF.pure_map
    (f := fun value : Nat =>
      (⟨value, value + 1⟩ : Costed CostModel.nat Nat)) 7

@[simp] theorem explicitlyCostedSample_valueDist :
    RandCosted.valueDist explicitlyCostedSample = PMF.pure 7 := by
  simp [explicitlyCostedSample]

end CryptoTest.Infrastructure.Computation.CostComposition

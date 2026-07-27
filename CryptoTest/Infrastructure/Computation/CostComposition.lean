import Crypto.Infrastructure.Computation.Algebra.Basic
import Crypto.Infrastructure.Computation.Cost.Distribution

namespace CryptoTest.Infrastructure.Computation.CostComposition

open Crypto.Infrastructure.Computation
open Crypto.Infrastructure.Computation.Cost

/-- A shared writer result is charged once before its value is reused. -/
def sharedAddition : Costed Nat :=
  letI : AddCost Nat := ⟨fun _ _ => 3⟩
  do
    let value ← (⟨4, 2⟩ : Costed Nat)
    Crypto.Infrastructure.Computation.Algebra.Costed.add value value

@[simp] theorem sharedAddition_value : sharedAddition.val = 8 :=
  rfl

@[simp] theorem sharedAddition_cost : sharedAddition.cost = 5 :=
  rfl

/--
Default group costs are selected explicitly before bridging the typeclass
compatibility layer into the authoritative backend interface.
-/
def explicitIntegerBackend :
    Crypto.Infrastructure.Computation.Algebra.AdditiveBackend Nat Int := by
  let model :=
    Crypto.Infrastructure.Computation.Algebra.Group.unitLinearCostModel Int
  letI := model.add
  letI := model.sub
  letI := model.neg
  letI := model.natSMul
  exact Crypto.Infrastructure.Computation.Algebra.AdditiveBackend.ofCostModel

@[simp] theorem explicitIntegerBackend_costs :
    (explicitIntegerBackend.add 2 3).cost = 1 ∧
      (explicitIntegerBackend.smul 7 5).cost = 7 :=
  ⟨rfl, rfl⟩

/-- `do` notation for `RandCosted` selects the writer bind and adds both path costs. -/
noncomputable def twoStageRandomized : RandCosted Nat := do
  let first ← RandCosted.liftCosted (⟨5, 2⟩ : Costed Nat)
  let second ← RandCosted.liftCosted (⟨7, 3⟩ : Costed Nat)
  pure (first + second)

theorem twoStageRandomized_eq :
    twoStageRandomized = PMF.pure (⟨12, 5⟩ : Costed Nat) := by
  change
    RandCosted.bind (RandCosted.liftCosted (⟨5, 2⟩ : Costed Nat))
      (fun first =>
        RandCosted.bind (RandCosted.liftCosted (⟨7, 3⟩ : Costed Nat))
          (fun second => RandCosted.pure (first + second))) =
      PMF.pure (⟨12, 5⟩ : Costed Nat)
  simp only [RandCosted.bind, RandCosted.liftCosted, RandCosted.pure, PMF.pure_bind]
  rw [PMF.pure_map, PMF.pure_map]
  rfl

@[simp] theorem twoStageRandomized_valueDist :
    RandCosted.valueDist twoStageRandomized = PMF.pure 12 := by
  rw [twoStageRandomized_eq]
  exact PMF.pure_map (f := Costed.val) (⟨12, 5⟩ : Costed Nat)

/-- Explicit sampling cost is retained on the sampled path. -/
noncomputable def explicitlyCostedSample : RandCosted Nat :=
  RandCosted.sampleWithCost (PMF.pure 7) (fun value => value + 1)

theorem explicitlyCostedSample_eq :
    explicitlyCostedSample = PMF.pure (⟨7, 8⟩ : Costed Nat) := by
  exact PMF.pure_map (f := fun value : Nat => (⟨value, value + 1⟩ : Costed Nat)) 7

@[simp] theorem explicitlyCostedSample_valueDist :
    RandCosted.valueDist explicitlyCostedSample = PMF.pure 7 := by
  simp [explicitlyCostedSample]

end CryptoTest.Infrastructure.Computation.CostComposition

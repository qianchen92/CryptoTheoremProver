import Crypto.Infrastructure.Complexity.ProgramMachine
import Crypto.Infrastructure.Computation.Randomized
import Mathlib.Probability.Distributions.Uniform
import Mathlib.Tactic

namespace CryptoTest.Infrastructure.Computation.GenericCost

open Crypto.Infrastructure.Computation.Cost
open Crypto.Infrastructure.Computation
open Crypto.Infrastructure.Computation.Algebra
open Crypto.Infrastructure.Complexity

/-- A small resource vector tracking execution steps and oracle queries separately. -/
abbrev StepsQueries := Nat × Nat

/-- Componentwise exact-resource model used to check that costs are not forced to `Nat`. -/
abbrev stepsQueriesCostModel : CostModel where
  Cost := StepsQueries
  instAddMonoid := inferInstance
  instPartialOrder := inferInstance
  instAddLeftMono :=
    ⟨fun fixed _left _right hle =>
      ⟨Nat.add_le_add_left hle.1 fixed.1,
        Nat.add_le_add_left hle.2 fixed.2⟩⟩
  instAddRightMono :=
    ⟨fun fixed _left _right hle =>
      ⟨Nat.add_le_add_right hle.1 fixed.1,
        Nat.add_le_add_right hle.2 fixed.2⟩⟩

/-- Sequential identity is inherited from the model's chosen additive monoid. -/
example (resources : StepsQueries) :
    stepsQueriesCostModel.instAddMonoid.add
        stepsQueriesCostModel.instAddMonoid.zero resources = resources := by
  change (0, 0) + resources = resources
  simp

/-- The right sequential identity is checked independently of the left one. -/
example (resources : StepsQueries) :
    stepsQueriesCostModel.instAddMonoid.add resources
        stepsQueriesCostModel.instAddMonoid.zero = resources := by
  change resources + (0, 0) = resources
  simp

/-- Sequential composition remains associative without assuming commutativity. -/
example (first second third : StepsQueries) :
    stepsQueriesCostModel.instAddMonoid.add
        (stepsQueriesCostModel.instAddMonoid.add first second) third =
      stepsQueriesCostModel.instAddMonoid.add first
        (stepsQueriesCostModel.instAddMonoid.add second third) := by
  change (first + second) + third = first + (second + third)
  exact add_assoc first second third

/-- Both sides of sequential composition are monotone in the configured order. -/
example (fixed left right : StepsQueries)
    (hle : stepsQueriesCostModel.instPartialOrder.le left right) :
    stepsQueriesCostModel.instPartialOrder.le
        (stepsQueriesCostModel.instAddMonoid.add fixed left)
        (stepsQueriesCostModel.instAddMonoid.add fixed right) := by
  letI := stepsQueriesCostModel.instAddMonoid
  letI := stepsQueriesCostModel.instPartialOrder
  letI := stepsQueriesCostModel.instAddLeftMono
  exact add_le_add_right hle fixed

/-- Monotonicity also holds when the varying resource is on the left. -/
example (fixed left right : StepsQueries)
    (hle : stepsQueriesCostModel.instPartialOrder.le left right) :
    stepsQueriesCostModel.instPartialOrder.le
        (stepsQueriesCostModel.instAddMonoid.add left fixed)
        (stepsQueriesCostModel.instAddMonoid.add right fixed) := by
  letI := stepsQueriesCostModel.instAddMonoid
  letI := stepsQueriesCostModel.instPartialOrder
  letI := stepsQueriesCostModel.instAddRightMono
  exact add_le_add_left hle fixed

/-- A worst-case capability supplies the automatic branch join independently. -/
example (left right : Nat) :
    @LE.le Nat WorstCaseCostModel.nat.toCostModel.instPartialOrder.toLE left
      (WorstCaseCostModel.nat.instSemilatticeSup.sup left right) := by
  rw [← WorstCaseCostModel.nat.partialOrder_eq]
  exact
    @le_sup_left Nat WorstCaseCostModel.nat.instSemilatticeSup left right

def firstStage : CostedT stepsQueriesCostModel Nat :=
  ⟨4, (2, 1)⟩

def twoStage : CostedT stepsQueriesCostModel Nat :=
  firstStage.bind fun value => ⟨value + 3, (5, 2)⟩

example : twoStage.val = 7 := rfl

example : twoStage.cost = (7, 3) := rfl

/-- Observe total work only at the legacy machine boundary. -/
def totalWork : NatMeasure stepsQueriesCostModel where
  toNat :=
    { toFun := fun resources => resources.1 + resources.2
      map_zero' := rfl
      map_add' := by
        intro left right
        simp only [Prod.fst_add, Prod.snd_add]
        omega }
  monotone_toNat := by
    intro left right hle
    exact Nat.add_le_add hle.1 hle.2

/-- One generic-cost primitive used to exercise the legacy-machine adapter. -/
inductive VectorOperation : Type → Type 1 where
  | tick (value : Nat) : VectorOperation Nat

def vectorSignature : Signature where
  Op := VectorOperation

noncomputable def vectorAlgebra :
    CostedAlgebra stepsQueriesCostModel vectorSignature where
  exec operation :=
    match operation with
    | .tick value => PMF.pure ⟨value + 1, (2, 1)⟩

noncomputable def vectorBounds : OperationBounds vectorAlgebra where
  budget _operation := (2, 1)
  cost_le operation result hresult := by
    cases operation
    simp only [vectorAlgebra] at hresult
    rw [PMF.mem_support_pure_iff] at hresult
    subst result
    exact le_refl _

noncomputable def vectorProgram : Program vectorAlgebra Nat Nat where
  body input := .call (.tick input)

noncomputable def vectorBoundedProgram :
    Program.BoundedProgram (Input := Nat) (Output := Nat)
      vectorBounds (fun _input : Nat => (2, 1)) where
  program := vectorProgram
  certificate input :=
    Program.Code.Bound.call (bounds := vectorBounds) (.tick input)

/-- The genuinely vector-valued program is projected only at the machine boundary. -/
noncomputable def vectorTimedMachine : TimedMachine Nat Nat :=
  TimedMachine.ofBoundedProgram
    totalWork
    (fun _sec => vectorAlgebra)
    (fun _sec => vectorBounds)
    (fun _sec _input => (2, 1))
    (fun _sec => 3)
    (fun _sec => vectorBoundedProgram)
    (by
      intro sec input
      exact Nat.le_refl 3)

example (sec : Crypto.SecPar) (input : Nat) :
    RandCosted.valueDist (vectorTimedMachine.run sec input) =
      Program.valueDist vectorProgram input := by
  unfold vectorTimedMachine
  rw [TimedMachine.valueDist_run_ofBoundedProgram]
  rfl

example : CostedT.mapCost totalWork twoStage = (⟨7, 10⟩ : Costed Nat) := rfl

noncomputable def sampled : RandCostedT stepsQueriesCostModel Nat :=
  RandCostedT.sampleWithCost (PMF.pure 11) (fun _ => (3, 2))

/-- A nontrivial distribution whose exact cost depends on the sampled value. -/
noncomputable def correlatedBooleanSample :
    RandCostedT stepsQueriesCostModel Bool :=
  RandCostedT.sampleWithCost (PMF.uniformOfFintype Bool)
    (fun value => if value then (2, 0) else (0, 3))

/-- Both correctly paired value/cost paths occur in the joint distribution. -/
example :
    (⟨true, (2, 0)⟩ : CostedT stepsQueriesCostModel Bool) ∈
      correlatedBooleanSample.support := by
  simp only [correlatedBooleanSample, RandCostedT.sampleWithCost]
  rw [PMF.mem_support_map_iff]
  exact ⟨true, PMF.mem_support_uniformOfFintype true, rfl⟩

example :
    (⟨false, (0, 3)⟩ : CostedT stepsQueriesCostModel Bool) ∈
      correlatedBooleanSample.support := by
  simp only [correlatedBooleanSample, RandCostedT.sampleWithCost]
  rw [PMF.mem_support_map_iff]
  exact ⟨false, PMF.mem_support_uniformOfFintype false, rfl⟩

/-- Costs cannot be detached from their sampled values and cross-paired. -/
example :
    (⟨true, (0, 3)⟩ : CostedT stepsQueriesCostModel Bool) ∉
      correlatedBooleanSample.support := by
  simp [correlatedBooleanSample, RandCostedT.sampleWithCost]

/-- A second randomized stage lets the test observe the full value/cost pair. -/
noncomputable def randomizedTwoStage :
    RandCostedT stepsQueriesCostModel Nat :=
  RandCostedT.bind sampled fun value =>
    RandCostedT.sampleWithCost (PMF.pure (value + 1)) (fun _ => (1, 4))

example : randomizedTwoStage = PMF.pure ⟨12, (4, 6)⟩ := by
  simp only [randomizedTwoStage, sampled, RandCostedT.bind,
    RandCostedT.sampleWithCost, PMF.pure_map, PMF.pure_bind, CostedT.bind]
  rfl

example : RandCostedT.valueDist sampled = PMF.pure 11 := by
  simp [sampled]

example :
    RandCosted.valueDist (RandCostedT.mapCost totalWork sampled) = PMF.pure 11 := by
  simp [sampled]

example :
    RandCosted.costDist (RandCostedT.mapCost totalWork sampled) = PMF.pure 5 := by
  rw [RandCostedT.costDist_mapCost]
  unfold sampled
  rw [RandCostedT.costDist_sampleWithCost]
  rw [PMF.map_comp]
  rw [PMF.pure_map]
  rfl

example :
    RandCosted.valueDist
        (RandCostedT.mapCost totalWork
          (RandCostedT.bind sampled fun value =>
            RandCostedT.pure stepsQueriesCostModel (value + 1))) =
      PMF.pure 12 := by
  rw [RandCostedT.valueDist_mapCost]
  rw [RandCostedT.valueDist_bind]
  unfold sampled
  rw [RandCostedT.valueDist_sampleWithCost]
  rw [PMF.pure_bind]
  rw [RandCostedT.valueDist_pure]

end CryptoTest.Infrastructure.Computation.GenericCost

import CryptoLib.Core.Infrastructure.Computation.Algebra.Operation
import CryptoLib.Core.Infrastructure.Probability.Uniform
import CryptoLib.Core.Infrastructure.Complexity.ProgramMachine
import Mathlib.Tactic

namespace CryptoLib.Test.Infrastructure.Computation.Program

open CryptoLib.Core.Infrastructure.Complexity
open CryptoLib.Core.Infrastructure.Computation
open CryptoLib.Core.Infrastructure.Computation.Algebra
open CryptoLib.Core.Infrastructure.Computation.Cost

/-- Exact arithmetic costs used by the direct typed primitive handlers. -/
def integerAddCost (_left _right : Int) : Nat := 2
def integerNegCost (_value : Int) : Nat := 1
def integerSubCost (_left _right : Int) : Nat := 2
def integerSMulCost (_scalar : Nat) (_value : Int) : Nat := 3
def integerMulCost (_left _right : Int) : Nat := 5

/-- A direct exact addition algebra over the natural-number cost model. -/
noncomputable def integerAddAlgebra :
    CostedAlgebra CostModel.nat (AddOperation.signature Int) :=
  AddOperation.algebra CostModel.nat integerAddCost

/-- Addition semantics are independent of the exact cost function. -/
noncomputable def integerAddLaws : AlgebraLaws integerAddAlgebra :=
  AddOperation.laws CostModel.nat integerAddCost

/-- Addition bounds are attached directly to the exact addition algebra. -/
noncomputable def integerAddBounds : OperationBounds integerAddAlgebra :=
  AddOperation.bounds CostModel.nat integerAddCost
    (fun _left _right => 2) (by
      intro left right
      exact Nat.le_refl _)

/-- The sample type is deliberately different from the arithmetic carrier. -/
noncomputable def boolSample : RandCosted CostModel.nat Bool :=
  RandCosted.sampleWithCost
    (CryptoLib.Core.Infrastructure.Probability.uniformPMF Bool)
    (fun _value => 2)

/-- Uniformity is a mathematical law separate from the exact sampler. -/
noncomputable def boolSampleLaws :
    AlgebraLaws (SampleOperation.algebra CostModel.nat boolSample) :=
  SampleOperation.laws CostModel.nat boolSample
    (CryptoLib.Core.Infrastructure.Probability.uniformPMF Bool)
    (RandCosted.valueDist_sampleWithCost _ _)

/-- Sampling bounds are separate from the sampler's exact semantics. -/
noncomputable def boolSampleBounds :
    OperationBounds (SampleOperation.algebra CostModel.nat boolSample) :=
  SampleOperation.bounds CostModel.nat boolSample 2 (by
    intro result hresult
    simp only [boolSample, RandCosted.sampleWithCost] at hresult
    rw [PMF.mem_support_map_iff] at hresult
    rcases hresult with ⟨value, _hvalue, hresult⟩
    subst result
    exact Nat.le_refl _)

/-- A genuinely heterogeneous signature: calls return either `Bool` or `Int`. -/
abbrev SampleAddSignature :=
  Signature.sum (SampleOperation.signature Bool) (AddOperation.signature Int)

/-- Exact handlers compose in the same shape as their typed signatures. -/
noncomputable def sampleAddAlgebra :
    CostedAlgebra CostModel.nat SampleAddSignature :=
  CostedAlgebra.sum
    (SampleOperation.algebra CostModel.nat boolSample)
    integerAddAlgebra

/-- Mathematical specifications compose independently of exact costs. -/
noncomputable def sampleAddLaws : AlgebraLaws sampleAddAlgebra :=
  AlgebraLaws.sum
    boolSampleLaws
    integerAddLaws

/-- Upper-bound certificates also compose independently. -/
noncomputable def sampleAddBounds : OperationBounds sampleAddAlgebra :=
  OperationBounds.sum
    boolSampleBounds
    integerAddBounds

/-- An addition call in the right-hand capability of `SampleAddSignature`. -/
noncomputable def addCode (left right : Int) :
    CryptoLib.Core.Infrastructure.Computation.Program.Code sampleAddAlgebra Int :=
  .call (.inr (.add left right))

/-- A sampling call may bind a `Bool` before the program returns an `Int`. -/
noncomputable def sampledAdditionCode :
    CryptoLib.Core.Infrastructure.Computation.Program.Code sampleAddAlgebra Int :=
  .bind (.call (.inl .sample)) fun sampled =>
    addCode (if sampled then 3 else 1) 4

/-- The heterogeneous program has one structural certificate with budget `2 + 2`. -/
noncomputable def sampledAdditionCodeBound :
    CryptoLib.Core.Infrastructure.Computation.Program.Code.Bound
      sampleAddBounds sampledAdditionCode 4 :=
  CryptoLib.Core.Infrastructure.Computation.Program.Code.Bound.bind
    (CryptoLib.Core.Infrastructure.Computation.Program.Code.Bound.call
      (bounds := sampleAddBounds) (.inl .sample))
    (fun sampled =>
      CryptoLib.Core.Infrastructure.Computation.Program.Code.Bound.call
        (bounds := sampleAddBounds)
        (.inr (.add (if sampled then 3 else 1) 4)))

/-- A plain addition receives only the addition capability's budget. -/
noncomputable def addCodeBound (left right : Int) :
    CryptoLib.Core.Infrastructure.Computation.Program.Code.Bound
      sampleAddBounds (addCode left right) 2 :=
  CryptoLib.Core.Infrastructure.Computation.Program.Code.Bound.call
    (bounds := sampleAddBounds) (.inr (.add left right))

/-- The external input selects code with a genuinely input-dependent budget. -/
noncomputable def inputDependentProgram :
    CryptoLib.Core.Infrastructure.Computation.Program sampleAddAlgebra Bool Int where
  body useSampler :=
    if useSampler then sampledAdditionCode else addCode 3 4

def inputBudget (useSampler : Bool) : Nat :=
  if useSampler then 4 else 2

/-- `BoundedProgram` certifies the same program body rather than storing a copy. -/
noncomputable def boundedInputDependentProgram :
    CryptoLib.Core.Infrastructure.Computation.Program.BoundedProgram
      (Input := Bool) (Output := Int) sampleAddBounds inputBudget where
  program := inputDependentProgram
  certificate useSampler := by
    cases useSampler with
    | false => exact addCodeBound 3 4
    | true => exact sampledAdditionCodeBound

/-- Every exact path respects the budget selected by the program input. -/
theorem boundedInputDependentProgram_cost_le
    (input : Bool) (result : Costed CostModel.nat Int)
    (hresult :
      result ∈
        (CryptoLib.Core.Infrastructure.Computation.Program.runCosted
          boundedInputDependentProgram.program input).support) :
    result.cost ≤ inputBudget input :=
  boundedInputDependentProgram.cost_le_budget_of_mem_support input result hresult

/-- The exact addition handler is authoritative for both result and path cost. -/
theorem integerAddition_runCosted :
    CryptoLib.Core.Infrastructure.Computation.Program.Code.runCosted (addCode 3 4) =
      RandCosted.liftCosted (⟨7, 2⟩ : Costed CostModel.nat Int) :=
  rfl

/-- The exact interpreter path is reified with the same value and resource cost. -/
example :
    CryptoLib.Core.Infrastructure.Computation.Program.Code.Execution
      (addCode 3 4) 7 2 := by
  refine
    CryptoLib.Core.Infrastructure.Computation.Program.Code.execution_of_mem_support_runCosted
      (addCode 3 4) (⟨7, 2⟩ : Costed CostModel.nat Int) ?_
  rw [integerAddition_runCosted]
  rw [PMF.mem_support_pure_iff]

/-- Cost erasure follows the separately composed mathematical laws. -/
theorem integerAddition_valueDist :
    CryptoLib.Core.Infrastructure.Computation.Program.Code.valueDist (addCode 3 4) =
      PMF.pure 7 := by
  simpa [addCode, sampleAddLaws] using
    (CryptoLib.Core.Infrastructure.Computation.Program.Code.valueDist_call_eq
      sampleAddLaws (.inr (.add (3 : Int) 4)))

/-- The remaining arithmetic capabilities retain their direct algebra costs. -/
example :
    CryptoLib.Core.Infrastructure.Computation.Program.Code.runCosted
        (A := NegOperation.algebra CostModel.nat integerNegCost)
        (.call (.neg (5 : Int))) =
      RandCosted.liftCosted
        (⟨-5, 1⟩ : Costed CostModel.nat Int) :=
  rfl

example :
    CryptoLib.Core.Infrastructure.Computation.Program.Code.runCosted
        (A := SubOperation.algebra CostModel.nat integerSubCost)
        (.call (.sub (7 : Int) 4)) =
      RandCosted.liftCosted
        (⟨3, 2⟩ : Costed CostModel.nat Int) :=
  rfl

example :
    CryptoLib.Core.Infrastructure.Computation.Program.Code.runCosted
        (A := SMulOperation.algebra CostModel.nat integerSMulCost)
        (.call (.smul 2 (5 : Int))) =
      RandCosted.liftCosted
        (⟨10, 3⟩ : Costed CostModel.nat Int) :=
  rfl

example :
    CryptoLib.Core.Infrastructure.Computation.Program.Code.runCosted
        (A := MulOperation.algebra CostModel.nat integerMulCost)
        (.call (.mul (6 : Int) 7)) =
      RandCosted.liftCosted
        (⟨42, 5⟩ : Costed CostModel.nat Int) :=
  rfl

/-- Addition and scalar multiplication form another independently composed algebra. -/
abbrev AddSMulSignature :=
  Signature.sum
    (AddOperation.signature Int)
    (SMulOperation.signature Nat Int)

noncomputable def addSMulAlgebra :
    CostedAlgebra CostModel.nat AddSMulSignature :=
  CostedAlgebra.sum
    integerAddAlgebra
    (SMulOperation.algebra CostModel.nat integerSMulCost)

noncomputable def addSMulBounds : OperationBounds addSMulAlgebra :=
  OperationBounds.sum
    integerAddBounds
    (SMulOperation.bounds CostModel.nat integerSMulCost
      (fun _scalar _value => 3) (by
        intro scalar value
        exact Nat.le_refl _))

/-- Only the selected branch contributes exact cost; its certificate uses `max 2 3`. -/
noncomputable def branchProgram :
    CryptoLib.Core.Infrastructure.Computation.Program addSMulAlgebra Bool Int where
  body condition :=
    .branch condition
      (.call (.inl (.add 3 4)))
      (.call (.inr (.smul 2 5)))

noncomputable def boundedBranchProgram :
    CryptoLib.Core.Infrastructure.Computation.Program.BoundedProgram
      (Input := Bool) (Output := Int)
      addSMulBounds (fun _condition : Bool => max 2 3) where
  program := branchProgram
  certificate _condition :=
    CryptoLib.Core.Infrastructure.Computation.Program.Code.Bound.branchSup
      (W := WorstCaseCostModel.nat)
      (CryptoLib.Core.Infrastructure.Computation.Program.Code.Bound.call
        (bounds := addSMulBounds) (.inl (.add 3 4)))
      (CryptoLib.Core.Infrastructure.Computation.Program.Code.Bound.call
        (bounds := addSMulBounds) (.inr (.smul 2 5)))

/-- The common `max` budget bounds either selected execution path. -/
theorem boundedBranchProgram_cost_le
    (condition : Bool) (result : Costed CostModel.nat Int)
    (hresult :
      result ∈
        (CryptoLib.Core.Infrastructure.Computation.Program.runCosted
          boundedBranchProgram.program condition).support) :
    result.cost ≤ 3 := by
  simpa using
    boundedBranchProgram.cost_le_budget_of_mem_support condition result hresult

/-- `NatMeasure.nat` certifies runtime without replacing the exact `Nat` costs. -/
noncomputable def boundedInputDependentMachine :
    TimedMachine CostModel.nat NatMeasure.nat
      (fun _sec => Bool) (fun _sec _input => Int) :=
  TimedMachine.ofBoundedProgram
    NatMeasure.nat
    (fun _sec => sampleAddAlgebra)
    (fun _sec => sampleAddBounds)
    (fun _sec input => inputBudget input)
    (fun _sec => 4)
    (fun _sec => boundedInputDependentProgram)
    (by
      intro sec input
      cases input <;> simp [inputBudget, NatMeasure.nat])

@[simp] theorem boundedInputDependentMachine_runtime
    (sec : CryptoLib.Core.SecPar) :
    boundedInputDependentMachine.runtime sec = 4 :=
  rfl

/-- Program-to-machine conversion preserves ordinary semantics definitionally. -/
theorem boundedInputDependentMachine_valueDist
    (sec : CryptoLib.Core.SecPar) (input : Bool) :
    RandCosted.valueDist (boundedInputDependentMachine.run sec input) =
      CryptoLib.Core.Infrastructure.Computation.Program.valueDist
        boundedInputDependentProgram.program input := by
  rfl

end CryptoLib.Test.Infrastructure.Computation.Program

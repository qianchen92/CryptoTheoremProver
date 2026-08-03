import Crypto.Infrastructure.Computation.Algebra.Basic
import Crypto.Infrastructure.Complexity.ProgramMachine
import Mathlib.Tactic

namespace CryptoTest.Infrastructure.Computation.Program

open Crypto.Infrastructure.Complexity
open Crypto.Infrastructure.Computation
open Crypto.Infrastructure.Computation.Algebra
open Crypto.Infrastructure.Computation.Cost

/-- A small backend whose exact local operation costs are visible in tests. -/
def integerBackend : AdditiveBackend Nat Int :=
  AdditiveBackend.ofConstantCosts 2 1 2 3

/-- Independent uniform bounds for `integerBackend`. -/
def integerBounds : AdditiveCostBounds integerBackend :=
  AdditiveCostBounds.ofConstantCosts 2 1 2 3

/-- A multiplication capability with a different exact local cost. -/
def integerMultiplicativeBackend : MultiplicativeBackend Int :=
  MultiplicativeBackend.ofConstantCost 5

/-- The sample type is deliberately different from the arithmetic carrier. -/
noncomputable def boolSampler : UniformSampler Bool :=
  UniformSampler.ofConstantCost 2

/-- Uniformity is a mathematical law separate from the exact sampler. -/
noncomputable def boolSamplerLaws : UniformSamplerLaws boolSampler :=
  UniformSamplerLaws.ofConstantCost 2

/-- Sampling bounds are separate from the sampler's exact semantics. -/
noncomputable def boolSamplerBounds : UniformSamplerBounds boolSampler :=
  UniformSamplerBounds.ofConstantCost 2

/-- A genuinely heterogeneous signature: calls return either `Bool` or `Int`. -/
abbrev SampleAddSignature :=
  Signature.sum (SampleOperation.signature Bool) (AddOperation.signature Int)

/-- Exact handlers compose in the same shape as their typed signatures. -/
noncomputable def sampleAddAlgebra :
    CostedAlgebra natCostModel SampleAddSignature :=
  CostedAlgebra.sum
    (SampleOperation.algebra boolSampler)
    (AddOperation.algebra integerBackend)

/-- Mathematical specifications compose independently of exact costs. -/
noncomputable def sampleAddLaws : AlgebraLaws sampleAddAlgebra :=
  AlgebraLaws.sum
    (SampleOperation.laws boolSampler boolSamplerLaws)
    (AddOperation.laws integerBackend)

/-- Upper-bound certificates also compose independently. -/
noncomputable def sampleAddBounds : OperationBounds sampleAddAlgebra :=
  OperationBounds.sum
    (SampleOperation.bounds boolSamplerBounds)
    (AddOperation.bounds integerBounds)

/-- An addition call in the right-hand capability of `SampleAddSignature`. -/
noncomputable def addCode (left right : Int) :
    Crypto.Infrastructure.Computation.Program.Code sampleAddAlgebra Int :=
  .call (.inr (.add left right))

/-- A sampling call may bind a `Bool` before the program returns an `Int`. -/
noncomputable def sampledAdditionCode :
    Crypto.Infrastructure.Computation.Program.Code sampleAddAlgebra Int :=
  .bind (.call (.inl .sample)) fun sampled =>
    addCode (if sampled then 3 else 1) 4

/-- The heterogeneous program has one structural certificate with budget `2 + 2`. -/
noncomputable def sampledAdditionCodeBound :
    Crypto.Infrastructure.Computation.Program.Code.Bound
      sampleAddBounds sampledAdditionCode 4 :=
  Crypto.Infrastructure.Computation.Program.Code.Bound.bind
    (Crypto.Infrastructure.Computation.Program.Code.Bound.call
      (bounds := sampleAddBounds) (.inl .sample))
    (fun sampled =>
      Crypto.Infrastructure.Computation.Program.Code.Bound.call
        (bounds := sampleAddBounds)
        (.inr (.add (if sampled then 3 else 1) 4)))

/-- A plain addition receives only the addition capability's budget. -/
noncomputable def addCodeBound (left right : Int) :
    Crypto.Infrastructure.Computation.Program.Code.Bound
      sampleAddBounds (addCode left right) 2 :=
  Crypto.Infrastructure.Computation.Program.Code.Bound.call
    (bounds := sampleAddBounds) (.inr (.add left right))

/-- The external input selects code with a genuinely input-dependent budget. -/
noncomputable def inputDependentProgram :
    Crypto.Infrastructure.Computation.Program sampleAddAlgebra Bool Int where
  body useSampler :=
    if useSampler then sampledAdditionCode else addCode 3 4

def inputBudget (useSampler : Bool) : Nat :=
  if useSampler then 4 else 2

/-- `BoundedProgram` certifies the same program body rather than storing a copy. -/
noncomputable def boundedInputDependentProgram :
    Crypto.Infrastructure.Computation.Program.BoundedProgram
      (Input := Bool) (Output := Int) sampleAddBounds inputBudget where
  program := inputDependentProgram
  certificate useSampler := by
    cases useSampler with
    | false => exact addCodeBound 3 4
    | true => exact sampledAdditionCodeBound

/-- Every exact path respects the budget selected by the program input. -/
theorem boundedInputDependentProgram_cost_le
    (input : Bool) (result : Costed Int)
    (hresult :
      result ∈
        (Crypto.Infrastructure.Computation.Program.runCosted
          boundedInputDependentProgram.program input).support) :
    result.cost ≤ inputBudget input :=
  boundedInputDependentProgram.cost_le_budget_of_mem_support input result hresult

/-- The exact addition handler is authoritative for both result and path cost. -/
theorem integerAddition_runCosted :
    Crypto.Infrastructure.Computation.Program.Code.runCosted (addCode 3 4) =
      RandCosted.liftCosted (⟨7, 2⟩ : Costed Int) :=
  rfl

/-- Cost erasure follows the separately composed mathematical laws. -/
theorem integerAddition_valueDist :
    Crypto.Infrastructure.Computation.Program.Code.valueDist (addCode 3 4) =
      PMF.pure 7 := by
  simpa [addCode, sampleAddLaws] using
    (Crypto.Infrastructure.Computation.Program.Code.valueDist_call_eq
      sampleAddLaws (.inr (.add (3 : Int) 4)))

/-- The remaining arithmetic capabilities retain their backend's exact costs. -/
example :
    Crypto.Infrastructure.Computation.Program.Code.runCosted
        (A := NegOperation.algebra integerBackend) (.call (.neg (5 : Int))) =
      RandCosted.liftCosted (⟨-5, 1⟩ : Costed Int) :=
  rfl

example :
    Crypto.Infrastructure.Computation.Program.Code.runCosted
        (A := SubOperation.algebra integerBackend) (.call (.sub (7 : Int) 4)) =
      RandCosted.liftCosted (⟨3, 2⟩ : Costed Int) :=
  rfl

example :
    Crypto.Infrastructure.Computation.Program.Code.runCosted
        (A := SMulOperation.algebra integerBackend) (.call (.smul 2 (5 : Int))) =
      RandCosted.liftCosted (⟨10, 3⟩ : Costed Int) :=
  rfl

example :
    Crypto.Infrastructure.Computation.Program.Code.runCosted
        (A := MulOperation.algebra integerMultiplicativeBackend)
        (.call (.mul (6 : Int) 7)) =
      RandCosted.liftCosted (⟨42, 5⟩ : Costed Int) :=
  rfl

/-- Addition and scalar multiplication form another independently composed algebra. -/
abbrev AddSMulSignature :=
  Signature.sum
    (AddOperation.signature Int)
    (SMulOperation.signature Nat Int)

noncomputable def addSMulAlgebra :
    CostedAlgebra natCostModel AddSMulSignature :=
  CostedAlgebra.sum
    (AddOperation.algebra integerBackend)
    (SMulOperation.algebra integerBackend)

noncomputable def addSMulBounds : OperationBounds addSMulAlgebra :=
  OperationBounds.sum
    (AddOperation.bounds integerBounds)
    (SMulOperation.bounds integerBounds)

/-- Only the selected branch contributes exact cost; its certificate uses `max 2 3`. -/
noncomputable def branchProgram :
    Crypto.Infrastructure.Computation.Program addSMulAlgebra Bool Int where
  body condition :=
    .branch condition
      (.call (.inl (.add 3 4)))
      (.call (.inr (.smul 2 5)))

noncomputable def boundedBranchProgram :
    Crypto.Infrastructure.Computation.Program.BoundedProgram
      (Input := Bool) (Output := Int)
      addSMulBounds (fun _condition : Bool => max 2 3) where
  program := branchProgram
  certificate _condition :=
    Crypto.Infrastructure.Computation.Program.Code.Bound.branchSup
      (W := WorstCaseCostModel.nat)
      (Crypto.Infrastructure.Computation.Program.Code.Bound.call
        (bounds := addSMulBounds) (.inl (.add 3 4)))
      (Crypto.Infrastructure.Computation.Program.Code.Bound.call
        (bounds := addSMulBounds) (.inr (.smul 2 5)))

/-- The common `max` budget bounds either selected execution path. -/
theorem boundedBranchProgram_cost_le
    (condition : Bool) (result : Costed Int)
    (hresult :
      result ∈
        (Crypto.Infrastructure.Computation.Program.runCosted
          boundedBranchProgram.program condition).support) :
    result.cost ≤ 3 := by
  simpa using
    boundedBranchProgram.cost_le_budget_of_mem_support condition result hresult

/-- Projecting the exact cost through `NatMeasure.nat` yields a legacy machine. -/
noncomputable def boundedInputDependentMachine : TimedMachine Bool Int :=
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
    (sec : Crypto.SecPar) :
    boundedInputDependentMachine.runtime sec = 4 :=
  rfl

/-- Cost projection at the machine boundary preserves ordinary semantics. -/
theorem boundedInputDependentMachine_valueDist
    (sec : Crypto.SecPar) (input : Bool) :
    RandCosted.valueDist (boundedInputDependentMachine.run sec input) =
      Crypto.Infrastructure.Computation.Program.valueDist
        boundedInputDependentProgram.program input := by
  change
    RandCosted.valueDist
        (RandCostedT.mapCost NatMeasure.nat
          (Crypto.Infrastructure.Computation.Program.runCosted
            boundedInputDependentProgram.program input)) =
      RandCostedT.valueDist
        (Crypto.Infrastructure.Computation.Program.runCosted
          boundedInputDependentProgram.program input)
  exact RandCostedT.valueDist_mapCost NatMeasure.nat _

end CryptoTest.Infrastructure.Computation.Program

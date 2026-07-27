import Crypto.Infrastructure.Complexity.ProgramMachine

namespace CryptoTest.Infrastructure.Computation.Program

open Crypto.Infrastructure.Computation
open Crypto.Infrastructure.Computation.Algebra
open Crypto.Infrastructure.Computation.Cost

/-- A small backend whose local operation costs are visible in reduction tests. -/
def integerBackend : AdditiveBackend Nat Int :=
  AdditiveBackend.ofConstantCosts 2 1 2 3

/-- Uniform bounds for all operations in `integerBackend`. -/
def integerBounds : AdditiveCostBounds integerBackend :=
  AdditiveCostBounds.ofConstantCosts 2 1 2 3

/--
The sampled type is deliberately independent of both the scalar and carrier
types: `Scalar = Nat`, `Carrier = Int`, and `Sample = Bool`.
-/
noncomputable def boolSampler : UniformSampler Bool :=
  UniformSampler.ofConstantCost 2

/-- Sampling followed by addition has a statically composed budget of `2 + 2`. -/
noncomputable def boundedSampledAddition :
    Crypto.Infrastructure.Computation.Program.BoundedProgram
      (backend := integerBackend) (sampler := boolSampler)
      4 (ULift Int) :=
  Crypto.Infrastructure.Computation.Program.BoundedProgram.bindSample
    (Crypto.Infrastructure.Computation.Program.BoundedProgram.sample
      (backend := integerBackend) (sampler := boolSampler))
    (fun _ =>
      Crypto.Infrastructure.Computation.Program.BoundedProgram.add
        integerBounds 3 4)

/-- Every path produced by the interpreter satisfies the composed budget. -/
theorem boundedSampledAddition_cost_le
    (result : Costed (ULift Int))
    (hresult :
      result ∈
        (Crypto.Infrastructure.Computation.Program.runCosted
          boundedSampledAddition.program).support) :
    result.cost ≤ 4 :=
  Crypto.Infrastructure.Computation.Program.BoundedProgram.cost_le_budget_of_mem_support
    boundedSampledAddition result hresult

/-- The algebra backend determines both the value and local cost of addition. -/
theorem integerAddition_runCosted :
    Crypto.Infrastructure.Computation.Program.runCosted
      (backend := integerBackend) (sampler := boolSampler)
      (.add 3 4) =
        RandCosted.liftCosted
          (⟨ULift.up (7 : Int), 2⟩ : Costed (ULift Int)) :=
  rfl

/-- A timed machine obtains its runtime certificate directly from the program budget. -/
noncomputable def boundedSampledAdditionMachine :
    Crypto.Infrastructure.Complexity.TimedMachine Unit (ULift Int) :=
  Crypto.Infrastructure.Complexity.TimedMachine.ofBoundedProgram
    integerBackend boolSampler (fun _sec => 4)
    (fun _sec _input => boundedSampledAddition)

@[simp] theorem boundedSampledAdditionMachine_runtime
    (sec : Crypto.SecPar) :
    boundedSampledAdditionMachine.runtime sec = 4 :=
  rfl

/-- Carrier-valued programs erase their internal `ULift` at the machine boundary. -/
noncomputable def boundedIntegerAdditionMachine :
    Crypto.Infrastructure.Complexity.TimedMachine (Int × Int) Int :=
  Crypto.Infrastructure.Complexity.TimedMachine.ofBoundedCarrierProgram
    integerBackend boolSampler (fun _sec => integerBounds.addBudget)
    (fun _sec input =>
      Crypto.Infrastructure.Computation.Program.BoundedProgram.add
        integerBounds input.1 input.2)

@[simp] theorem boundedIntegerAdditionMachine_runtime
    (sec : Crypto.SecPar) :
    boundedIntegerAdditionMachine.runtime sec = 2 :=
  rfl

/-- The generated machine certificate consumes the same program-derived path cost. -/
theorem boundedIntegerAdditionMachine_cost_le
    (sec : Crypto.SecPar) (input : Int × Int)
    (result : Costed Int)
    (hresult : result ∈ (boundedIntegerAdditionMachine.run sec input).support) :
    result.cost ≤ boundedIntegerAdditionMachine.runtime sec :=
  boundedIntegerAdditionMachine.runtime_sound sec input result hresult

/--
A conditional receives the maximum branch budget, even though only the selected
branch contributes to a concrete path.
-/
noncomputable def boundedBranch :
    Crypto.Infrastructure.Computation.Program.BoundedProgram
      (backend := integerBackend) (sampler := boolSampler)
      3 (ULift Int) := by
  simpa [integerBounds] using
    (Crypto.Infrastructure.Computation.Program.BoundedProgram.branch true
      (Crypto.Infrastructure.Computation.Program.BoundedProgram.add
        integerBounds 3 4)
      (Crypto.Infrastructure.Computation.Program.BoundedProgram.smul
        integerBounds 2 5))

/-- The `max` branch certificate still bounds every selected execution path. -/
theorem boundedBranch_cost_le
    (result : Costed (ULift Int))
    (hresult :
      result ∈
        (Crypto.Infrastructure.Computation.Program.runCosted
          boundedBranch.program).support) :
    result.cost ≤ 3 :=
  boundedBranch.sound result hresult

end CryptoTest.Infrastructure.Computation.Program

import Crypto.Infrastructure.Complexity.Machine
import Crypto.Infrastructure.Computation.Cost.Projection
import Crypto.Infrastructure.Computation.Program

namespace Crypto.Infrastructure.Complexity

open Crypto.Infrastructure.Asymptotic
open Crypto.Infrastructure.Computation
open Crypto.Infrastructure.Computation.Algebra
open Crypto.Infrastructure.Computation.Cost

universe uCost uIn uOut uResult uOp

namespace TimedMachine

/--
Build a legacy `Nat`-timed machine from programs over an arbitrary exact
resource model.

`measure` is the explicit complexity boundary.  Its monotonicity transfers the
program certificate to the declared runtime, while `mapCost` preserves the
ordinary value distribution.
-/
noncomputable def ofBoundedProgram
    {M : CostModel.{uCost}}
    {S : Signature.{uResult, uOp}}
    {Input : Type uIn} {Output : Type uResult}
    (measure : NatMeasure M)
    (A : Crypto.SecPar → CostedAlgebra M S)
    (bounds : (sec : Crypto.SecPar) → OperationBounds (A sec))
    (budget : Crypto.SecPar → Input → M.Cost)
    (runtime : Crypto.SecPar → Nat)
    (program :
      (sec : Crypto.SecPar) →
        Program.BoundedProgram (Input := Input) (Output := Output)
          (bounds sec) (budget sec))
    (budget_le_runtime :
      ∀ sec input, measure (budget sec input) ≤ runtime sec) :
    TimedMachine Input Output where
  run := fun sec input =>
    RandCostedT.mapCost measure
      (Program.runCosted (program sec).program input)
  runtime := runtime
  runtime_sound := by
    intro sec input result hresult
    simp only [RandCostedT.mapCost] at hresult
    rw [PMF.mem_support_map_iff] at hresult
    rcases hresult with ⟨exactResult, hexactResult, hresult⟩
    subst result
    exact le_trans
      (measure.monotone_toNat
        ((program sec).cost_le_budget_of_mem_support
          input exactResult hexactResult))
      (budget_le_runtime sec input)

/-- Projecting an exact program cost to `Nat` preserves its value distribution. -/
@[simp] theorem valueDist_run_ofBoundedProgram
    {M : CostModel.{uCost}}
    {S : Signature.{uResult, uOp}}
    {Input : Type uIn} {Output : Type uResult}
    (measure : NatMeasure M)
    (A : Crypto.SecPar → CostedAlgebra M S)
    (bounds : (sec : Crypto.SecPar) → OperationBounds (A sec))
    (budget : Crypto.SecPar → Input → M.Cost)
    (runtime : Crypto.SecPar → Nat)
    (program :
      (sec : Crypto.SecPar) →
        Program.BoundedProgram (Input := Input) (Output := Output)
          (bounds sec) (budget sec))
    (budget_le_runtime :
      ∀ sec input, measure (budget sec input) ≤ runtime sec)
    (sec : Crypto.SecPar) (input : Input) :
    RandCosted.valueDist
        ((ofBoundedProgram measure A bounds budget runtime program
          budget_le_runtime).run sec input) =
      Program.valueDist (program sec).program input := by
  change
    RandCosted.valueDist
        (RandCostedT.mapCost measure
          (Program.runCosted (program sec).program input)) =
      RandCostedT.valueDist
        (Program.runCosted (program sec).program input)
  exact RandCostedT.valueDist_mapCost measure _

/--
Apply a value-only output map after projecting an exact program cost to `Nat`.
-/
noncomputable def ofMappedBoundedProgram
    {M : CostModel.{uCost}}
    {S : Signature.{uResult, uOp}}
    {Input : Type uIn} {ProgramOutput : Type uResult} {Output : Type uOut}
    (measure : NatMeasure M)
    (A : Crypto.SecPar → CostedAlgebra M S)
    (bounds : (sec : Crypto.SecPar) → OperationBounds (A sec))
    (budget : Crypto.SecPar → Input → M.Cost)
    (runtime : Crypto.SecPar → Nat)
    (mapOutput : ProgramOutput → Output)
    (program :
      (sec : Crypto.SecPar) →
        Program.BoundedProgram (Input := Input) (Output := ProgramOutput)
          (bounds sec) (budget sec))
    (budget_le_runtime :
      ∀ sec input, measure (budget sec input) ≤ runtime sec) :
    TimedMachine Input Output where
  run := fun sec input =>
    RandCosted.map mapOutput
      (RandCostedT.mapCost measure
        (Program.runCosted (program sec).program input))
  runtime := runtime
  runtime_sound := by
    intro sec input result hresult
    simp only [RandCosted.map, RandCostedT.mapCost] at hresult
    rw [PMF.mem_support_map_iff] at hresult
    rcases hresult with ⟨projectedResult, hprojectedResult, hresult⟩
    rw [PMF.mem_support_map_iff] at hprojectedResult
    rcases hprojectedResult with ⟨exactResult, hexactResult, hprojectedResult⟩
    subst projectedResult
    subst result
    exact le_trans
      (measure.monotone_toNat
        ((program sec).cost_le_budget_of_mem_support
          input exactResult hexactResult))
      (budget_le_runtime sec input)

/-- Output mapping and cost projection preserve the expected mapped semantics. -/
@[simp] theorem valueDist_run_ofMappedBoundedProgram
    {M : CostModel.{uCost}}
    {S : Signature.{uResult, uOp}}
    {Input : Type uIn} {ProgramOutput : Type uResult} {Output : Type uOut}
    (measure : NatMeasure M)
    (A : Crypto.SecPar → CostedAlgebra M S)
    (bounds : (sec : Crypto.SecPar) → OperationBounds (A sec))
    (budget : Crypto.SecPar → Input → M.Cost)
    (runtime : Crypto.SecPar → Nat)
    (mapOutput : ProgramOutput → Output)
    (program :
      (sec : Crypto.SecPar) →
        Program.BoundedProgram (Input := Input) (Output := ProgramOutput)
          (bounds sec) (budget sec))
    (budget_le_runtime :
      ∀ sec input, measure (budget sec input) ≤ runtime sec)
    (sec : Crypto.SecPar) (input : Input) :
    RandCosted.valueDist
        ((ofMappedBoundedProgram measure A bounds budget runtime mapOutput
          program budget_le_runtime).run sec input) =
      PMF.map mapOutput (Program.valueDist (program sec).program input) := by
  change
    RandCosted.valueDist
        (RandCosted.map mapOutput
          (RandCostedT.mapCost measure
            (Program.runCosted (program sec).program input))) =
      PMF.map mapOutput
        (RandCostedT.valueDist
          (Program.runCosted (program sec).program input))
  rw [RandCosted.valueDist_map, RandCostedT.valueDist_mapCost]

/-- Nat-cost specialization with the identity resource observation. -/
noncomputable def ofNatBoundedProgram
    {S : Signature.{uResult, uOp}}
    {Input : Type uIn} {Output : Type uResult}
    (A : Crypto.SecPar → CostedAlgebra natCostModel S)
    (bounds : (sec : Crypto.SecPar) → OperationBounds (A sec))
    (runtime : Crypto.SecPar → Nat)
    (program :
      (sec : Crypto.SecPar) →
        Program.BoundedProgram (Input := Input) (Output := Output)
          (bounds sec) (fun _input => runtime sec)) :
    TimedMachine Input Output :=
  ofBoundedProgram NatMeasure.nat A bounds
    (fun sec _input => runtime sec) runtime program (by
      intro sec input
      exact Nat.le_refl _)

end TimedMachine

namespace PPTMachine

/-- Program-derived timed machines are PPT when their projected runtime is polynomial. -/
noncomputable def ofBoundedProgram
    {M : CostModel.{uCost}}
    {S : Signature.{uResult, uOp}}
    {Input : Type uIn} {Output : Type uResult}
    (measure : NatMeasure M)
    (A : Crypto.SecPar → CostedAlgebra M S)
    (bounds : (sec : Crypto.SecPar) → OperationBounds (A sec))
    (budget : Crypto.SecPar → Input → M.Cost)
    (runtime : Crypto.SecPar → Nat)
    (program :
      (sec : Crypto.SecPar) →
        Program.BoundedProgram (Input := Input) (Output := Output)
          (bounds sec) (budget sec))
    (budget_le_runtime :
      ∀ sec input, measure (budget sec input) ≤ runtime sec)
    (runtime_isPoly : IsPolyBounded runtime) :
    PPTMachine Input Output :=
  { TimedMachine.ofBoundedProgram
      measure A bounds budget runtime program budget_le_runtime with
    runtime_isPoly := runtime_isPoly }

/-- Output-mapped specialization of `ofBoundedProgram`. -/
noncomputable def ofMappedBoundedProgram
    {M : CostModel.{uCost}}
    {S : Signature.{uResult, uOp}}
    {Input : Type uIn} {ProgramOutput : Type uResult} {Output : Type uOut}
    (measure : NatMeasure M)
    (A : Crypto.SecPar → CostedAlgebra M S)
    (bounds : (sec : Crypto.SecPar) → OperationBounds (A sec))
    (budget : Crypto.SecPar → Input → M.Cost)
    (runtime : Crypto.SecPar → Nat)
    (mapOutput : ProgramOutput → Output)
    (program :
      (sec : Crypto.SecPar) →
        Program.BoundedProgram (Input := Input) (Output := ProgramOutput)
          (bounds sec) (budget sec))
    (budget_le_runtime :
      ∀ sec input, measure (budget sec input) ≤ runtime sec)
    (runtime_isPoly : IsPolyBounded runtime) :
    PPTMachine Input Output :=
  { TimedMachine.ofMappedBoundedProgram
      measure A bounds budget runtime mapOutput program budget_le_runtime with
    runtime_isPoly := runtime_isPoly }

end PPTMachine

end Crypto.Infrastructure.Complexity

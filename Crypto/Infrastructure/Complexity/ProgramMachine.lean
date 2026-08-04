import Crypto.Infrastructure.Complexity.Machine
import Crypto.Infrastructure.Computation.Program.Basic

namespace Crypto.Infrastructure.Complexity

open Crypto.Infrastructure.Asymptotic
open Crypto.Infrastructure.Computation
open Crypto.Infrastructure.Computation.Algebra
open Crypto.Infrastructure.Computation.Cost

universe uCost uIn uResult uOp

namespace TimedMachine

/--
Build a timed machine from exact-cost programs over an arbitrary resource model.

The resulting machine keeps the program's original `M.Cost` annotations.  The
chosen `NatMeasure` appears only in the runtime certificate and never rewrites
the machine's execution distribution.
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
    TimedMachine M measure
      (fun _sec => Input) (fun _sec _input => Output) where
  toProbabilisticMachine :=
    { run := fun sec input =>
        Program.runCosted (program sec).program input }
  certificate :=
    { toExactCostCertificate :=
        { budget := budget
          sound := fun sec input => (program sec).costBound input }
      runtime := runtime
      budget_le_runtime := budget_le_runtime }

/-- Program-to-machine conversion preserves exact value erasure definitionally. -/
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
      Program.valueDist (program sec).program input :=
  rfl

end TimedMachine

namespace PPTMachine

/--
Build a PPT machine from the same exact program run, a polynomial runtime
certificate, and an independent host-level admission proof.

`BoundedProgram` alone is intentionally insufficient: its higher-order Lean
boundary can hide computation in inputs, pure values, and continuations.
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
      ∀ sec input, measure (budget sec input) ≤ runtime sec)
    (runtime_isPoly : IsPolyBounded runtime)
    (admission : PPTAdmissible
      (TimedMachine.ofBoundedProgram
        measure A bounds budget runtime program budget_le_runtime).run
      runtime) :
    PPTMachine M measure
      (fun _sec => Input) (fun _sec _input => Output) :=
  PPTMachine.ofAdmittedTimedMachine
    (TimedMachine.ofBoundedProgram
      measure A bounds budget runtime program budget_le_runtime)
    runtime_isPoly admission

/-- PPT program conversion preserves the original exact value distribution. -/
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
    (runtime_isPoly : IsPolyBounded runtime)
    (admission : PPTAdmissible
      (TimedMachine.ofBoundedProgram
        measure A bounds budget runtime program budget_le_runtime).run
      runtime)
    (sec : Crypto.SecPar) (input : Input) :
    RandCosted.valueDist
        ((ofBoundedProgram measure A bounds budget runtime program
          budget_le_runtime runtime_isPoly admission).run sec input) =
      Program.valueDist (program sec).program input :=
  rfl

end PPTMachine

end Crypto.Infrastructure.Complexity

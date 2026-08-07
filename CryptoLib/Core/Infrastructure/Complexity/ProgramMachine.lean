import CryptoLib.Core.Infrastructure.Complexity.Machine
import CryptoLib.Core.Infrastructure.Computation.Program.Basic

namespace CryptoLib.Core.Infrastructure.Complexity

open CryptoLib.Core.Infrastructure.Asymptotic
open CryptoLib.Core.Infrastructure.Computation
open CryptoLib.Core.Infrastructure.Computation.Algebra
open CryptoLib.Core.Infrastructure.Computation.Cost

universe uCost uIn uResult uOp

namespace TimedMachine

variable
    {M : CostModel.{uCost}}
    {S : Signature.{uResult, uOp}}
    {Input : Type uIn} {Output : Type uResult}

/--
Build a timed machine from exact-cost programs over an arbitrary resource model.

The resulting machine keeps the program's original `M.Cost` annotations.  The
chosen `NatMeasure` appears only in the runtime certificate and never rewrites
the machine's execution distribution.
-/
noncomputable def ofBoundedProgram
    (measure : NatMeasure M)
    (A : CryptoLib.Core.SecPar → CostedAlgebra M S)
    (bounds : (sec : CryptoLib.Core.SecPar) → OperationBounds (A sec))
    (budget : CryptoLib.Core.SecPar → Input → M.Cost)
    (runtime : CryptoLib.Core.SecPar → Nat)
    (program :
      (sec : CryptoLib.Core.SecPar) →
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
    (measure : NatMeasure M)
    (A : CryptoLib.Core.SecPar → CostedAlgebra M S)
    (bounds : (sec : CryptoLib.Core.SecPar) → OperationBounds (A sec))
    (budget : CryptoLib.Core.SecPar → Input → M.Cost)
    (runtime : CryptoLib.Core.SecPar → Nat)
    (program :
      (sec : CryptoLib.Core.SecPar) →
        Program.BoundedProgram (Input := Input) (Output := Output)
          (bounds sec) (budget sec))
    (budget_le_runtime :
      ∀ sec input, measure (budget sec input) ≤ runtime sec)
    (sec : CryptoLib.Core.SecPar) (input : Input) :
    RandCosted.valueDist
        ((ofBoundedProgram measure A bounds budget runtime program
          budget_le_runtime).run sec input) =
      Program.valueDist (program sec).program input :=
  rfl

end TimedMachine

namespace PPTMachine

variable
    {M : CostModel.{uCost}}
    {S : Signature.{uResult, uOp}}
    {Input : Type uIn} {Output : Type uResult}

/--
Build a PPT machine from the same exact program run, a polynomial runtime
certificate, and an independent host-level admission proof.

`BoundedProgram` alone is intentionally insufficient: its higher-order Lean
boundary can hide computation in inputs, pure values, and continuations.
-/
noncomputable def ofBoundedProgram
    (measure : NatMeasure M)
    (A : CryptoLib.Core.SecPar → CostedAlgebra M S)
    (bounds : (sec : CryptoLib.Core.SecPar) → OperationBounds (A sec))
    (budget : CryptoLib.Core.SecPar → Input → M.Cost)
    (runtime : CryptoLib.Core.SecPar → Nat)
    (program :
      (sec : CryptoLib.Core.SecPar) →
        Program.BoundedProgram (Input := Input) (Output := Output)
          (bounds sec) (budget sec))
    (budget_le_runtime :
      ∀ sec input, measure (budget sec input) ≤ runtime sec)
    (runtime_isPoly : IsPolyBounded runtime)
    (admission : PPTAdmissible M measure
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
    (measure : NatMeasure M)
    (A : CryptoLib.Core.SecPar → CostedAlgebra M S)
    (bounds : (sec : CryptoLib.Core.SecPar) → OperationBounds (A sec))
    (budget : CryptoLib.Core.SecPar → Input → M.Cost)
    (runtime : CryptoLib.Core.SecPar → Nat)
    (program :
      (sec : CryptoLib.Core.SecPar) →
        Program.BoundedProgram (Input := Input) (Output := Output)
          (bounds sec) (budget sec))
    (budget_le_runtime :
      ∀ sec input, measure (budget sec input) ≤ runtime sec)
    (runtime_isPoly : IsPolyBounded runtime)
    (admission : PPTAdmissible M measure
      (TimedMachine.ofBoundedProgram
        measure A bounds budget runtime program budget_le_runtime).run
      runtime)
    (sec : CryptoLib.Core.SecPar) (input : Input) :
    RandCosted.valueDist
        ((ofBoundedProgram measure A bounds budget runtime program
          budget_le_runtime runtime_isPoly admission).run sec input) =
      Program.valueDist (program sec).program input :=
  rfl

end PPTMachine

end CryptoLib.Core.Infrastructure.Complexity

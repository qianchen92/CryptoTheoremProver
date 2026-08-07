import CryptoLib.Core.Infrastructure.Complexity.CostBound
import CryptoLib.Core.Infrastructure.Complexity.Operational

namespace CryptoLib.Core.Infrastructure.Complexity

open CryptoLib.Core.Infrastructure.Computation
open CryptoLib.Core.Infrastructure.Computation.Cost
open CryptoLib.Core.Infrastructure.Computation.Oracle

universe uCost uIn uOut uMapped uFirstOrder uBase uValue uOp
  uClosedInput uCallerInput uOutput uOracle uQuery uResponse

/--
A randomized machine over one exact cost model and fully dependent I/O families.

The machine stores exactly one computation.  Cost and polynomial certificates
are attached by the refinements below without replacing that computation.
-/
structure ProbabilisticMachine
    (M : CostModel.{uCost})
    (Input : CryptoLib.Core.SecPar → Type uIn)
    (Output : (sec : CryptoLib.Core.SecPar) → Input sec → Type uOut) where
  run : RandomizedComputation M Input Output

namespace ProbabilisticMachine

variable
    {M : CostModel.{uCost}}
    {Input : CryptoLib.Core.SecPar → Type uIn}
    {Output : (sec : CryptoLib.Core.SecPar) → Input sec → Type uOut}

/-- Forget exact path costs and expose the ordinary dependent output distribution. -/
noncomputable def runDist
    (machine : ProbabilisticMachine M Input Output)
    (sec : CryptoLib.Core.SecPar) (input : Input sec) :
    PMF (Output sec input) :=
  RandomizedComputation.valueDist machine.run sec input

/-- Build a zero-cost probabilistic machine from a dependent pure function. -/
noncomputable def ofFunction
    (M : CostModel.{uCost})
    {Input : CryptoLib.Core.SecPar → Type uIn}
    {Output : (sec : CryptoLib.Core.SecPar) → Input sec → Type uOut}
    (function :
      (sec : CryptoLib.Core.SecPar) → (input : Input sec) → Output sec input) :
    ProbabilisticMachine M Input Output where
  run := RandomizedComputation.pure M function

/-- Apply a dependent value-only map while preserving every exact path cost. -/
noncomputable def map
    {Mapped : (sec : CryptoLib.Core.SecPar) → Input sec → Type uMapped}
    (transform :
      (sec : CryptoLib.Core.SecPar) → (input : Input sec) →
        Output sec input → Mapped sec input)
    (machine : ProbabilisticMachine M Input Output) :
    ProbabilisticMachine M Input Mapped where
  run := RandomizedComputation.map transform machine.run

@[simp] theorem runDist_ofFunction
    (M : CostModel.{uCost})
    {Input : CryptoLib.Core.SecPar → Type uIn}
    {Output : (sec : CryptoLib.Core.SecPar) → Input sec → Type uOut}
    (function :
      (sec : CryptoLib.Core.SecPar) → (input : Input sec) → Output sec input)
    (sec : CryptoLib.Core.SecPar) (input : Input sec) :
    (ofFunction M function).runDist sec input =
      PMF.pure (function sec input) := by
  exact RandomizedComputation.valueDist_pure M function sec input

@[simp] theorem runDist_map
    {Mapped : (sec : CryptoLib.Core.SecPar) → Input sec → Type uMapped}
    (transform :
      (sec : CryptoLib.Core.SecPar) → (input : Input sec) →
        Output sec input → Mapped sec input)
    (machine : ProbabilisticMachine M Input Output)
    (sec : CryptoLib.Core.SecPar) (input : Input sec) :
    (machine.map transform).runDist sec input =
      PMF.map (transform sec input) (machine.runDist sec input) := by
  exact RandomizedComputation.valueDist_map transform machine.run sec input

end ProbabilisticMachine

/-- A machine whose one exact computation has a measured runtime certificate. -/
structure TimedMachine
    (M : CostModel.{uCost}) (measure : NatMeasure M)
    (Input : CryptoLib.Core.SecPar → Type uIn)
    (Output : (sec : CryptoLib.Core.SecPar) → Input sec → Type uOut)
    extends ProbabilisticMachine M Input Output where
  certificate : RuntimeCertificate measure run

namespace TimedMachine

variable
    {M : CostModel.{uCost}} {measure : NatMeasure M}
    {Input : CryptoLib.Core.SecPar → Type uIn}
    {Output : (sec : CryptoLib.Core.SecPar) → Input sec → Type uOut}

/-- The exact input-dependent budget certified for this machine. -/
def costBound
    (machine : TimedMachine M measure Input Output) :
    (sec : CryptoLib.Core.SecPar) → Input sec → M.Cost :=
  machine.certificate.budget

/-- The uniform natural-number runtime obtained through the chosen measure. -/
def runtime
    (machine : TimedMachine M measure Input Output) : CryptoLib.Core.SecPar → Nat :=
  machine.certificate.runtime

/-- Every concrete exact path respects the stored exact budget. -/
theorem cost_le_bound
    (machine : TimedMachine M measure Input Output)
    (sec : CryptoLib.Core.SecPar) (input : Input sec)
    (result : Costed M (Output sec input))
    (hresult : result ∈ (machine.run sec input).support) :
    M.instPartialOrder.le result.cost (machine.costBound sec input) :=
  machine.certificate.cost_le_budget sec input result hresult

/-- Measuring any concrete exact path yields at most the uniform runtime. -/
theorem measuredCost_le_runtime
    (machine : TimedMachine M measure Input Output)
    (sec : CryptoLib.Core.SecPar) (input : Input sec)
    (result : Costed M (Output sec input))
    (hresult : result ∈ (machine.run sec input).support) :
    measure result.cost ≤ machine.runtime sec :=
  machine.certificate.measuredCost_le_runtime sec input result hresult

/-- Build a zero-runtime timed machine from a dependent pure function. -/
noncomputable def ofFunction
    (M : CostModel.{uCost}) (measure : NatMeasure M)
    {Input : CryptoLib.Core.SecPar → Type uIn}
    {Output : (sec : CryptoLib.Core.SecPar) → Input sec → Type uOut}
    (function :
      (sec : CryptoLib.Core.SecPar) → (input : Input sec) → Output sec input) :
    TimedMachine M measure Input Output where
  toProbabilisticMachine := ProbabilisticMachine.ofFunction M function
  certificate := RuntimeCertificate.pure M measure function

/-- Dependent value mapping preserves the machine's exact and measured bounds. -/
noncomputable def map
    {Mapped : (sec : CryptoLib.Core.SecPar) → Input sec → Type uMapped}
    (transform :
      (sec : CryptoLib.Core.SecPar) → (input : Input sec) →
        Output sec input → Mapped sec input)
    (machine : TimedMachine M measure Input Output) :
    TimedMachine M measure Input Mapped where
  toProbabilisticMachine := machine.toProbabilisticMachine.map transform
  certificate := machine.certificate.map transform

/--
Interpret a fixed reified first-order program as a constant-family timed
machine. This constructor transports an exact first-order path bound only; PPT
admission still requires `PPTMachine.ofFirstOrderCode` and a structurally valid
algebra.
-/
noncomputable def ofFirstOrderProgram
    {M : CostModel.{uCost}} (measure : NatMeasure M)
    {Base : Type uBase} {interpret : Base → Type uValue}
    {S : CryptoLib.Program.Signature.{uBase, uOp} Base}
    (A : CryptoLib.Program.CostedAlgebra M interpret S)
    {FirstOrderInput FirstOrderOutput : CryptoLib.Program.Ty Base}
    (program : CryptoLib.Program.Procedure interpret S
      FirstOrderInput FirstOrderOutput)
    (budget : CryptoLib.Program.Ty.denote interpret FirstOrderInput → M.Cost)
    (runtime : Nat)
    (costBound : CryptoLib.Program.Procedure.CostBound A program budget)
    (budget_le_runtime : ∀ input, measure (budget input) ≤ runtime) :
    TimedMachine M measure
      (fun _sec => CryptoLib.Program.Ty.denote interpret FirstOrderInput)
      (fun _sec _input =>
        CryptoLib.Program.Ty.denote interpret FirstOrderOutput) where
  toProbabilisticMachine :=
    { run := fun _sec input => CryptoLib.Program.Procedure.runCosted A program input }
  certificate :=
    { budget := fun _sec input => budget input
      sound := fun _sec input => costBound input
      runtime := fun _sec => runtime
      budget_le_runtime := fun _sec input => budget_le_runtime input }

@[simp] theorem runtime_ofFunction
    (M : CostModel.{uCost}) (measure : NatMeasure M)
    {Input : CryptoLib.Core.SecPar → Type uIn}
    {Output : (sec : CryptoLib.Core.SecPar) → Input sec → Type uOut}
    (function :
      (sec : CryptoLib.Core.SecPar) → (input : Input sec) → Output sec input) :
    (ofFunction M measure function).runtime = fun _sec => 0 :=
  rfl

end TimedMachine

namespace FirstOrderOperationalCode

/--
Interpret internally certified first-order code as a constant-family timed
machine. The security parameter indexes the cryptographic interface but does
not select a different hidden Lean program.
-/
noncomputable def toTimedMachine
    {M : CostModel.{uFirstOrder}} {measure : NatMeasure M}
    {Base : Type uFirstOrder} {interpret : Base → Type uFirstOrder}
    {S : CryptoLib.Program.Signature.{uFirstOrder, uFirstOrder} Base}
    {A : CryptoLib.Program.CostedAlgebra M interpret S}
    {FirstOrderInput FirstOrderOutput : CryptoLib.Program.Ty Base}
    (code : FirstOrderOperationalCode M measure interpret A
      FirstOrderInput FirstOrderOutput) :
    TimedMachine M measure
      (fun _sec => CryptoLib.Program.Ty.denote interpret FirstOrderInput)
      (fun _sec _input => CryptoLib.Program.Ty.denote interpret FirstOrderOutput) where
  toProbabilisticMachine :=
    { run := fun _sec input =>
        CryptoLib.Program.Procedure.runCosted A code.program input }
  certificate :=
    { budget := fun _sec input => code.budget input
      sound := fun _sec input => code.costBound input
      runtime := fun _sec => code.runtime
      budget_le_runtime := fun _sec input => code.budget_le_runtime input }

end FirstOrderOperationalCode

/--
An exact run and claimed runtime realized by validated code in an explicit
host-independent operational model.

Exact path annotations and a polynomial bound on their projection do not, by
themselves, account for Lean host reduction hidden in pure values, higher-order
continuations, or value maps. The realization therefore records a model and
code whose denotation is this exact run and whose operational claim is this
runtime. Canonical first-order code is validated internally; other backends
retain an explicit external validation boundary.
-/
private inductive ControlledOracleSeal
    (M : CostModel.{uCost}) (measure : NatMeasure M)
    {Input : CryptoLib.Core.SecPar → Type uIn}
    {Output : (sec : CryptoLib.Core.SecPar) → Input sec → Type uOut}
    (run : RandomizedComputation M Input Output)
    (runtime : CryptoLib.Core.SecPar → Nat) : Prop where
  | intro : ControlledOracleSeal M measure run runtime

inductive PPTAdmissible
    (M : CostModel.{uCost}) (measure : NatMeasure M) :
    {Input : CryptoLib.Core.SecPar → Type uIn} →
    {Output : (sec : CryptoLib.Core.SecPar) → Input sec → Type uOut} →
    RandomizedComputation M Input Output →
    (CryptoLib.Core.SecPar → Nat) → Prop where
  | operational
      {Input : CryptoLib.Core.SecPar → Type uIn}
      {Output : (sec : CryptoLib.Core.SecPar) → Input sec → Type uOut}
      {run : RandomizedComputation M Input Output}
      {runtime : CryptoLib.Core.SecPar → Nat} :
      OperationalRealization run runtime →
        PPTAdmissible M measure run runtime
  | controlled
      {Input : CryptoLib.Core.SecPar → Type uIn}
      {Output : (sec : CryptoLib.Core.SecPar) → Input sec → Type uOut}
      {run : RandomizedComputation M Input Output}
      {runtime : CryptoLib.Core.SecPar → Nat} :
      ControlledOracleSeal M measure run runtime →
        PPTAdmissible M measure run runtime

namespace PPTAdmissible

/--
The sole public constructor for the controlled admission token.  Its result is
indexed by the compiler's exact `close` run and runtime expression; callers
cannot use it to admit a different host wrapper.
-/
theorem ofControlledOracleAdapter
    {M : CostModel.{uCost}} {measure : NatMeasure M}
    {ClosedInput : CryptoLib.Core.SecPar → Type uClosedInput}
    {CallerInput : CryptoLib.Core.SecPar → Type uCallerInput}
    {ClosedOutput : CryptoLib.Core.SecPar → Type uOutput}
    {Spec : (sec : CryptoLib.Core.SecPar) → CallerInput sec →
      OracleSpec.{uOracle, uQuery, uResponse}}
    {Base : Type uBase} {interpret : Base → Type uValue}
    {S : CryptoLib.Program.Signature.{uBase, uBase} Base}
    {A : CryptoLib.Program.CostedAlgebra M interpret S}
    {PrepareInput PrepareOutput RejectInput RejectOutput
      QueryInput QueryOutput : CryptoLib.Program.Ty Base}
    (caller : OracleMachine M CallerInput
      (fun sec _input => ClosedOutput sec) Spec)
    (adapter : FirstOrderOracleAdapter M measure ClosedInput CallerInput
      ClosedOutput Spec interpret A PrepareInput PrepareOutput RejectInput
      RejectOutput QueryInput QueryOutput)
    (localRuntime totalQueryRuntime : CryptoLib.Core.SecPar → Nat)
    (_callerAdmission : OperationalRealization caller
      (localRuntime, totalQueryRuntime)) :
    PPTAdmissible M measure (adapter.close caller)
      (adapter.closedRuntime (localRuntime, totalQueryRuntime)) :=
  .controlled .intro

end PPTAdmissible

/--
A polynomially bounded annotated machine that is additionally admitted by a
host-independent PPT model.

The admission field is the firewall between internal path-cost certificates
and cryptographic quantification over PPT adversaries.  In particular, no
arbitrary Lean function is admitted merely because it can be placed in a
zero-cost `pure` computation.
-/
structure PPTMachine
    (M : CostModel.{uCost}) (measure : NatMeasure M)
    (Input : CryptoLib.Core.SecPar → Type uIn)
    (Output : (sec : CryptoLib.Core.SecPar) → Input sec → Type uOut)
    extends TimedMachine M measure Input Output where
  runtime_poly :
    CryptoLib.Core.Infrastructure.Asymptotic.IsPolyBounded toTimedMachine.runtime
  admission : PPTAdmissible M measure
    toTimedMachine.run toTimedMachine.runtime

namespace PPTMachine

variable
    {M : CostModel.{uCost}} {measure : NatMeasure M}
    {Input : CryptoLib.Core.SecPar → Type uIn}
    {Output : (sec : CryptoLib.Core.SecPar) → Input sec → Type uOut}

/-- The exact input-dependent budget certified for this PPT machine. -/
def costBound
    (machine : PPTMachine M measure Input Output) :
    (sec : CryptoLib.Core.SecPar) → Input sec → M.Cost :=
  machine.certificate.budget

/-- The uniform polynomial natural-number runtime. -/
def runtime
    (machine : PPTMachine M measure Input Output) : CryptoLib.Core.SecPar → Nat :=
  machine.certificate.runtime

/-- The stored runtime is polynomially bounded. -/
theorem runtime_isPoly
    (machine : PPTMachine M measure Input Output) :
    CryptoLib.Core.Infrastructure.Asymptotic.IsPolyBounded machine.runtime :=
  machine.runtime_poly

/--
Promote an annotated timed machine only after an operational model has admitted
that exact machine. Polynomiality of the measured bound and PPT admission are
intentionally separate obligations. The first-order constructor below derives
the latter internally.
-/
def ofAdmittedTimedMachine
    (machine : TimedMachine M measure Input Output)
    (runtime_isPoly :
      CryptoLib.Core.Infrastructure.Asymptotic.IsPolyBounded machine.runtime)
    (admission : PPTAdmissible M measure machine.run machine.runtime) :
    PPTMachine M measure Input Output where
  toTimedMachine := machine
  runtime_poly := runtime_isPoly
  admission := admission

/--
Build a PPT machine directly from internally validated first-order code.

This constructor needs no external `OperationalModel.ValidCode` assumption:
the reified syntax, structural primitive-algebra witness, exact path bound, and
measured runtime are all fields of `code`.
-/
noncomputable def ofFirstOrderCode
    {M : CostModel.{uFirstOrder}} {measure : NatMeasure M}
    {Base : Type uFirstOrder} {interpret : Base → Type uFirstOrder}
    {S : CryptoLib.Program.Signature.{uFirstOrder, uFirstOrder} Base}
    {A : CryptoLib.Program.CostedAlgebra M interpret S}
    {FirstOrderInput FirstOrderOutput : CryptoLib.Program.Ty Base}
    (code : FirstOrderOperationalCode M measure interpret A
      FirstOrderInput FirstOrderOutput) :
    PPTMachine M measure
      (fun _sec => CryptoLib.Program.Ty.denote interpret FirstOrderInput)
      (fun _sec _input => CryptoLib.Program.Ty.denote interpret FirstOrderOutput) where
  toTimedMachine := code.toTimedMachine
  runtime_poly :=
    CryptoLib.Core.Infrastructure.Asymptotic.IsPolyBounded.const code.runtime
  admission := PPTAdmissible.operational
    (OperationalRealization.ofFirstOrderMachineCode code)

@[simp] theorem toTimedMachine_run
    (machine : PPTMachine M measure Input Output) :
    machine.toTimedMachine.run = machine.run :=
  rfl

@[simp] theorem toTimedMachine_runtime
    (machine : PPTMachine M measure Input Output) :
    machine.toTimedMachine.runtime = machine.runtime :=
  rfl

end PPTMachine

end CryptoLib.Core.Infrastructure.Complexity

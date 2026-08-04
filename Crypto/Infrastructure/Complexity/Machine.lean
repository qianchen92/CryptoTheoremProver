import Crypto.Infrastructure.Complexity.CostBound

namespace Crypto.Infrastructure.Complexity

open Crypto.Infrastructure.Computation
open Crypto.Infrastructure.Computation.Cost

universe uCost uIn uOut uMapped

/--
A randomized machine over one exact cost model and fully dependent I/O families.

The machine stores exactly one computation.  Cost and polynomial certificates
are attached by the refinements below without replacing that computation.
-/
structure ProbabilisticMachine
    (M : CostModel.{uCost})
    (Input : Crypto.SecPar → Type uIn)
    (Output : (sec : Crypto.SecPar) → Input sec → Type uOut) where
  run : RandomizedComputation M Input Output

namespace ProbabilisticMachine

/-- Forget exact path costs and expose the ordinary dependent output distribution. -/
noncomputable def runDist
    {M : CostModel.{uCost}}
    {Input : Crypto.SecPar → Type uIn}
    {Output : (sec : Crypto.SecPar) → Input sec → Type uOut}
    (machine : ProbabilisticMachine M Input Output)
    (sec : Crypto.SecPar) (input : Input sec) :
    PMF (Output sec input) :=
  RandomizedComputation.valueDist machine.run sec input

/-- Build a zero-cost probabilistic machine from a dependent pure function. -/
noncomputable def ofFunction
    (M : CostModel.{uCost})
    {Input : Crypto.SecPar → Type uIn}
    {Output : (sec : Crypto.SecPar) → Input sec → Type uOut}
    (function :
      (sec : Crypto.SecPar) → (input : Input sec) → Output sec input) :
    ProbabilisticMachine M Input Output where
  run := RandomizedComputation.pure M function

/-- Apply a dependent value-only map while preserving every exact path cost. -/
noncomputable def map
    {M : CostModel.{uCost}}
    {Input : Crypto.SecPar → Type uIn}
    {Output : (sec : Crypto.SecPar) → Input sec → Type uOut}
    {Mapped : (sec : Crypto.SecPar) → Input sec → Type uMapped}
    (transform :
      (sec : Crypto.SecPar) → (input : Input sec) →
        Output sec input → Mapped sec input)
    (machine : ProbabilisticMachine M Input Output) :
    ProbabilisticMachine M Input Mapped where
  run := RandomizedComputation.map transform machine.run

@[simp] theorem runDist_ofFunction
    (M : CostModel.{uCost})
    {Input : Crypto.SecPar → Type uIn}
    {Output : (sec : Crypto.SecPar) → Input sec → Type uOut}
    (function :
      (sec : Crypto.SecPar) → (input : Input sec) → Output sec input)
    (sec : Crypto.SecPar) (input : Input sec) :
    (ofFunction M function).runDist sec input =
      PMF.pure (function sec input) := by
  exact RandomizedComputation.valueDist_pure M function sec input

@[simp] theorem runDist_map
    {M : CostModel.{uCost}}
    {Input : Crypto.SecPar → Type uIn}
    {Output : (sec : Crypto.SecPar) → Input sec → Type uOut}
    {Mapped : (sec : Crypto.SecPar) → Input sec → Type uMapped}
    (transform :
      (sec : Crypto.SecPar) → (input : Input sec) →
        Output sec input → Mapped sec input)
    (machine : ProbabilisticMachine M Input Output)
    (sec : Crypto.SecPar) (input : Input sec) :
    (machine.map transform).runDist sec input =
      PMF.map (transform sec input) (machine.runDist sec input) := by
  exact RandomizedComputation.valueDist_map transform machine.run sec input

end ProbabilisticMachine

/-- A machine whose one exact computation has a measured runtime certificate. -/
structure TimedMachine
    (M : CostModel.{uCost}) (measure : NatMeasure M)
    (Input : Crypto.SecPar → Type uIn)
    (Output : (sec : Crypto.SecPar) → Input sec → Type uOut)
    extends ProbabilisticMachine M Input Output where
  certificate : RuntimeCertificate measure run

namespace TimedMachine

/-- The exact input-dependent budget certified for this machine. -/
def costBound
    {M : CostModel.{uCost}} {measure : NatMeasure M}
    {Input : Crypto.SecPar → Type uIn}
    {Output : (sec : Crypto.SecPar) → Input sec → Type uOut}
    (machine : TimedMachine M measure Input Output) :
    (sec : Crypto.SecPar) → Input sec → M.Cost :=
  machine.certificate.budget

/-- The uniform natural-number runtime obtained through the chosen measure. -/
def runtime
    {M : CostModel.{uCost}} {measure : NatMeasure M}
    {Input : Crypto.SecPar → Type uIn}
    {Output : (sec : Crypto.SecPar) → Input sec → Type uOut}
    (machine : TimedMachine M measure Input Output) : Crypto.SecPar → Nat :=
  machine.certificate.runtime

/-- Every concrete exact path respects the stored exact budget. -/
theorem cost_le_bound
    {M : CostModel.{uCost}} {measure : NatMeasure M}
    {Input : Crypto.SecPar → Type uIn}
    {Output : (sec : Crypto.SecPar) → Input sec → Type uOut}
    (machine : TimedMachine M measure Input Output)
    (sec : Crypto.SecPar) (input : Input sec)
    (result : Costed M (Output sec input))
    (hresult : result ∈ (machine.run sec input).support) :
    M.instPartialOrder.le result.cost (machine.costBound sec input) :=
  machine.certificate.cost_le_budget sec input result hresult

/-- Measuring any concrete exact path yields at most the uniform runtime. -/
theorem measuredCost_le_runtime
    {M : CostModel.{uCost}} {measure : NatMeasure M}
    {Input : Crypto.SecPar → Type uIn}
    {Output : (sec : Crypto.SecPar) → Input sec → Type uOut}
    (machine : TimedMachine M measure Input Output)
    (sec : Crypto.SecPar) (input : Input sec)
    (result : Costed M (Output sec input))
    (hresult : result ∈ (machine.run sec input).support) :
    measure result.cost ≤ machine.runtime sec :=
  machine.certificate.measuredCost_le_runtime sec input result hresult

/-- Build a zero-runtime timed machine from a dependent pure function. -/
noncomputable def ofFunction
    (M : CostModel.{uCost}) (measure : NatMeasure M)
    {Input : Crypto.SecPar → Type uIn}
    {Output : (sec : Crypto.SecPar) → Input sec → Type uOut}
    (function :
      (sec : Crypto.SecPar) → (input : Input sec) → Output sec input) :
    TimedMachine M measure Input Output where
  toProbabilisticMachine := ProbabilisticMachine.ofFunction M function
  certificate := RuntimeCertificate.pure M measure function

/-- Dependent value mapping preserves the machine's exact and measured bounds. -/
noncomputable def map
    {M : CostModel.{uCost}} {measure : NatMeasure M}
    {Input : Crypto.SecPar → Type uIn}
    {Output : (sec : Crypto.SecPar) → Input sec → Type uOut}
    {Mapped : (sec : Crypto.SecPar) → Input sec → Type uMapped}
    (transform :
      (sec : Crypto.SecPar) → (input : Input sec) →
        Output sec input → Mapped sec input)
    (machine : TimedMachine M measure Input Output) :
    TimedMachine M measure Input Mapped where
  toProbabilisticMachine := machine.toProbabilisticMachine.map transform
  certificate := machine.certificate.map transform

@[simp] theorem runtime_ofFunction
    (M : CostModel.{uCost}) (measure : NatMeasure M)
    {Input : Crypto.SecPar → Type uIn}
    {Output : (sec : Crypto.SecPar) → Input sec → Type uOut}
    (function :
      (sec : Crypto.SecPar) → (input : Input sec) → Output sec input) :
    (ofFunction M measure function).runtime = fun _sec => 0 :=
  rfl

end TimedMachine

/--
External, host-independent admission of one exact run under one claimed
runtime as genuinely PPT.

The generic cost framework deliberately provides no constructor for this
predicate.  Exact path annotations and a polynomial bound on their projection
do not, by themselves, account for Lean host reduction hidden in pure values,
higher-order continuations, or value maps.  A concrete first-order machine
model (for example a RAM, circuit, or bytecode semantics) must discharge this
obligation for these same two indices.
-/
opaque PPTAdmissible
    {M : CostModel.{uCost}}
    {Input : Crypto.SecPar → Type uIn}
    {Output : (sec : Crypto.SecPar) → Input sec → Type uOut}
    (run : RandomizedComputation M Input Output)
    (runtime : Crypto.SecPar → Nat) : Prop

/--
A polynomially bounded annotated machine that is additionally admitted by an
external host-independent PPT model.

The admission field is the firewall between internal path-cost certificates
and cryptographic quantification over PPT adversaries.  In particular, no
arbitrary Lean function is admitted merely because it can be placed in a
zero-cost `pure` computation.
-/
structure PPTMachine
    (M : CostModel.{uCost}) (measure : NatMeasure M)
    (Input : Crypto.SecPar → Type uIn)
    (Output : (sec : Crypto.SecPar) → Input sec → Type uOut)
    extends TimedMachine M measure Input Output where
  runtime_poly :
    Crypto.Infrastructure.Asymptotic.IsPolyBounded toTimedMachine.runtime
  admission : PPTAdmissible toTimedMachine.run toTimedMachine.runtime

namespace PPTMachine

/-- The exact input-dependent budget certified for this PPT machine. -/
def costBound
    {M : CostModel.{uCost}} {measure : NatMeasure M}
    {Input : Crypto.SecPar → Type uIn}
    {Output : (sec : Crypto.SecPar) → Input sec → Type uOut}
    (machine : PPTMachine M measure Input Output) :
    (sec : Crypto.SecPar) → Input sec → M.Cost :=
  machine.certificate.budget

/-- The uniform polynomial natural-number runtime. -/
def runtime
    {M : CostModel.{uCost}} {measure : NatMeasure M}
    {Input : Crypto.SecPar → Type uIn}
    {Output : (sec : Crypto.SecPar) → Input sec → Type uOut}
    (machine : PPTMachine M measure Input Output) : Crypto.SecPar → Nat :=
  machine.certificate.runtime

/-- The stored runtime is polynomially bounded. -/
theorem runtime_isPoly
    {M : CostModel.{uCost}} {measure : NatMeasure M}
    {Input : Crypto.SecPar → Type uIn}
    {Output : (sec : Crypto.SecPar) → Input sec → Type uOut}
    (machine : PPTMachine M measure Input Output) :
    Crypto.Infrastructure.Asymptotic.IsPolyBounded machine.runtime :=
  machine.runtime_poly

/--
Promote an annotated timed machine only after an external operational model has
admitted that exact machine.  Polynomiality of the measured bound and PPT
admission are intentionally separate obligations.
-/
def ofAdmittedTimedMachine
    {M : CostModel.{uCost}} {measure : NatMeasure M}
    {Input : Crypto.SecPar → Type uIn}
    {Output : (sec : Crypto.SecPar) → Input sec → Type uOut}
    (machine : TimedMachine M measure Input Output)
    (runtime_isPoly :
      Crypto.Infrastructure.Asymptotic.IsPolyBounded machine.runtime)
    (admission : PPTAdmissible machine.run machine.runtime) :
    PPTMachine M measure Input Output where
  toTimedMachine := machine
  runtime_poly := runtime_isPoly
  admission := admission

@[simp] theorem toTimedMachine_run
    {M : CostModel.{uCost}} {measure : NatMeasure M}
    {Input : Crypto.SecPar → Type uIn}
    {Output : (sec : Crypto.SecPar) → Input sec → Type uOut}
    (machine : PPTMachine M measure Input Output) :
    machine.toTimedMachine.run = machine.run :=
  rfl

@[simp] theorem toTimedMachine_runtime
    {M : CostModel.{uCost}} {measure : NatMeasure M}
    {Input : Crypto.SecPar → Type uIn}
    {Output : (sec : Crypto.SecPar) → Input sec → Type uOut}
    (machine : PPTMachine M measure Input Output) :
    machine.toTimedMachine.runtime = machine.runtime :=
  rfl

end PPTMachine

end Crypto.Infrastructure.Complexity

import Crypto.Infrastructure.Complexity.Machine
import Crypto.Infrastructure.Computation.Program

namespace Crypto.Infrastructure.Complexity

open Crypto.Infrastructure.Asymptotic
open Crypto.Infrastructure.Computation
open Crypto.Infrastructure.Computation.Algebra

universe uIn uOut uScalar uCarrier uSample

namespace TimedMachine

/--
Build a timed machine from a family of statically bounded programs.

The supplied runtime function is statically tied to the budget index carried by
each program, whose soundness is established compositionally from
primitive-operation and sampler bounds.  This constructor validates that
shared index; it does not synthesize a closed-form security-parameter bound.
-/
noncomputable def ofBoundedProgram
    {Input : Type uIn}
    {Scalar : Type uScalar} {Carrier : Type uCarrier} {Sample : Type uSample}
    {Output : Type (max uScalar (max uCarrier uSample))}
    [AddGroup Carrier] [SMul Scalar Carrier]
    [Fintype Sample] [Nonempty Sample]
    (backend : AdditiveBackend Scalar Carrier)
    (sampler : UniformSampler Sample)
    (runtime : Crypto.SecPar → Nat)
    (program :
      (sec : Crypto.SecPar) →
      Input →
        Program.BoundedProgram
          (backend := backend) (sampler := sampler)
          (runtime sec) Output) :
    TimedMachine Input Output where
  run := fun sec input =>
    Program.runCosted (program sec input).program
  runtime := runtime
  runtime_sound := by
    intro sec input result hresult
    exact (program sec input).sound result hresult

/--
Build a timed machine by applying a cost-preserving output map to a family of
statically bounded programs.

This constructor is useful when a program's result carries an internal
universe lift or another representation that should not appear in the machine
interface.
-/
noncomputable def ofMappedBoundedProgram
    {Input : Type uIn} {Output : Type uOut}
    {Scalar : Type uScalar} {Carrier : Type uCarrier} {Sample : Type uSample}
    {ProgramOutput : Type (max uScalar (max uCarrier uSample))}
    [AddGroup Carrier] [SMul Scalar Carrier]
    [Fintype Sample] [Nonempty Sample]
    (backend : AdditiveBackend Scalar Carrier)
    (sampler : UniformSampler Sample)
    (runtime : Crypto.SecPar → Nat)
    (mapOutput : ProgramOutput → Output)
    (program :
      (sec : Crypto.SecPar) →
      Input →
        Program.BoundedProgram
          (backend := backend) (sampler := sampler)
          (runtime sec) ProgramOutput) :
    TimedMachine Input Output where
  run := fun sec input =>
    Crypto.Infrastructure.Computation.Cost.RandCosted.map mapOutput
      (Program.runCosted (program sec input).program)
  runtime := runtime
  runtime_sound := by
    intro sec input result hresult
    simp only [Crypto.Infrastructure.Computation.Cost.RandCosted.map] at hresult
    rw [PMF.mem_support_map_iff] at hresult
    rcases hresult with ⟨programResult, hprogramResult, hresult⟩
    subst result
    exact (program sec input).sound programResult hprogramResult

/--
Build a timed machine from carrier-valued programs while erasing the internal
`ULift` used to accommodate independent scalar, carrier, and sampler universes.
-/
noncomputable def ofBoundedCarrierProgram
    {Input : Type uIn}
    {Scalar : Type uScalar} {Carrier : Type uCarrier} {Sample : Type uSample}
    [AddGroup Carrier] [SMul Scalar Carrier]
    [Fintype Sample] [Nonempty Sample]
    (backend : AdditiveBackend Scalar Carrier)
    (sampler : UniformSampler Sample)
    (runtime : Crypto.SecPar → Nat)
    (program :
      (sec : Crypto.SecPar) →
      Input →
        Program.BoundedProgram
          (backend := backend) (sampler := sampler)
          (runtime sec) (ULift.{max uScalar uSample} Carrier)) :
    TimedMachine Input Carrier :=
  ofMappedBoundedProgram backend sampler runtime ULift.down program

end TimedMachine

namespace PPTMachine

/--
Build a PPT machine from compositionally bounded programs and a polynomial
bound on their shared budget function.
-/
noncomputable def ofBoundedProgram
    {Input : Type uIn}
    {Scalar : Type uScalar} {Carrier : Type uCarrier} {Sample : Type uSample}
    {Output : Type (max uScalar (max uCarrier uSample))}
    [AddGroup Carrier] [SMul Scalar Carrier]
    [Fintype Sample] [Nonempty Sample]
    (backend : AdditiveBackend Scalar Carrier)
    (sampler : UniformSampler Sample)
    (runtime : Crypto.SecPar → Nat)
    (program :
      (sec : Crypto.SecPar) →
      Input →
        Program.BoundedProgram
          (backend := backend) (sampler := sampler)
          (runtime sec) Output)
    (runtime_isPoly : IsPolyBounded runtime) :
    PPTMachine Input Output :=
  { TimedMachine.ofBoundedProgram backend sampler runtime program with
    runtime_isPoly := runtime_isPoly }

/--
Build a PPT machine by applying a cost-preserving output map to a family of
compositionally bounded programs.
-/
noncomputable def ofMappedBoundedProgram
    {Input : Type uIn} {Output : Type uOut}
    {Scalar : Type uScalar} {Carrier : Type uCarrier} {Sample : Type uSample}
    {ProgramOutput : Type (max uScalar (max uCarrier uSample))}
    [AddGroup Carrier] [SMul Scalar Carrier]
    [Fintype Sample] [Nonempty Sample]
    (backend : AdditiveBackend Scalar Carrier)
    (sampler : UniformSampler Sample)
    (runtime : Crypto.SecPar → Nat)
    (mapOutput : ProgramOutput → Output)
    (program :
      (sec : Crypto.SecPar) →
      Input →
        Program.BoundedProgram
          (backend := backend) (sampler := sampler)
          (runtime sec) ProgramOutput)
    (runtime_isPoly : IsPolyBounded runtime) :
    PPTMachine Input Output :=
  { TimedMachine.ofMappedBoundedProgram
      backend sampler runtime mapOutput program with
    runtime_isPoly := runtime_isPoly }

/-- Carrier-valued specialization of `ofBoundedProgram` with `ULift` erased. -/
noncomputable def ofBoundedCarrierProgram
    {Input : Type uIn}
    {Scalar : Type uScalar} {Carrier : Type uCarrier} {Sample : Type uSample}
    [AddGroup Carrier] [SMul Scalar Carrier]
    [Fintype Sample] [Nonempty Sample]
    (backend : AdditiveBackend Scalar Carrier)
    (sampler : UniformSampler Sample)
    (runtime : Crypto.SecPar → Nat)
    (program :
      (sec : Crypto.SecPar) →
      Input →
        Program.BoundedProgram
          (backend := backend) (sampler := sampler)
          (runtime sec) (ULift.{max uScalar uSample} Carrier))
    (runtime_isPoly : IsPolyBounded runtime) :
    PPTMachine Input Carrier :=
  ofMappedBoundedProgram
    backend sampler runtime ULift.down program runtime_isPoly

end PPTMachine

end Crypto.Infrastructure.Complexity

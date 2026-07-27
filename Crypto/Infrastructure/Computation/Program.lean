import Crypto.Infrastructure.Computation.Algebra.Backend
import Crypto.Infrastructure.Computation.Cost.Distribution
import Mathlib.Probability.ProbabilityMassFunction.Monad

namespace Crypto.Infrastructure.Computation

open Crypto.Infrastructure.Computation.Algebra
open Crypto.Infrastructure.Computation.Cost

universe uScalar uCarrier uSample

/--
A typed program whose computational algebra and scalar sampler are explicit.

This is the engineering-level, higher-order representation: algebraic work and
sampling are syntax constructors, while `pure`, continuations, and branch
conditions are still Lean-level values.  A first-order language can later
replace those three host-language boundaries without changing the interpreters'
resource interface.
-/
inductive Program
    (Scalar : Type uScalar) (Carrier : Type uCarrier) (Sample : Type uSample)
    [AddGroup Carrier] [SMul Scalar Carrier]
    [Fintype Sample] [Nonempty Sample]
    (backend : AdditiveBackend Scalar Carrier)
    (sampler : UniformSampler Sample) :
    Type (max uScalar (max uCarrier uSample)) →
      Type (max uScalar (max uCarrier uSample) + 1) where
  | pure {α : Type (max uScalar (max uCarrier uSample))} :
      α → Program Scalar Carrier Sample backend sampler α
  | bind
      {α β : Type (max uScalar (max uCarrier uSample))} :
      Program Scalar Carrier Sample backend sampler α →
      (α → Program Scalar Carrier Sample backend sampler β) →
      Program Scalar Carrier Sample backend sampler β
  | add :
      Carrier → Carrier →
        Program Scalar Carrier Sample backend sampler
          (ULift.{max uScalar uSample} Carrier)
  | neg :
      Carrier →
        Program Scalar Carrier Sample backend sampler
          (ULift.{max uScalar uSample} Carrier)
  | sub :
      Carrier → Carrier →
        Program Scalar Carrier Sample backend sampler
          (ULift.{max uScalar uSample} Carrier)
  | smul :
      Scalar → Carrier →
        Program Scalar Carrier Sample backend sampler
          (ULift.{max uScalar uSample} Carrier)
  | sample :
      Program Scalar Carrier Sample backend sampler
        (ULift.{max uScalar uCarrier} Sample)
  | branch
      {α : Type (max uScalar (max uCarrier uSample))} :
      Bool →
      Program Scalar Carrier Sample backend sampler α →
      Program Scalar Carrier Sample backend sampler α →
      Program Scalar Carrier Sample backend sampler α

namespace Program

variable
    {Scalar : Type uScalar} {Carrier : Type uCarrier} {Sample : Type uSample}
    [AddGroup Carrier] [SMul Scalar Carrier]
    [Fintype Sample] [Nonempty Sample]
    {backend : AdditiveBackend Scalar Carrier}
    {sampler : UniformSampler Sample}

/--
Costed semantics of a typed program.

Only primitive constructors introduce local cost.  Sequential composition uses
the writer bind of `RandCosted`, so path costs are accumulated exactly once.
-/
noncomputable def runCosted
    {α : Type (max uScalar (max uCarrier uSample))}
    (program : Program Scalar Carrier Sample backend sampler α) :
    RandCosted α :=
  match program with
  | .pure value =>
      RandCosted.pure value
  | .bind first next =>
      RandCosted.bind (runCosted first) fun value =>
        runCosted (next value)
  | .add left right =>
      RandCosted.liftCosted
        (Costed.map ULift.up (backend.add left right))
  | .neg value =>
      RandCosted.liftCosted
        (Costed.map ULift.up (backend.neg value))
  | .sub left right =>
      RandCosted.liftCosted
        (Costed.map ULift.up (backend.sub left right))
  | .smul scalar value =>
      RandCosted.liftCosted
        (Costed.map ULift.up (backend.smul scalar value))
  | .sample =>
      RandCosted.map ULift.up sampler.sample
  | .branch condition thenProgram elseProgram =>
      if condition then runCosted thenProgram else runCosted elseProgram

/-- Ordinary value semantics, obtained solely by erasing path costs. -/
noncomputable def valueDist
    {α : Type (max uScalar (max uCarrier uSample))}
    (program : Program Scalar Carrier Sample backend sampler α) :
    PMF α :=
  RandCosted.valueDist (runCosted program)

@[simp] theorem valueDist_pure
    {α : Type (max uScalar (max uCarrier uSample))}
    (value : α) :
    valueDist
      (backend := backend) (sampler := sampler)
      (Program.pure value) = PMF.pure value := by
  simp [valueDist, runCosted]

@[simp] theorem valueDist_bind
    {α β : Type (max uScalar (max uCarrier uSample))}
    (first : Program Scalar Carrier Sample backend sampler α)
    (next : α → Program Scalar Carrier Sample backend sampler β) :
    valueDist (.bind first next) =
      PMF.bind (valueDist first) fun value => valueDist (next value) := by
  simp [valueDist, runCosted]

@[simp] theorem valueDist_add (left right : Carrier) :
    valueDist
      (Program.add (backend := backend) (sampler := sampler) left right) =
        PMF.pure (ULift.up (left + right)) := by
  simp [valueDist, runCosted]

@[simp] theorem valueDist_neg (value : Carrier) :
    valueDist
      (Program.neg (backend := backend) (sampler := sampler) value) =
        PMF.pure (ULift.up (-value)) := by
  simp [valueDist, runCosted]

@[simp] theorem valueDist_sub (left right : Carrier) :
    valueDist
      (Program.sub (backend := backend) (sampler := sampler) left right) =
        PMF.pure (ULift.up (left - right)) := by
  simp [valueDist, runCosted]

@[simp] theorem valueDist_smul (scalar : Scalar) (value : Carrier) :
    valueDist
      (Program.smul (backend := backend) (sampler := sampler) scalar value) =
        PMF.pure (ULift.up (scalar • value)) := by
  simp [valueDist, runCosted]

@[simp] theorem valueDist_sample :
    valueDist (Program.sample (backend := backend) (sampler := sampler)) =
      PMF.map ULift.up (Distribution.uniformPMF Sample) := by
  simp [valueDist, runCosted]

@[simp] theorem valueDist_branch
    {α : Type (max uScalar (max uCarrier uSample))}
    (condition : Bool)
    (thenProgram elseProgram : Program Scalar Carrier Sample backend sampler α) :
    valueDist (.branch condition thenProgram elseProgram) =
      if condition then valueDist thenProgram else valueDist elseProgram := by
  cases condition <;> simp [valueDist, runCosted]

/-- Bind a carrier-producing program without exposing the `ULift` plumbing. -/
def bindCarrier
    {α : Type (max uScalar (max uCarrier uSample))}
    (first :
      Program Scalar Carrier Sample backend sampler
        (ULift.{max uScalar uSample} Carrier))
    (next : Carrier → Program Scalar Carrier Sample backend sampler α) :
    Program Scalar Carrier Sample backend sampler α :=
  .bind first fun value => next value.down

/-- Bind a sampler-producing program without exposing the `ULift` plumbing. -/
def bindSample
    {α : Type (max uScalar (max uCarrier uSample))}
    (first :
      Program Scalar Carrier Sample backend sampler
        (ULift.{max uScalar uCarrier} Sample))
    (next : Sample → Program Scalar Carrier Sample backend sampler α) :
    Program Scalar Carrier Sample backend sampler α :=
  .bind first fun value => next value.down

/-- Ordinary carrier-valued semantics with the common-universe lift erased. -/
noncomputable def carrierValueDist
    (program :
      Program Scalar Carrier Sample backend sampler
        (ULift.{max uScalar uSample} Carrier)) :
    PMF Carrier :=
  PMF.map ULift.down (valueDist program)

/-- Costed carrier-valued semantics with the common-universe lift erased. -/
noncomputable def runCostedCarrier
    (program :
      Program Scalar Carrier Sample backend sampler
        (ULift.{max uScalar uSample} Carrier)) :
    RandCosted Carrier :=
  RandCosted.map ULift.down (runCosted program)

/-- Ordinary sampler-valued semantics with the common-universe lift erased. -/
noncomputable def sampleValueDist
    (program :
      Program Scalar Carrier Sample backend sampler
        (ULift.{max uScalar uCarrier} Sample)) :
    PMF Sample :=
  PMF.map ULift.down (valueDist program)

/-- Costed sampler-valued semantics with the common-universe lift erased. -/
noncomputable def runCostedSample
    (program :
      Program Scalar Carrier Sample backend sampler
        (ULift.{max uScalar uCarrier} Sample)) :
    RandCosted Sample :=
  RandCosted.map ULift.down (runCosted program)

/-- Forgetting costs from the costed interpreter recovers the ordinary semantics. -/
theorem valueDist_runCosted
    {α : Type (max uScalar (max uCarrier uSample))}
    (program : Program Scalar Carrier Sample backend sampler α) :
    RandCosted.valueDist (runCosted program) = valueDist program :=
  rfl

/-- Erasing costs after carrier lowering recovers the lowered value semantics. -/
@[simp] theorem valueDist_runCostedCarrier
    (program :
      Program Scalar Carrier Sample backend sampler
        (ULift.{max uScalar uSample} Carrier)) :
    RandCosted.valueDist (runCostedCarrier program) = carrierValueDist program := by
  simp [runCostedCarrier, carrierValueDist, valueDist]

/-- Erasing costs after sample lowering recovers the lowered value semantics. -/
@[simp] theorem valueDist_runCostedSample
    (program :
      Program Scalar Carrier Sample backend sampler
        (ULift.{max uScalar uCarrier} Sample)) :
    RandCosted.valueDist (runCostedSample program) = sampleValueDist program := by
  simp [runCostedSample, sampleValueDist, valueDist]

/-- A structural execution path and its exact accumulated cost. -/
inductive Execution :
    {α : Type (max uScalar (max uCarrier uSample))} →
    Program Scalar Carrier Sample backend sampler α →
    α → Cost → Prop where
  | pure
      {α : Type (max uScalar (max uCarrier uSample))}
      (value : α) :
      Execution (.pure value) value 0
  | bind
      {α β : Type (max uScalar (max uCarrier uSample))}
      {first : Program Scalar Carrier Sample backend sampler α}
      {next : α → Program Scalar Carrier Sample backend sampler β}
      {firstValue : α} {value : β}
      {firstCost nextCost : Cost}
      (firstExecution : Execution first firstValue firstCost)
      (nextExecution : Execution (next firstValue) value nextCost) :
      Execution (.bind first next) value (firstCost + nextCost)
  | add (left right : Carrier) :
      Execution (.add left right)
        (ULift.up (backend.add left right).val) (backend.add left right).cost
  | neg (value : Carrier) :
      Execution (.neg value)
        (ULift.up (backend.neg value).val) (backend.neg value).cost
  | sub (left right : Carrier) :
      Execution (.sub left right)
        (ULift.up (backend.sub left right).val) (backend.sub left right).cost
  | smul (scalar : Scalar) (value : Carrier) :
      Execution (.smul scalar value)
        (ULift.up (backend.smul scalar value).val) (backend.smul scalar value).cost
  | sample
      (result : Costed Sample)
      (result_mem : result ∈ sampler.sample.support) :
      Execution .sample (ULift.up result.val) result.cost
  | branchTrue
      {α : Type (max uScalar (max uCarrier uSample))}
      {thenProgram elseProgram : Program Scalar Carrier Sample backend sampler α}
      {value : α} {cost : Cost}
      (execution : Execution thenProgram value cost) :
      Execution (.branch true thenProgram elseProgram) value cost
  | branchFalse
      {α : Type (max uScalar (max uCarrier uSample))}
      {thenProgram elseProgram : Program Scalar Carrier Sample backend sampler α}
      {value : α} {cost : Cost}
      (execution : Execution elseProgram value cost) :
      Execution (.branch false thenProgram elseProgram) value cost

/--
Every result produced by the costed interpreter follows a structural execution
path carrying exactly the recorded cost.
-/
theorem execution_of_mem_support_runCosted
    {α : Type (max uScalar (max uCarrier uSample))}
    (program : Program Scalar Carrier Sample backend sampler α)
    (result : Costed α)
    (hresult : result ∈ (runCosted program).support) :
    Execution program result.val result.cost := by
  induction program with
  | pure value =>
      simp only [runCosted, RandCosted.pure, RandCosted.liftCosted, Costed.pure] at hresult
      rw [PMF.mem_support_pure_iff] at hresult
      subst result
      exact Execution.pure value
  | bind first next ihFirst ihNext =>
      simp only [runCosted, RandCosted.bind] at hresult
      rw [PMF.mem_support_bind_iff] at hresult
      rcases hresult with ⟨firstResult, hfirstResult, hnextResult⟩
      rw [PMF.mem_support_map_iff] at hnextResult
      rcases hnextResult with ⟨nextResult, hnextResult, hresult⟩
      subst result
      exact Execution.bind
        (ihFirst firstResult hfirstResult)
        (ihNext firstResult.val nextResult hnextResult)
  | add left right =>
      simp only [runCosted, RandCosted.liftCosted] at hresult
      rw [PMF.mem_support_pure_iff] at hresult
      subst result
      exact Execution.add left right
  | neg value =>
      simp only [runCosted, RandCosted.liftCosted] at hresult
      rw [PMF.mem_support_pure_iff] at hresult
      subst result
      exact Execution.neg value
  | sub left right =>
      simp only [runCosted, RandCosted.liftCosted] at hresult
      rw [PMF.mem_support_pure_iff] at hresult
      subst result
      exact Execution.sub left right
  | smul scalar value =>
      simp only [runCosted, RandCosted.liftCosted] at hresult
      rw [PMF.mem_support_pure_iff] at hresult
      subst result
      exact Execution.smul scalar value
  | sample =>
      simp only [runCosted, RandCosted.map] at hresult
      rw [PMF.mem_support_map_iff] at hresult
      rcases hresult with ⟨sampledResult, hsampledResult, hresult⟩
      subst result
      exact Execution.sample sampledResult hsampledResult
  | branch condition thenProgram elseProgram ihThen ihElse =>
      cases condition with
      | false =>
          simp only [runCosted] at hresult
          exact Execution.branchFalse (ihElse result hresult)
      | true =>
          simp only [runCosted, if_true] at hresult
          exact Execution.branchTrue (ihThen result hresult)

/-- Every interpreter path is bounded by `budget`. -/
def CostBound
    {α : Type (max uScalar (max uCarrier uSample))}
    (program : Program Scalar Carrier Sample backend sampler α)
    (budget : Cost) : Prop :=
  ∀ result, result ∈ (runCosted program).support → result.cost ≤ budget

/-- A typed program paired with a statically verified uniform path budget. -/
structure BoundedProgram
    (budget : Cost)
    (α : Type (max uScalar (max uCarrier uSample))) where
  program : Program Scalar Carrier Sample backend sampler α
  sound : CostBound program budget

namespace BoundedProgram

variable
    {firstBudget nextBudget budget largerBudget : Cost}
    {α β : Type (max uScalar (max uCarrier uSample))}

/-- A returned value has zero program cost. -/
def pure (value : α) :
    BoundedProgram (backend := backend) (sampler := sampler) 0 α where
  program := .pure value
  sound := by
    intro result hresult
    simp only [runCosted, RandCosted.pure, RandCosted.liftCosted, Costed.pure] at hresult
    rw [PMF.mem_support_pure_iff] at hresult
    subst result
    exact Nat.le_refl 0

/-- Sequential composition adds the two verified budgets. -/
def bind
    (first :
      BoundedProgram (backend := backend) (sampler := sampler) firstBudget α)
    (next :
      α →
        BoundedProgram (backend := backend) (sampler := sampler) nextBudget β) :
    BoundedProgram
      (backend := backend) (sampler := sampler)
      (firstBudget + nextBudget) β where
  program := .bind first.program fun value => (next value).program
  sound := by
    intro result hresult
    simp only [runCosted, RandCosted.bind] at hresult
    rw [PMF.mem_support_bind_iff] at hresult
    rcases hresult with ⟨firstResult, hfirstResult, hnextResult⟩
    rw [PMF.mem_support_map_iff] at hnextResult
    rcases hnextResult with ⟨nextResult, hnextResult, hresult⟩
    subst result
    exact Nat.add_le_add
      (first.sound firstResult hfirstResult)
      ((next firstResult.val).sound nextResult hnextResult)

/-- Sequentially bind a carrier result without exposing its `ULift`. -/
def bindCarrier
    (first :
      BoundedProgram
        (backend := backend) (sampler := sampler)
        firstBudget (ULift.{max uScalar uSample} Carrier))
    (next :
      Carrier →
        BoundedProgram (backend := backend) (sampler := sampler) nextBudget α) :
    BoundedProgram
      (backend := backend) (sampler := sampler)
      (firstBudget + nextBudget) α :=
  bind first fun value => next value.down

/-- Sequentially bind a sampled result without exposing its `ULift`. -/
def bindSample
    (first :
      BoundedProgram
        (backend := backend) (sampler := sampler)
        firstBudget (ULift.{max uScalar uCarrier} Sample))
    (next :
      Sample →
        BoundedProgram (backend := backend) (sampler := sampler) nextBudget α) :
    BoundedProgram
      (backend := backend) (sampler := sampler)
      (firstBudget + nextBudget) α :=
  bind first fun value => next value.down

/-- Widen a verified program budget. -/
def weaken
    (program :
      BoundedProgram (backend := backend) (sampler := sampler) budget α)
    (budget_le : budget ≤ largerBudget) :
    BoundedProgram (backend := backend) (sampler := sampler) largerBudget α where
  program := program.program
  sound := by
    intro result hresult
    exact le_trans (program.sound result hresult) budget_le

/-- Addition is bounded by the backend's uniform addition budget. -/
def add
    (bounds : AdditiveCostBounds backend)
    (left right : Carrier) :
    BoundedProgram
      (backend := backend) (sampler := sampler)
      bounds.addBudget (ULift.{max uScalar uSample} Carrier) where
  program := .add left right
  sound := by
    intro result hresult
    simp only [runCosted, RandCosted.liftCosted] at hresult
    rw [PMF.mem_support_pure_iff] at hresult
    subst result
    exact bounds.addCost_le left right

/-- Negation is bounded by the backend's uniform negation budget. -/
def neg
    (bounds : AdditiveCostBounds backend)
    (value : Carrier) :
    BoundedProgram
      (backend := backend) (sampler := sampler)
      bounds.negBudget (ULift.{max uScalar uSample} Carrier) where
  program := .neg value
  sound := by
    intro result hresult
    simp only [runCosted, RandCosted.liftCosted] at hresult
    rw [PMF.mem_support_pure_iff] at hresult
    subst result
    exact bounds.negCost_le value

/-- Subtraction is bounded by the backend's uniform subtraction budget. -/
def sub
    (bounds : AdditiveCostBounds backend)
    (left right : Carrier) :
    BoundedProgram
      (backend := backend) (sampler := sampler)
      bounds.subBudget (ULift.{max uScalar uSample} Carrier) where
  program := .sub left right
  sound := by
    intro result hresult
    simp only [runCosted, RandCosted.liftCosted] at hresult
    rw [PMF.mem_support_pure_iff] at hresult
    subst result
    exact bounds.subCost_le left right

/-- Scalar multiplication is bounded by the backend's uniform scalar-multiplication budget. -/
def smul
    (bounds : AdditiveCostBounds backend)
    (scalar : Scalar) (value : Carrier) :
    BoundedProgram
      (backend := backend) (sampler := sampler)
      bounds.smulBudget (ULift.{max uScalar uSample} Carrier) where
  program := .smul scalar value
  sound := by
    intro result hresult
    simp only [runCosted, RandCosted.liftCosted] at hresult
    rw [PMF.mem_support_pure_iff] at hresult
    subst result
    exact bounds.smulCost_le scalar value

/-- Uniform sampling is bounded by the sampler's declared uniform budget. -/
def sample :
    BoundedProgram
      (backend := backend) (sampler := sampler)
      sampler.sampleBudget (ULift.{max uScalar uCarrier} Sample) where
  program := .sample
  sound := by
    intro result hresult
    simp only [runCosted, RandCosted.map] at hresult
    rw [PMF.mem_support_map_iff] at hresult
    rcases hresult with ⟨sampledResult, hsampledResult, hresult⟩
    subst result
    exact sampler.cost_le sampledResult hsampledResult

/-- A conditional program uses the maximum of its two branch budgets. -/
def branch
    (condition : Bool)
    (thenProgram :
      BoundedProgram (backend := backend) (sampler := sampler) firstBudget α)
    (elseProgram :
      BoundedProgram (backend := backend) (sampler := sampler) nextBudget α) :
    BoundedProgram
      (backend := backend) (sampler := sampler)
      (max firstBudget nextBudget) α where
  program := .branch condition thenProgram.program elseProgram.program
  sound := by
    intro result hresult
    cases condition with
    | false =>
        simp only [runCosted] at hresult
        exact le_trans
          (elseProgram.sound result hresult)
          (Nat.le_max_right firstBudget nextBudget)
    | true =>
        simp only [runCosted, if_true] at hresult
        exact le_trans
          (thenProgram.sound result hresult)
          (Nat.le_max_left firstBudget nextBudget)

/-- Interpreter results of a bounded program respect its static budget. -/
theorem cost_le_budget_of_mem_support
    (program :
      BoundedProgram (backend := backend) (sampler := sampler) budget α)
    (result : Costed α)
    (hresult : result ∈ (runCosted program.program).support) :
    result.cost ≤ budget :=
  program.sound result hresult

end BoundedProgram

end Program

end Crypto.Infrastructure.Computation

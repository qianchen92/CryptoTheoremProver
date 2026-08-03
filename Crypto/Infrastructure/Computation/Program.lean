import Crypto.Infrastructure.Computation.Algebra.Signature
import Mathlib.Probability.ProbabilityMassFunction.Monad

namespace Crypto.Infrastructure.Computation

open Crypto.Infrastructure.Computation.Algebra
open Crypto.Infrastructure.Computation.Cost

universe uCost uResult uOp uIn

namespace Program

/-- Reified program code after the external input has been supplied. -/
inductive Code
    {M : CostModel.{uCost}}
    {S : Signature.{uResult, uOp}}
    (A : CostedAlgebra M S) :
    Type uResult → Type (max uResult uOp + 1) where
  | pure {Result : Type uResult} : Result → Code A Result
  | bind {First Result : Type uResult} :
      Code A First → (First → Code A Result) → Code A Result
  | call {Result : Type uResult} : S.Op Result → Code A Result
  | branch {Result : Type uResult} :
      Bool → Code A Result → Code A Result → Code A Result

end Program

/--
A typed, higher-order program over one explicit cost-aware primitive algebra.

`Input` is represented at the outer boundary; the reified body contains only
pure values, sequencing, primitive calls, and conditionals.  Primitive calls
are heterogeneous because their signature is indexed by the result type.
-/
structure Program
    {M : CostModel.{uCost}}
    {S : Signature.{uResult, uOp}}
    (A : CostedAlgebra M S)
    (Input : Type uIn) (Output : Type uResult) where
  body : Input → Program.Code A Output

namespace Program

namespace Code

variable
    {M : CostModel.{uCost}}
    {S : Signature.{uResult, uOp}}
    {A : CostedAlgebra M S}

instance : Monad (Code A) where
  pure := Code.pure
  bind := Code.bind

/-- Execute code using the algebra's sole exact primitive handler. -/
noncomputable def runCosted
    {Result : Type uResult} (code : Code A Result) : RandCostedT M Result :=
  match code with
  | .pure value => RandCostedT.pure M value
  | .bind first next =>
      RandCostedT.bind (runCosted first) fun value => runCosted (next value)
  | .call operation => A.exec operation
  | .branch condition thenCode elseCode =>
      if condition then runCosted thenCode else runCosted elseCode

/-- Ordinary semantics is obtained only by erasing exact path costs. -/
noncomputable def valueDist
    {Result : Type uResult} (code : Code A Result) : PMF Result :=
  RandCostedT.valueDist (runCosted code)

@[simp] theorem valueDist_pure
    {Result : Type uResult} (value : Result) :
    valueDist (A := A) (.pure value) = PMF.pure value := by
  simp [valueDist, runCosted]

@[simp] theorem valueDist_bind
    {First Result : Type uResult}
    (first : Code A First) (next : First → Code A Result) :
    valueDist (.bind first next) =
      PMF.bind (valueDist first) fun value => valueDist (next value) := by
  simp [valueDist, runCosted]

@[simp] theorem valueDist_call
    {Result : Type uResult} (operation : S.Op Result) :
    valueDist (A := A) (.call operation) =
      RandCostedT.valueDist (A.exec operation) :=
  rfl

@[simp] theorem valueDist_branch
    {Result : Type uResult} (condition : Bool)
    (thenCode elseCode : Code A Result) :
    valueDist (.branch condition thenCode elseCode) =
      if condition then valueDist thenCode else valueDist elseCode := by
  cases condition <;> simp [valueDist, runCosted]

/-- A primitive call satisfies the mathematical specification in `laws`. -/
@[simp] theorem valueDist_call_eq
    (laws : AlgebraLaws A)
    {Result : Type uResult} (operation : S.Op Result) :
    valueDist (A := A) (.call operation) = laws.semantics operation :=
  laws.exec_spec operation

/-- A structural execution path and its exact accumulated resource cost. -/
inductive Execution :
    {Result : Type uResult} → Code A Result → Result → M.Cost → Prop where
  | pure {Result : Type uResult} (value : Result) :
      Execution (.pure value) value M.instAddMonoid.zero
  | bind
      {First Result : Type uResult}
      {first : Code A First} {next : First → Code A Result}
      {firstValue : First} {value : Result}
      {firstCost nextCost : M.Cost}
      (firstExecution : Execution first firstValue firstCost)
      (nextExecution : Execution (next firstValue) value nextCost) :
      Execution (.bind first next) value
        (M.instAddMonoid.add firstCost nextCost)
  | call
      {Result : Type uResult} (operation : S.Op Result)
      (result : CostedT M Result)
      (result_mem : result ∈ (A.exec operation).support) :
      Execution (.call operation) result.val result.cost
  | branchTrue
      {Result : Type uResult} {thenCode elseCode : Code A Result}
      {value : Result} {cost : M.Cost}
      (execution : Execution thenCode value cost) :
      Execution (.branch true thenCode elseCode) value cost
  | branchFalse
      {Result : Type uResult} {thenCode elseCode : Code A Result}
      {value : Result} {cost : M.Cost}
      (execution : Execution elseCode value cost) :
      Execution (.branch false thenCode elseCode) value cost

/-- Every interpreter result has a structural execution with the same cost. -/
theorem execution_of_mem_support_runCosted
    {Result : Type uResult} (code : Code A Result)
    (result : CostedT M Result)
    (hresult : result ∈ (runCosted code).support) :
    Execution code result.val result.cost := by
  induction code with
  | pure value =>
      simp only [runCosted, RandCostedT.pure, RandCostedT.liftCosted,
        CostedT.pure] at hresult
      rw [PMF.mem_support_pure_iff] at hresult
      subst result
      exact Execution.pure value
  | bind first next ihFirst ihNext =>
      simp only [runCosted, RandCostedT.bind] at hresult
      rw [PMF.mem_support_bind_iff] at hresult
      rcases hresult with ⟨firstResult, hfirstResult, hnextResult⟩
      rw [PMF.mem_support_map_iff] at hnextResult
      rcases hnextResult with ⟨nextResult, hnextResult, hresult⟩
      subst result
      exact Execution.bind
        (ihFirst firstResult hfirstResult)
        (ihNext firstResult.val nextResult hnextResult)
  | call operation =>
      exact Execution.call operation result hresult
  | branch condition thenCode elseCode ihThen ihElse =>
      cases condition with
      | false =>
          simp only [runCosted] at hresult
          exact Execution.branchFalse (ihElse result hresult)
      | true =>
          simp only [runCosted, if_true] at hresult
          exact Execution.branchTrue (ihThen result hresult)

/-- Every interpreter path of `code` is bounded by `budget`. -/
def CostBound
    {Result : Type uResult} (code : Code A Result) (budget : M.Cost) : Prop :=
  ∀ result, result ∈ (runCosted code).support →
    M.instPartialOrder.le result.cost budget

/--
An upper-bound certificate over an existing program body.

The program is an index, not a field, so a certificate cannot contain or
interpret a second copy of the algorithm.  The constructors below build these
proofs compositionally.
-/
structure Bound (bounds : OperationBounds A)
    {Result : Type uResult} (code : Code A Result) (budget : M.Cost) : Prop where
  sound : CostBound code budget

namespace Bound

/-- Pure code has zero cost. -/
def pure
    {bounds : OperationBounds A}
    {Result : Type uResult} (value : Result) :
    Bound bounds (.pure value) M.instAddMonoid.zero where
  sound := by
    letI := M.instPartialOrder
    intro result hresult
    simp only [runCosted, RandCostedT.pure, RandCostedT.liftCosted,
      CostedT.pure] at hresult
    rw [PMF.mem_support_pure_iff] at hresult
    subst result
    exact le_refl _

/-- A primitive call uses its independently supplied operation bound. -/
def call
    {bounds : OperationBounds A}
    {Result : Type uResult} (operation : S.Op Result) :
    Bound bounds (.call operation) (bounds.budget operation) where
  sound := bounds.cost_le operation

/-- Sequential composition combines certified budgets with the cost monoid. -/
def bind
    {bounds : OperationBounds A}
    {First Result : Type uResult}
    {first : Code A First} {next : First → Code A Result}
    {firstBudget nextBudget : M.Cost}
    (firstBound : Bound bounds first firstBudget)
    (nextBound : ∀ value, Bound bounds (next value) nextBudget) :
    Bound bounds (.bind first next)
      (M.instAddMonoid.add firstBudget nextBudget) where
  sound := by
    change
      ∀ result,
        result ∈
            (RandCostedT.bind (runCosted first)
              (fun value => runCosted (next value))).support →
          M.instPartialOrder.le result.cost
            (M.instAddMonoid.add firstBudget nextBudget)
    exact
      RandCostedT.bind_cost_le
        (M := M) (runCosted first) (fun value => runCosted (next value))
        firstBudget nextBudget firstBound.sound
        (fun value => (nextBound value).sound)

/-- Both branches may share a caller-selected common budget. -/
def branch
    {bounds : OperationBounds A}
    {Result : Type uResult} {condition : Bool}
    {thenCode elseCode : Code A Result} {budget : M.Cost}
    (thenBound : Bound bounds thenCode budget)
    (elseBound : Bound bounds elseCode budget) :
    Bound bounds (.branch condition thenCode elseCode) budget where
  sound := by
    intro result hresult
    simp only [runCosted] at hresult
    split at hresult
    · exact thenBound.sound result hresult
    · exact elseBound.sound result hresult

/-- Widen an already certified budget. -/
def weaken
    {bounds : OperationBounds A}
    {Result : Type uResult} {code : Code A Result}
    {budget largerBudget : M.Cost}
    (bound : Bound bounds code budget)
    (budget_le : M.instPartialOrder.le budget largerBudget) :
    Bound bounds code largerBudget where
  sound := by
    letI := M.instPartialOrder
    intro result hresult
    exact le_trans (bound.sound result hresult) budget_le

/-- Build a branch certificate from two bounds and a supplied common bound. -/
def branchOfBounds
    {bounds : OperationBounds A}
    {Result : Type uResult} {condition : Bool}
    {thenCode elseCode : Code A Result}
    {thenBudget elseBudget commonBudget : M.Cost}
    (thenBound : Bound bounds thenCode thenBudget)
    (elseBound : Bound bounds elseCode elseBudget)
    (then_le : M.instPartialOrder.le thenBudget commonBudget)
    (else_le : M.instPartialOrder.le elseBudget commonBudget) :
    Bound bounds (.branch condition thenCode elseCode) commonBudget :=
  branch (weaken thenBound then_le) (weaken elseBound else_le)

/--
Automatically derive a branch budget by taking the least common upper bound
provided by a worst-case cost model.
-/
def branchSup
    {W : WorstCaseCostModel.{uCost}}
    {S : Signature.{uResult, uOp}}
    {A : CostedAlgebra W.toCostModel S}
    {bounds : OperationBounds A}
    {Result : Type uResult} {condition : Bool}
    {thenCode elseCode : Code A Result}
    {thenBudget elseBudget : W.Cost}
    (thenBound : Bound bounds thenCode thenBudget)
    (elseBound : Bound bounds elseCode elseBudget) :
    Bound bounds (.branch condition thenCode elseCode)
      (W.instSemilatticeSup.sup thenBudget elseBudget) := by
  apply branchOfBounds thenBound elseBound
  · rw [← W.partialOrder_eq]
    exact @le_sup_left W.Cost W.instSemilatticeSup thenBudget elseBudget
  · rw [← W.partialOrder_eq]
    exact @le_sup_right W.Cost W.instSemilatticeSup thenBudget elseBudget

end Bound

end Code

variable
    {M : CostModel.{uCost}}
    {S : Signature.{uResult, uOp}}
    {A : CostedAlgebra M S}
    {Input : Type uIn} {Output : Type uResult}

/-- Execute an input-parameterized program with exact resource annotations. -/
noncomputable def runCosted
    (program : Program A Input Output) (input : Input) : RandCostedT M Output :=
  Code.runCosted (program.body input)

/-- The ordinary program semantics, defined solely by exact-cost erasure. -/
noncomputable def valueDist
    (program : Program A Input Output) (input : Input) : PMF Output :=
  RandCostedT.valueDist (runCosted program input)

/-- An input-dependent upper bound for all exact program paths. -/
def CostBound
    (program : Program A Input Output) (budget : Input → M.Cost) : Prop :=
  ∀ input, Code.CostBound (program.body input) (budget input)

/--
A single program paired with an input-dependent structural cost certificate.

The algorithm body is stored once; the certificate refers to that same body.
-/
structure BoundedProgram
    (bounds : OperationBounds A) (budget : Input → M.Cost) where
  program : Program A Input Output
  certificate :
    ∀ input, Code.Bound bounds (program.body input) (budget input)

namespace BoundedProgram

variable
    {bounds : OperationBounds A}
    {budget : Input → M.Cost}

/-- A bounded program's certificate implies its semantic path bound. -/
theorem costBound
    (program : BoundedProgram (Output := Output) bounds budget) :
    Program.CostBound program.program budget := by
  intro input
  exact (program.certificate input).sound

/-- Every concrete result respects the bounded program's input-specific budget. -/
theorem cost_le_budget_of_mem_support
    (program : BoundedProgram (Output := Output) bounds budget)
    (input : Input) (result : CostedT M Output)
    (hresult : result ∈ (Program.runCosted program.program input).support) :
    M.instPartialOrder.le result.cost (budget input) :=
  program.costBound input result hresult

end BoundedProgram

end Program

end Crypto.Infrastructure.Computation

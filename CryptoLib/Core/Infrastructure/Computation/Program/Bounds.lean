import CryptoLib.Core.Infrastructure.Computation.Algebra.Bounds
import CryptoLib.Core.Infrastructure.Computation.Cost.PathBound
import CryptoLib.Core.Infrastructure.Computation.Program.Execution

namespace CryptoLib.Core.Infrastructure.Computation

open CryptoLib.Core.Infrastructure.Computation.Algebra
open CryptoLib.Core.Infrastructure.Computation.Cost

universe uCost uResult uOp uIn

namespace Program

namespace Code

variable
    {M : CostModel.{uCost}}
    {S : Signature.{uResult, uOp}}
    {A : CostedAlgebra M S}

/-- Every exact interpreter path of `code` is bounded by `budget`. -/
abbrev CostBound
    {Result : Type uResult} (code : Code A Result) (budget : M.Cost) : Prop :=
  RandCosted.CostBound (runCosted code) budget

/--
A structural upper-bound certificate over an existing code value.

The code is an index, not a field, so this certificate cannot contain or
interpret a second copy of the algorithm.
-/
structure Bound (bounds : OperationBounds A)
    {Result : Type uResult} (code : Code A Result) (budget : M.Cost) : Prop where
  sound : CostBound code budget

namespace Bound

variable
    {bounds : OperationBounds A}
    {First Result : Type uResult}
    {condition : Bool}
    {thenCode elseCode : Code A Result}

/-- Pure code has zero cost. -/
def pure
    (value : Result) :
    Bound bounds (.pure value) M.instAddMonoid.zero where
  sound := RandCosted.CostBound.pure value

/-- A primitive call uses its independently supplied operation bound. -/
def call
    (operation : S.Op Result) :
    Bound bounds (.call operation) (bounds.budget operation) where
  sound := bounds.cost_le operation

/-- Sequential composition combines certified budgets in execution order. -/
def bind
    {first : Code A First} {next : First → Code A Result}
    {firstBudget nextBudget : M.Cost}
    (firstBound : Bound bounds first firstBudget)
    (nextBound : ∀ value, Bound bounds (next value) nextBudget) :
    Bound bounds (.bind first next)
      (M.instAddMonoid.add firstBudget nextBudget) where
  sound := by
    change
      RandCosted.CostBound
        (RandCosted.bind (runCosted first)
          (fun value => runCosted (next value)))
        (M.instAddMonoid.add firstBudget nextBudget)
    exact RandCosted.CostBound.bind firstBound.sound
      (fun value => (nextBound value).sound)

/-- Both branches may share a caller-selected common budget. -/
def branch
    {budget : M.Cost}
    (thenBound : Bound bounds thenCode budget)
    (elseBound : Bound bounds elseCode budget) :
    Bound bounds (.branch condition thenCode elseCode) budget where
  sound := by
    cases condition
    · exact elseBound.sound
    · exact thenBound.sound

/-- Widen an already certified budget. -/
def weaken
    {code : Code A Result}
    {budget largerBudget : M.Cost}
    (bound : Bound bounds code budget)
    (budget_le : M.instPartialOrder.le budget largerBudget) :
    Bound bounds code largerBudget where
  sound := RandCosted.CostBound.weaken bound.sound budget_le

/-- Build a branch certificate from two bounds and an explicit common bound. -/
def branchOfBounds
    {thenBudget elseBudget commonBudget : M.Cost}
    (thenBound : Bound bounds thenCode thenBudget)
    (elseBound : Bound bounds elseCode elseBudget)
    (then_le : M.instPartialOrder.le thenBudget commonBudget)
    (else_le : M.instPartialOrder.le elseBudget commonBudget) :
    Bound bounds (.branch condition thenCode elseCode) commonBudget :=
  branch (weaken thenBound then_le) (weaken elseBound else_le)

/-- Automatically derive a branch budget from a worst-case cost model. -/
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
      (W.sup thenBudget elseBudget) :=
  branchOfBounds thenBound elseBound
    (W.le_sup_left thenBudget elseBudget)
    (W.le_sup_right thenBudget elseBudget)

end Bound

end Code

variable
    {M : CostModel.{uCost}}
    {S : Signature.{uResult, uOp}}
    {A : CostedAlgebra M S}
    {Input : Type uIn} {Output : Type uResult}

/-- An input-dependent upper bound for all exact program paths. -/
def CostBound
    (program : Program A Input Output) (budget : Input → M.Cost) : Prop :=
  ∀ input, Code.CostBound (program.body input) (budget input)

/-- A single program paired with a proof of its input-dependent path bound. -/
structure BoundedProgram
    (bounds : OperationBounds A) (budget : Input → M.Cost) where
  program : Program A Input Output
  certificate :
    ∀ input, Code.Bound bounds (program.body input) (budget input)

namespace BoundedProgram

variable
    {bounds : OperationBounds A}
    {budget : Input → M.Cost}

/-- A bounded program's structural certificate implies its semantic path bound. -/
theorem costBound
    (program : BoundedProgram (Output := Output) bounds budget) :
    Program.CostBound program.program budget := by
  intro input
  exact (program.certificate input).sound

/-- Every exact result respects the bounded program's input-specific budget. -/
theorem cost_le_budget_of_mem_support
    (program : BoundedProgram (Output := Output) bounds budget)
    (input : Input) (result : Costed M Output)
    (hresult : result ∈ (Program.runCosted program.program input).support) :
    M.instPartialOrder.le result.cost (budget input) :=
  program.costBound input result hresult

end BoundedProgram

end Program

end CryptoLib.Core.Infrastructure.Computation

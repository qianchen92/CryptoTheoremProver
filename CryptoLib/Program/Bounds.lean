import CryptoLib.Core.Infrastructure.Computation.Cost.PathBound
import CryptoLib.Program.Semantics
import CryptoLib.Program.Validation

namespace CryptoLib.Program

open CryptoLib.Core.Infrastructure.Computation.Cost

universe uCost uBase uValue uOp

namespace Code

/-- Every exact execution path of first-order code is within `budget`. -/
abbrev CostBound
    {M : CostModel.{uCost}}
    {Base : Type uBase} {interpret : Base → Type uValue}
    {S : Signature.{uBase, uOp} Base} (A : CostedAlgebra M interpret S)
    {context : List (Ty Base)} {Result : Ty Base}
    (code : Code interpret S context Result)
    (environment : Env interpret context) (budget : M.Cost) : Prop :=
  RandCosted.CostBound (runCosted A code environment) budget

/-- Returning a pure expression has zero path cost. -/
theorem CostBound.ret
    {M : CostModel.{uCost}}
    {Base : Type uBase} {interpret : Base → Type uValue}
    {S : Signature.{uBase, uOp} Base} {A : CostedAlgebra M interpret S}
    {context : List (Ty Base)} {Result : Ty Base}
    (result : Expr interpret context Result)
    (environment : Env interpret context) :
    CostBound A (.ret result) environment M.instAddMonoid.zero :=
  RandCosted.CostBound.pure (result.eval environment)

/-- A pure let-binding preserves the continuation's path bound. -/
theorem CostBound.letPure
    {M : CostModel.{uCost}}
    {Base : Type uBase} {interpret : Base → Type uValue}
    {S : Signature.{uBase, uOp} Base} {A : CostedAlgebra M interpret S}
    {context : List (Ty Base)} {Value Result : Ty Base}
    {value : Expr interpret context Value}
    {next : Code interpret S (Value :: context) Result}
    {environment : Env interpret context} {budget : M.Cost}
    (nextBound :
      CostBound A next (.cons (value.eval environment) environment) budget) :
    CostBound A (.letPure value next) environment budget :=
  nextBound

/-- A primitive bound and a uniform continuation bound compose additively. -/
theorem CostBound.call
    {M : CostModel.{uCost}}
    {Base : Type uBase} {interpret : Base → Type uValue}
    {S : Signature.{uBase, uOp} Base} {A : CostedAlgebra M interpret S}
    {context : List (Ty Base)} {Args Value Result : Ty Base}
    {operation : S.Op Args Value} {args : Expr interpret context Args}
    {next : Code interpret S (Value :: context) Result}
    {environment : Env interpret context}
    {operationBudget nextBudget : M.Cost}
    (operationBound :
      RandCosted.CostBound
        (A.exec operation (args.eval environment)) operationBudget)
    (nextBound : ∀ value,
      CostBound A next (.cons value environment) nextBudget) :
    CostBound A (.call operation args next) environment
      (M.instAddMonoid.add operationBudget nextBudget) := by
  change
    RandCosted.CostBound
      (RandCosted.bind
        (A.exec operation (args.eval environment))
        (fun value => runCosted A next (.cons value environment)))
      (M.instAddMonoid.add operationBudget nextBudget)
  apply RandCosted.CostBound.bind operationBound
  intro value
  exact nextBound value

/-- Two branches with a common budget bound the represented conditional. -/
theorem CostBound.branch
    {M : CostModel.{uCost}}
    {Base : Type uBase} {interpret : Base → Type uValue}
    {S : Signature.{uBase, uOp} Base} {A : CostedAlgebra M interpret S}
    {context : List (Ty Base)} {Result : Ty Base}
    {condition : Expr interpret context .bool}
    {thenCode elseCode : Code interpret S context Result}
    {environment : Env interpret context} {budget : M.Cost}
    (thenBound : CostBound A thenCode environment budget)
    (elseBound : CostBound A elseCode environment budget) :
    CostBound A (.branch condition thenCode elseCode) environment budget := by
  change
    RandCosted.CostBound
      (if (condition.eval environment).down then
        runCosted A thenCode environment
      else runCosted A elseCode environment)
      budget
  split
  · exact thenBound
  · exact elseBound

end Code

namespace Procedure

/-- An input-dependent path bound for a first-order program. -/
def CostBound
    {M : CostModel.{uCost}}
    {Base : Type uBase} {interpret : Base → Type uValue}
    {S : Signature.{uBase, uOp} Base} (A : CostedAlgebra M interpret S)
    {Input Output : Ty Base} (program : Procedure interpret S Input Output)
    (budget : Ty.denote interpret Input → M.Cost) : Prop :=
  ∀ input, Code.CostBound A program.body (.cons input .nil) (budget input)

/-- One first-order program paired with a semantic exact path-cost bound. -/
structure Bounded
    {M : CostModel.{uCost}}
    {Base : Type uBase} {interpret : Base → Type uValue}
    {S : Signature.{uBase, uOp} Base} (A : CostedAlgebra M interpret S)
    {Input Output : Ty Base} (budget : Ty.denote interpret Input → M.Cost) where
  program : Procedure interpret S Input Output
  certificate : CostBound A program budget

end Procedure

end CryptoLib.Program

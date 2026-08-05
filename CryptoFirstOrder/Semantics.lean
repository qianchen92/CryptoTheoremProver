import CryptoFirstOrder.Syntax
import Mathlib.Probability.ProbabilityMassFunction.Monad

namespace CryptoFirstOrder

open Crypto.Infrastructure.Computation.Cost

universe uCost uBase uValue uOp

namespace Code

/-- Execute first-order code using the algebra's exact primitive handler. -/
noncomputable def runCosted
    {M : CostModel.{uCost}}
    {Base : Type uBase} {interpret : Base → Type uValue}
    {S : Signature.{uBase, uOp} Base} (A : CostedAlgebra M interpret S)
    {context : List (Ty Base)} {Result : Ty Base}
    (code : Code interpret S context Result)
    (environment : Env interpret context) :
    RandCosted M (Ty.denote interpret Result) :=
  match code with
  | .ret result => RandCosted.pure M (result.eval environment)
  | .letPure value next =>
      runCosted A next (.cons (value.eval environment) environment)
  | .call operation args next =>
      RandCosted.bind (A.exec operation (args.eval environment)) fun value =>
        runCosted A next (.cons value environment)
  | .branch condition thenCode elseCode =>
      if (condition.eval environment).down then
        runCosted A thenCode environment
      else
        runCosted A elseCode environment

/-- Erase exact path costs from the execution of first-order code. -/
noncomputable def valueDist
    {M : CostModel.{uCost}}
    {Base : Type uBase} {interpret : Base → Type uValue}
    {S : Signature.{uBase, uOp} Base} (A : CostedAlgebra M interpret S)
    {context : List (Ty Base)} {Result : Ty Base}
    (code : Code interpret S context Result)
    (environment : Env interpret context) :
    PMF (Ty.denote interpret Result) :=
  RandCosted.valueDist (runCosted A code environment)

@[simp] theorem valueDist_ret
    {M : CostModel.{uCost}}
    {Base : Type uBase} {interpret : Base → Type uValue}
    {S : Signature.{uBase, uOp} Base} (A : CostedAlgebra M interpret S)
    {context : List (Ty Base)} {Result : Ty Base}
    (result : Expr interpret context Result)
    (environment : Env interpret context) :
    valueDist A (.ret result) environment =
      PMF.pure (result.eval environment) := by
  simp [valueDist, runCosted]

@[simp] theorem valueDist_letPure
    {M : CostModel.{uCost}}
    {Base : Type uBase} {interpret : Base → Type uValue}
    {S : Signature.{uBase, uOp} Base} (A : CostedAlgebra M interpret S)
    {context : List (Ty Base)} {Value Result : Ty Base}
    (value : Expr interpret context Value)
    (next : Code interpret S (Value :: context) Result)
    (environment : Env interpret context) :
    valueDist A (.letPure value next) environment =
      valueDist A next (.cons (value.eval environment) environment) :=
  rfl

@[simp] theorem valueDist_call
    {M : CostModel.{uCost}}
    {Base : Type uBase} {interpret : Base → Type uValue}
    {S : Signature.{uBase, uOp} Base} (A : CostedAlgebra M interpret S)
    {context : List (Ty Base)} {Args Value Result : Ty Base}
    (operation : S.Op Args Value) (args : Expr interpret context Args)
    (next : Code interpret S (Value :: context) Result)
    (environment : Env interpret context) :
    valueDist A (.call operation args next) environment =
      PMF.bind
        (RandCosted.valueDist (A.exec operation (args.eval environment)))
        (fun value => valueDist A next (.cons value environment)) := by
  simp [valueDist, runCosted]

@[simp] theorem valueDist_branch
    {M : CostModel.{uCost}}
    {Base : Type uBase} {interpret : Base → Type uValue}
    {S : Signature.{uBase, uOp} Base} (A : CostedAlgebra M interpret S)
    {context : List (Ty Base)} {Result : Ty Base}
    (condition : Expr interpret context .bool)
    (thenCode elseCode : Code interpret S context Result)
    (environment : Env interpret context) :
    valueDist A (.branch condition thenCode elseCode) environment =
      if (condition.eval environment).down then
        valueDist A thenCode environment
      else valueDist A elseCode environment := by
  cases hcondition : (condition.eval environment).down <;>
    simp [valueDist, runCosted, hcondition]

end Code

namespace Program

/-- Execute a first-order program from its single external input. -/
noncomputable def runCosted
    {M : CostModel.{uCost}}
    {Base : Type uBase} {interpret : Base → Type uValue}
    {S : Signature.{uBase, uOp} Base} (A : CostedAlgebra M interpret S)
    {Input Output : Ty Base} (program : Program interpret S Input Output)
    (input : Ty.denote interpret Input) :
    RandCosted M (Ty.denote interpret Output) :=
  Code.runCosted A program.body (.cons input .nil)

/-- Ordinary semantics is obtained only by erasing exact path costs. -/
noncomputable def valueDist
    {M : CostModel.{uCost}}
    {Base : Type uBase} {interpret : Base → Type uValue}
    {S : Signature.{uBase, uOp} Base} (A : CostedAlgebra M interpret S)
    {Input Output : Ty Base} (program : Program interpret S Input Output)
    (input : Ty.denote interpret Input) :
    PMF (Ty.denote interpret Output) :=
  RandCosted.valueDist (runCosted A program input)

end Program

end CryptoFirstOrder

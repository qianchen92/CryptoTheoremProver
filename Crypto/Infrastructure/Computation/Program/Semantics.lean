import Crypto.Infrastructure.Computation.Algebra.Laws
import Crypto.Infrastructure.Computation.Program.Syntax
import Mathlib.Probability.ProbabilityMassFunction.Monad

namespace Crypto.Infrastructure.Computation

open Crypto.Infrastructure.Computation.Algebra
open Crypto.Infrastructure.Computation.Cost

universe uCost uResult uOp uIn

namespace Program

namespace Code

variable
    {M : CostModel.{uCost}}
    {S : Signature.{uResult, uOp}}
    {A : CostedAlgebra M S}

/-- Execute code using the algebra's sole exact primitive handler. -/
noncomputable def runCosted
    {Result : Type uResult} (code : Code A Result) : RandCosted M Result :=
  match code with
  | .pure value => RandCosted.pure M value
  | .bind first next =>
      RandCosted.bind (runCosted first) fun value => runCosted (next value)
  | .call operation => A.exec operation
  | .branch condition thenCode elseCode =>
      if condition then runCosted thenCode else runCosted elseCode

variable {First Result : Type uResult}

/-- Ordinary semantics is obtained only by erasing exact path costs. -/
noncomputable def valueDist
    (code : Code A Result) : PMF Result :=
  RandCosted.valueDist (runCosted code)

@[simp] theorem valueDist_pure
    (value : Result) :
    valueDist (A := A) (.pure value) = PMF.pure value := by
  simp [valueDist, runCosted]

@[simp] theorem valueDist_bind
    (first : Code A First) (next : First → Code A Result) :
    valueDist (.bind first next) =
      PMF.bind (valueDist first) fun value => valueDist (next value) := by
  simp [valueDist, runCosted]

@[simp] theorem valueDist_call
    (operation : S.Op Result) :
    valueDist (A := A) (.call operation) =
      RandCosted.valueDist (A.exec operation) :=
  rfl

@[simp] theorem valueDist_branch
    (condition : Bool)
    (thenCode elseCode : Code A Result) :
    valueDist (.branch condition thenCode elseCode) =
      if condition then valueDist thenCode else valueDist elseCode := by
  cases condition <;> simp [valueDist, runCosted]

/-- A primitive call satisfies the algebra's cost-erased specification. -/
@[simp] theorem valueDist_call_eq
    (laws : AlgebraLaws A)
    {Result : Type uResult} (operation : S.Op Result) :
    valueDist (A := A) (.call operation) = laws.semantics operation :=
  laws.exec_spec operation

end Code

variable
    {M : CostModel.{uCost}}
    {S : Signature.{uResult, uOp}}
    {A : CostedAlgebra M S}
    {Input : Type uIn} {Output : Type uResult}

/-- Execute an input-parameterized program with exact resource annotations. -/
noncomputable def runCosted
    (program : Program A Input Output) (input : Input) : RandCosted M Output :=
  Code.runCosted (program.body input)

/-- The ordinary program semantics, defined solely by exact-cost erasure. -/
noncomputable def valueDist
    (program : Program A Input Output) (input : Input) : PMF Output :=
  RandCosted.valueDist (runCosted program input)

end Program

end Crypto.Infrastructure.Computation

import CryptoLib.Program.Transform.Handler

namespace CryptoLib.Program

open CryptoLib.Core.Infrastructure.Computation.Cost

universe uCost uBase uValue uSourceOp uMiddleOp uTargetOp

namespace Handler

/-- Inlining one operation has exactly the semantics of its procedure body. -/
theorem runCosted_inline
    {M : CostModel.{uCost}}
    {Base : Type uBase} {interpret : Base → Type uValue}
    {source : Signature.{uBase, uSourceOp} Base}
    {target : Signature.{uBase, uTargetOp} Base}
    (handler : Handler interpret source target)
    (targetAlgebra : CostedAlgebra M interpret target)
    {Args Result : Ty Base} (operation : source.Op Args Result)
    {context : List (Ty Base)} (args : Expr interpret context Args)
    (environment : Env interpret context) :
    Code.runCosted targetAlgebra (handler.inline operation args) environment =
      Procedure.runCosted targetAlgebra (handler.body operation)
        (args.eval environment) := by
  unfold Handler.inline Procedure.runCosted
  apply Code.runCosted_subst
  exact Env.subRelated_single args environment

/-- Cost erasure of `runCosted_inline`. -/
theorem valueDist_inline
    {M : CostModel.{uCost}}
    {Base : Type uBase} {interpret : Base → Type uValue}
    {source : Signature.{uBase, uSourceOp} Base}
    {target : Signature.{uBase, uTargetOp} Base}
    (handler : Handler interpret source target)
    (targetAlgebra : CostedAlgebra M interpret target)
    {Args Result : Ty Base} (operation : source.Op Args Result)
    {context : List (Ty Base)} (args : Expr interpret context Args)
    (environment : Env interpret context) :
    Code.valueDist targetAlgebra (handler.inline operation args) environment =
      Procedure.valueDist targetAlgebra (handler.body operation)
        (args.eval environment) := by
  unfold Code.valueDist Procedure.valueDist
  exact congrArg RandCosted.valueDist
    (runCosted_inline handler targetAlgebra operation args environment)

end Handler

namespace Code

/--
Handling preserves the complete exact value-and-cost distribution under the
algebra induced from the target handler implementation.
-/
theorem runCosted_handle
    {M : CostModel.{uCost}}
    {Base : Type uBase} {interpret : Base → Type uValue}
    {source : Signature.{uBase, uSourceOp} Base}
    {target : Signature.{uBase, uTargetOp} Base}
    (handler : Handler interpret source target)
    (targetAlgebra : CostedAlgebra M interpret target)
    {context : List (Ty Base)} {result : Ty Base}
    (code : Code interpret source context result)
    (environment : Env interpret context) :
    runCosted targetAlgebra (code.handle handler) environment =
      runCosted (handler.inducedAlgebra targetAlgebra) code environment := by
  induction code with
  | ret value => rfl
  | letPure value next ih =>
      simp only [handle, runCosted]
      exact ih (.cons (value.eval environment) environment)
  | call operation args next ih =>
      simp only [handle, runCosted_seq, runCosted, Handler.inducedAlgebra]
      rw [Handler.runCosted_inline]
      apply congrArg
        (RandCosted.bind
          (Procedure.runCosted targetAlgebra (handler.body operation)
            (args.eval environment)))
      funext value
      exact ih (.cons value environment)
  | branch condition thenCode elseCode ihThen ihElse =>
      simp only [handle, runCosted]
      split
      · exact ihThen environment
      · exact ihElse environment

/-- Value-distribution preservation derived from exact handler preservation. -/
theorem valueDist_handle
    {M : CostModel.{uCost}}
    {Base : Type uBase} {interpret : Base → Type uValue}
    {source : Signature.{uBase, uSourceOp} Base}
    {target : Signature.{uBase, uTargetOp} Base}
    (handler : Handler interpret source target)
    (targetAlgebra : CostedAlgebra M interpret target)
    {context : List (Ty Base)} {result : Ty Base}
    (code : Code interpret source context result)
    (environment : Env interpret context) :
    valueDist targetAlgebra (code.handle handler) environment =
      valueDist (handler.inducedAlgebra targetAlgebra) code environment := by
  unfold valueDist
  exact congrArg RandCosted.valueDist
    (runCosted_handle handler targetAlgebra code environment)

end Code

namespace Procedure

/-- Procedure-level exact semantic preservation for handlers. -/
theorem runCosted_handle
    {M : CostModel.{uCost}}
    {Base : Type uBase} {interpret : Base → Type uValue}
    {source : Signature.{uBase, uSourceOp} Base}
    {target : Signature.{uBase, uTargetOp} Base}
    (handler : Handler interpret source target)
    (targetAlgebra : CostedAlgebra M interpret target)
    {input output : Ty Base}
    (procedure : Procedure interpret source input output)
    (value : Ty.denote interpret input) :
    runCosted targetAlgebra (procedure.handle handler) value =
      runCosted (handler.inducedAlgebra targetAlgebra) procedure value := by
  exact Code.runCosted_handle handler targetAlgebra procedure.body (.cons value .nil)

/-- Procedure value-distribution preservation derived from exact equality. -/
theorem valueDist_handle
    {M : CostModel.{uCost}}
    {Base : Type uBase} {interpret : Base → Type uValue}
    {source : Signature.{uBase, uSourceOp} Base}
    {target : Signature.{uBase, uTargetOp} Base}
    (handler : Handler interpret source target)
    (targetAlgebra : CostedAlgebra M interpret target)
    {input output : Ty Base}
    (procedure : Procedure interpret source input output)
    (value : Ty.denote interpret input) :
    valueDist targetAlgebra (procedure.handle handler) value =
      valueDist (handler.inducedAlgebra targetAlgebra) procedure value := by
  unfold valueDist
  exact congrArg RandCosted.valueDist
    (runCosted_handle handler targetAlgebra procedure value)

end Procedure

namespace Handler

/-- The identity handler induces the original exact algebra. -/
@[simp] theorem inducedAlgebra_id
    {M : CostModel.{uCost}}
    {Base : Type uBase} {interpret : Base → Type uValue}
    {signature : Signature.{uBase, uSourceOp} Base}
    (algebra : CostedAlgebra M interpret signature) :
    (Handler.id signature).inducedAlgebra algebra = algebra := by
  cases algebra with
  | mk exec =>
      rw [CostedAlgebra.mk.injEq]
      funext Args Result operation args
      exact RandCosted.bind_pure (exec operation args)

/-- Handler composition induces nested source algebras in execution order. -/
@[simp] theorem inducedAlgebra_comp
    {M : CostModel.{uCost}}
    {Base : Type uBase} {interpret : Base → Type uValue}
    {source : Signature.{uBase, uSourceOp} Base}
    {middle : Signature.{uBase, uMiddleOp} Base}
    {target : Signature.{uBase, uTargetOp} Base}
    (first : Handler interpret source middle)
    (second : Handler interpret middle target)
    (targetAlgebra : CostedAlgebra M interpret target) :
    (second.comp first).inducedAlgebra targetAlgebra =
      first.inducedAlgebra (second.inducedAlgebra targetAlgebra) := by
  rw [CostedAlgebra.mk.injEq]
  funext Args Result operation args
  exact Procedure.runCosted_handle second targetAlgebra
    (first.body operation) args

end Handler

namespace Code

/-- Exact semantic equivalence of code under a fixed costed algebra. -/
def RunCostedEq
    {M : CostModel.{uCost}}
    {Base : Type uBase} {interpret : Base → Type uValue}
    {S : Signature.{uBase, uSourceOp} Base}
    {context : List (Ty Base)} {result : Ty Base}
    (algebra : CostedAlgebra M interpret S)
    (left right : Code interpret S context result) : Prop :=
  ∀ environment, runCosted algebra left environment = runCosted algebra right environment

theorem RunCostedEq.refl
    {M : CostModel.{uCost}}
    {Base : Type uBase} {interpret : Base → Type uValue}
    {S : Signature.{uBase, uSourceOp} Base}
    {context : List (Ty Base)} {result : Ty Base}
    {algebra : CostedAlgebra M interpret S}
    (code : Code interpret S context result) :
    RunCostedEq algebra code code :=
  fun _ ↦ rfl

theorem RunCostedEq.symm
    {M : CostModel.{uCost}}
    {Base : Type uBase} {interpret : Base → Type uValue}
    {S : Signature.{uBase, uSourceOp} Base}
    {context : List (Ty Base)} {result : Ty Base}
    {algebra : CostedAlgebra M interpret S}
    {left right : Code interpret S context result}
    (equivalent : RunCostedEq algebra left right) :
    RunCostedEq algebra right left :=
  fun environment ↦ (equivalent environment).symm

theorem RunCostedEq.trans
    {M : CostModel.{uCost}}
    {Base : Type uBase} {interpret : Base → Type uValue}
    {S : Signature.{uBase, uSourceOp} Base}
    {context : List (Ty Base)} {result : Ty Base}
    {algebra : CostedAlgebra M interpret S}
    {first second third : Code interpret S context result}
    (firstSecond : RunCostedEq algebra first second)
    (secondThird : RunCostedEq algebra second third) :
    RunCostedEq algebra first third :=
  fun environment ↦ (firstSecond environment).trans (secondThird environment)

/-- Pointwise exact identity-handler law. -/
theorem runCosted_handle_id
    {M : CostModel.{uCost}}
    {Base : Type uBase} {interpret : Base → Type uValue}
    {S : Signature.{uBase, uSourceOp} Base}
    (algebra : CostedAlgebra M interpret S)
    {context : List (Ty Base)} {result : Ty Base}
    (code : Code interpret S context result)
    (environment : Env interpret context) :
    runCosted algebra (code.handle (Handler.id S)) environment =
      runCosted algebra code environment := by
  rw [runCosted_handle, Handler.inducedAlgebra_id]

/-- Identity handling is exact semantic equivalence. -/
theorem handle_id
    {M : CostModel.{uCost}}
    {Base : Type uBase} {interpret : Base → Type uValue}
    {S : Signature.{uBase, uSourceOp} Base}
    (algebra : CostedAlgebra M interpret S)
    {context : List (Ty Base)} {result : Ty Base}
    (code : Code interpret S context result) :
    RunCostedEq algebra (code.handle (Handler.id S)) code :=
  runCosted_handle_id algebra code

/-- Pointwise exact handler-composition law. -/
theorem runCosted_handle_comp
    {M : CostModel.{uCost}}
    {Base : Type uBase} {interpret : Base → Type uValue}
    {source : Signature.{uBase, uSourceOp} Base}
    {middle : Signature.{uBase, uMiddleOp} Base}
    {target : Signature.{uBase, uTargetOp} Base}
    (first : Handler interpret source middle)
    (second : Handler interpret middle target)
    (targetAlgebra : CostedAlgebra M interpret target)
    {context : List (Ty Base)} {result : Ty Base}
    (code : Code interpret source context result)
    (environment : Env interpret context) :
    runCosted targetAlgebra (code.handle (second.comp first)) environment =
      runCosted targetAlgebra ((code.handle first).handle second) environment := by
  calc
    runCosted targetAlgebra (code.handle (second.comp first)) environment =
        runCosted ((second.comp first).inducedAlgebra targetAlgebra)
          code environment :=
      runCosted_handle (second.comp first) targetAlgebra code environment
    _ = runCosted (first.inducedAlgebra (second.inducedAlgebra targetAlgebra))
          code environment := by
      rw [Handler.inducedAlgebra_comp]
    _ = runCosted (second.inducedAlgebra targetAlgebra)
          (code.handle first) environment :=
      (runCosted_handle first (second.inducedAlgebra targetAlgebra)
        code environment).symm
    _ = runCosted targetAlgebra
          ((code.handle first).handle second) environment :=
      (runCosted_handle second targetAlgebra
        (code.handle first) environment).symm

/-- Composed and staged handling are exact semantic equivalents. -/
theorem handle_comp
    {M : CostModel.{uCost}}
    {Base : Type uBase} {interpret : Base → Type uValue}
    {source : Signature.{uBase, uSourceOp} Base}
    {middle : Signature.{uBase, uMiddleOp} Base}
    {target : Signature.{uBase, uTargetOp} Base}
    (first : Handler interpret source middle)
    (second : Handler interpret middle target)
    (targetAlgebra : CostedAlgebra M interpret target)
    {context : List (Ty Base)} {result : Ty Base}
    (code : Code interpret source context result) :
    RunCostedEq targetAlgebra
      (code.handle (second.comp first))
      ((code.handle first).handle second) :=
  runCosted_handle_comp first second targetAlgebra code

/-- Identity-handler value equality derived from exact equality. -/
theorem valueDist_handle_id
    {M : CostModel.{uCost}}
    {Base : Type uBase} {interpret : Base → Type uValue}
    {S : Signature.{uBase, uSourceOp} Base}
    (algebra : CostedAlgebra M interpret S)
    {context : List (Ty Base)} {result : Ty Base}
    (code : Code interpret S context result)
    (environment : Env interpret context) :
    valueDist algebra (code.handle (Handler.id S)) environment =
      valueDist algebra code environment := by
  unfold valueDist
  exact congrArg RandCosted.valueDist
    (runCosted_handle_id algebra code environment)

/-- Handler-composition value equality derived from exact equality. -/
theorem valueDist_handle_comp
    {M : CostModel.{uCost}}
    {Base : Type uBase} {interpret : Base → Type uValue}
    {source : Signature.{uBase, uSourceOp} Base}
    {middle : Signature.{uBase, uMiddleOp} Base}
    {target : Signature.{uBase, uTargetOp} Base}
    (first : Handler interpret source middle)
    (second : Handler interpret middle target)
    (targetAlgebra : CostedAlgebra M interpret target)
    {context : List (Ty Base)} {result : Ty Base}
    (code : Code interpret source context result)
    (environment : Env interpret context) :
    valueDist targetAlgebra (code.handle (second.comp first)) environment =
      valueDist targetAlgebra ((code.handle first).handle second) environment := by
  unfold valueDist
  exact congrArg RandCosted.valueDist
    (runCosted_handle_comp first second targetAlgebra code environment)

end Code

end CryptoLib.Program

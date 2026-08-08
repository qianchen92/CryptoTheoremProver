import CryptoLib.Program.Transform.Substitution

namespace CryptoLib.Program

open CryptoLib.Core.Infrastructure.Computation.Cost

universe uCost uBase uValue uOp

namespace Code

/--
First-order sequencing for typed code.

The continuation is syntax under the result binder. Descending through an
existing binder inserts that binder below the continuation result, so the
continuation is lifted by `Ren.lift Ren.weaken`. No Lean continuation is stored
in `Code`.
-/
def seq
    {Base : Type uBase} {interpret : Base → Type uValue}
    {S : Signature.{uBase, uOp} Base}
    {context : List (Ty Base)} {first second : Ty Base} :
    Code interpret S context first →
    Code interpret S (first :: context) second →
    Code interpret S context second
  | .ret value, next => .letPure value next
  | .letPure value rest, next =>
      .letPure value
        (seq rest (next.rename (Ren.lift Ren.weaken)))
  | .call operation args rest, next =>
      .call operation args
        (seq rest (next.rename (Ren.lift Ren.weaken)))
  | .branch condition thenCode elseCode, next =>
      .branch condition (seq thenCode next) (seq elseCode next)

/--
Sequencing preserves the complete exact value-and-cost distribution and the
left-to-right order of primitive costs.
-/
theorem runCosted_seq
    {M : CostModel.{uCost}}
    {Base : Type uBase} {interpret : Base → Type uValue}
    {S : Signature.{uBase, uOp} Base} (algebra : CostedAlgebra M interpret S)
    {context : List (Ty Base)} {first second : Ty Base}
    (code : Code interpret S context first)
    (next : Code interpret S (first :: context) second)
    (environment : Env interpret context) :
    runCosted algebra (seq code next) environment =
      RandCosted.bind (runCosted algebra code environment) fun value ↦
        runCosted algebra next (.cons value environment) := by
  induction code with
  | ret value =>
      simp only [seq, runCosted]
      exact (RandCosted.pure_bind (value.eval environment)
        (fun result ↦ runCosted algebra next (.cons result environment))).symm
  | letPure value rest ih =>
      simp only [seq, runCosted]
      rw [ih]
      apply congrArg (RandCosted.bind (runCosted algebra rest
        (.cons (value.eval environment) environment)))
      funext result
      apply runCosted_rename
      exact Env.related_lift_weaken environment result (value.eval environment)
  | call operation args rest ih =>
      simp only [seq, runCosted]
      rw [RandCosted.bind_assoc]
      apply congrArg
        (RandCosted.bind (algebra.exec operation (args.eval environment)))
      funext operationResult
      rw [ih]
      apply congrArg (RandCosted.bind
        (runCosted algebra rest (.cons operationResult environment)))
      funext result
      apply runCosted_rename
      exact Env.related_lift_weaken environment result operationResult
  | branch condition thenCode elseCode ihThen ihElse =>
      simp only [seq, runCosted]
      split
      · exact ihThen next environment
      · exact ihElse next environment

/-- Cost erasure of `runCosted_seq`. -/
theorem valueDist_seq
    {M : CostModel.{uCost}}
    {Base : Type uBase} {interpret : Base → Type uValue}
    {S : Signature.{uBase, uOp} Base} (algebra : CostedAlgebra M interpret S)
    {context : List (Ty Base)} {first second : Ty Base}
    (code : Code interpret S context first)
    (next : Code interpret S (first :: context) second)
    (environment : Env interpret context) :
    valueDist algebra (seq code next) environment =
      PMF.bind (valueDist algebra code environment) fun value ↦
        valueDist algebra next (.cons value environment) := by
  simp only [valueDist, runCosted_seq, RandCosted.valueDist_bind]

end Code

end CryptoLib.Program

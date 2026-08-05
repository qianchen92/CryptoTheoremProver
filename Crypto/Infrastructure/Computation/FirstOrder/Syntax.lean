import Crypto.Infrastructure.Computation.FirstOrder.Algebra

namespace Crypto.Infrastructure.Computation.FirstOrder

universe uBase uValue uOp

/--
Pure first-order expressions. Base constants are static data; there are no
function-valued expressions or arbitrary Lean callbacks.
-/
inductive Expr
    {Base : Type uBase} (interpret : Base → Type uValue)
    (context : List (Ty Base)) : Ty Base → Type (max uBase uValue) where
  | var {Result : Ty Base} : Var context Result → Expr interpret context Result
  | unit : Expr interpret context .unit
  | bool (value : Bool) : Expr interpret context .bool
  | constant {name : Base} : interpret name → Expr interpret context (.base name)
  | pair {Left Right : Ty Base} :
      Expr interpret context Left → Expr interpret context Right →
      Expr interpret context (.prod Left Right)
  | fst {Left Right : Ty Base} :
      Expr interpret context (.prod Left Right) → Expr interpret context Left
  | snd {Left Right : Ty Base} :
      Expr interpret context (.prod Left Right) → Expr interpret context Right

namespace Expr

/-- Evaluate a pure expression in an explicit typed environment. -/
def eval
    {Base : Type uBase} {interpret : Base → Type uValue}
    {context : List (Ty Base)} {Result : Ty Base} :
    Expr interpret context Result → Env interpret context →
    Ty.denote interpret Result
  | .var index, environment => environment.get index
  | .unit, _ => ULift.up ()
  | .bool value, _ => ULift.up value
  | .constant value, _ => value
  | .pair left right, environment =>
      (left.eval environment, right.eval environment)
  | .fst product, environment => (product.eval environment).1
  | .snd product, environment => (product.eval environment).2

end Expr

/--
Typed first-order straight-line code.

The continuation of a binding is syntax under one additional de Bruijn
variable, rather than a Lean function. Consequently all runtime control flow
is represented by this inductive syntax.
-/
inductive Code
    {Base : Type uBase} (interpret : Base → Type uValue)
    (S : Signature.{uBase, uOp} Base) :
    List (Ty Base) → Ty Base →
    Type (max uBase (max uValue uOp)) where
  | ret {context : List (Ty Base)} {Result : Ty Base} :
      Expr interpret context Result → Code interpret S context Result
  | letPure {context : List (Ty Base)} {Value Result : Ty Base} :
      Expr interpret context Value →
      Code interpret S (Value :: context) Result →
      Code interpret S context Result
  | call {context : List (Ty Base)} {Args Value Result : Ty Base} :
      S.Op Args Value →
      Expr interpret context Args →
      Code interpret S (Value :: context) Result →
      Code interpret S context Result
  | branch {context : List (Ty Base)} {Result : Ty Base} :
      Expr interpret context .bool →
      Code interpret S context Result →
      Code interpret S context Result →
      Code interpret S context Result

/-- A closed first-order body with one distinguished external input. -/
structure Program
    {Base : Type uBase} (interpret : Base → Type uValue)
    (S : Signature.{uBase, uOp} Base) (Input Output : Ty Base) where
  body : Code interpret S [Input] Output

end Crypto.Infrastructure.Computation.FirstOrder

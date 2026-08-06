import CryptoFirstOrder.Algebra

namespace CryptoFirstOrder

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
  | none {Value : Ty Base} : Expr interpret context (.option Value)
  | some {Value : Ty Base} :
      Expr interpret context Value → Expr interpret context (.option Value)

namespace Expr

/-- Reuse a pure expression after extending its context by one fresh value. -/
def weaken
    {Base : Type uBase} {interpret : Base → Type uValue}
    {context : List (Ty Base)} {Result Other : Ty Base} :
    Expr interpret context Result → Expr interpret (Other :: context) Result
  | .var index => .var (.there index)
  | .unit => .unit
  | .bool value => .bool value
  | .constant value => .constant value
  | .pair left right => .pair left.weaken right.weaken
  | .fst product => .fst product.weaken
  | .snd product => .snd product.weaken
  | .none => .none
  | .some value => .some value.weaken

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
  | .none, _ => Option.none
  | .some value, environment => Option.some (value.eval environment)

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

namespace Program

/--
A first-order program with a statically known list of logical inputs.

The list is a surface-level typed context. It compiles to the existing single
structural input through `Ty.tuple`, so the trusted `Program` and `Code` cores
remain unchanged.
-/
abbrev NAry
    {Base : Type uBase} (interpret : Base → Type uValue)
    (S : Signature.{uBase, uOp} Base)
    (Inputs : List (Ty Base)) (Output : Ty Base) :=
  Program interpret S (Ty.tuple Inputs) Output

/-- An `NAry` program returning two logically distinct results. -/
abbrev NAryPair
    {Base : Type uBase} (interpret : Base → Type uValue)
    (S : Signature.{uBase, uOp} Base)
    (Inputs : List (Ty Base)) (Left Right : Ty Base) :=
  NAry interpret S Inputs (.prod Left Right)

/-- A compatibility name for a first-order program with no logical inputs. -/
abbrev Nullary
    {Base : Type uBase} (interpret : Base → Type uValue)
    (S : Signature.{uBase, uOp} Base) (Output : Ty Base) :=
  NAry interpret S [] Output

/-- A compatibility name for a first-order program with one logical input. -/
abbrev Unary
    {Base : Type uBase} (interpret : Base → Type uValue)
    (S : Signature.{uBase, uOp} Base) (Input Output : Ty Base) :=
  NAry interpret S [Input] Output

/-- A compatibility name for a first-order program with two logical inputs. -/
abbrev Binary
    {Base : Type uBase} (interpret : Base → Type uValue)
    (S : Signature.{uBase, uOp} Base)
    (Left Right Output : Ty Base) :=
  NAry interpret S [Left, Right] Output

/-- A compatibility name for a first-order program with three logical inputs. -/
abbrev Ternary
    {Base : Type uBase} (interpret : Base → Type uValue)
    (S : Signature.{uBase, uOp} Base)
    (First Second Third Output : Ty Base) :=
  NAry interpret S [First, Second, Third] Output

/-- A compatibility name for a nullary program returning two distinct results. -/
abbrev NullaryPair
    {Base : Type uBase} (interpret : Base → Type uValue)
    (S : Signature.{uBase, uOp} Base) (Left Right : Ty Base) :=
  NAryPair interpret S [] Left Right

end Program

end CryptoFirstOrder

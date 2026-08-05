namespace CryptoFirstOrder

universe uBase uValue

variable {Base : Type uBase}

/--
The value types available to the first-order language.

`Base` names the domain-specific carrier types. Unit, booleans, and products
are structural language types; functions are deliberately absent.
-/
inductive Ty (Base : Type uBase) : Type uBase where
  | unit
  | bool
  | base (name : Base)
  | prod (left right : Ty Base)
  deriving DecidableEq

/-- Product types in the first-order object language. -/
scoped infixr:35 " ×ₜ " => Ty.prod

namespace Ty

/--
Encode a statically known list of logical argument types as one structural
first-order input. Empty and singleton contexts avoid redundant products;
larger contexts are right-associated products.
-/
@[reducible] def tuple : List (Ty Base) → Ty Base
  | [] => .unit
  | [value] => value
  | value :: next :: rest => .prod value (tuple (next :: rest))

/-- Interpret a first-order type using a family of Lean carrier types. -/
def denote (interpret : Base → Type uValue) : Ty Base → Type uValue
  | .unit => ULift.{uValue} Unit
  | .bool => ULift.{uValue} Bool
  | .base name => interpret name
  | .prod left right => denote interpret left × denote interpret right

end Ty

/-- A typed, heterogeneous environment for de Bruijn variables. -/
inductive Env {Base : Type uBase} (interpret : Base → Type uValue) :
    List (Ty Base) → Type (max uBase uValue) where
  | nil : Env interpret []
  | cons {head : Ty Base} {tail : List (Ty Base)} :
      Ty.denote interpret head → Env interpret tail → Env interpret (head :: tail)

/-- A typed de Bruijn variable. -/
inductive Var {Base : Type uBase} : List (Ty Base) → Ty Base → Type uBase where
  | here {context : List (Ty Base)} {value : Ty Base} :
      Var (value :: context) value
  | there {context : List (Ty Base)} {value other : Ty Base} :
      Var context value → Var (other :: context) value

namespace Env

/-- Look up a typed variable in an environment. -/
def get
    {interpret : Base → Type uValue}
    {context : List (Ty Base)} {value : Ty Base} :
    Env interpret context → Var context value → Ty.denote interpret value
  | .cons head _, .here => head
  | .cons _ tail, .there index => get tail index

end Env

end CryptoFirstOrder

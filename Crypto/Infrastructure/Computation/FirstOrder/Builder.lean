import Crypto.Infrastructure.Computation.FirstOrder.Syntax
import Lean.Parser.Do

namespace Crypto.Infrastructure.Computation.FirstOrder

open Lean Macro

/--
Surface syntax for straight-line first-order programs.

The syntax uses ordinary `do` layout and named binders, but expands immediately
to `FirstOrder.Code`. No Lean continuation or variable name remains in the
resulting program.

Supported expression forms are bound names, `unit`, pairs, `value(...)`,
`fst(...)`, `snd(...)`, and booleans. Primitive calls have the form
`call operation with arguments`.
-/
scoped syntax:max (name := builderCall)
  "call " term:arg " with " term:arg : term

scoped syntax:max (name := builderValue)
  "value(" term ")" : term

scoped syntax:max (name := builderFst)
  "fst(" term ")" : term

scoped syntax:max (name := builderSnd)
  "snd(" term ")" : term

scoped syntax:lead (name := builderProgram)
  "first_order " ident " do " doSeq : term

namespace Builder

open scoped FirstOrder

private def findName (target : Name) : List Name → Option Nat
  | [] => none
  | name :: names =>
      if target == name then some 0 else (findName target names).map Nat.succ

private def variableSyntax (index : Nat) : MacroM (TSyntax `term) := do
  let mut resultSyntax ← `(.here)
  for _ in [:index] do
    resultSyntax ← `(.there $resultSyntax)
  `(.var $resultSyntax)

private partial def expressionSyntax
    (names : List Name) (expression : Syntax) : MacroM (TSyntax `term) := do
  if expression.isIdent then
    let name := expression.getId
    if let some index := findName name names then
      return ← variableSyntax index
    if name == `unit then
      return ← `(.unit)
    if name == `true then
      return ← `(.bool true)
    if name == `false then
      return ← `(.bool false)
    Macro.throwErrorAt expression
      "unknown first-order value; wrap static Lean values in `value(...)`"
  match expression with
  | `(value($value:term)) => `(.constant $value)
  | `(fst($product:term)) =>
      let product ← expressionSyntax names product
      `(.fst $product)
  | `(snd($product:term)) =>
      let product ← expressionSyntax names product
      `(.snd $product)
  | `(($left:term, $right:term)) =>
      let left ← expressionSyntax names left
      let right ← expressionSyntax names right
      `(.pair $left $right)
  | _ =>
      Macro.throwErrorAt expression
        "unsupported first-order expression"

private partial def codeSyntax
    (names : List Name) :
    List (TSyntax `doElem) → MacroM (TSyntax `term)
  | [] => Macro.throwError "first-order block must end with `return`"
  | element :: remaining =>
      match element with
      | `(doElem| let $name:ident ← $action:term) =>
          match action with
          | `(call $operation:term with $arguments:term) => do
              let arguments ← expressionSyntax names arguments
              let next ← codeSyntax (name.getId :: names) remaining
              `(.call $operation $arguments $next)
          | _ =>
              Macro.throwErrorAt action
                "first-order bind must use `call operation with arguments`"
      | `(doElem| let $name:ident := $value:term) => do
          let value ← expressionSyntax names value
          let next ← codeSyntax (name.getId :: names) remaining
          `(.letPure $value $next)
      | `(doElem| return $result:term) => do
          unless remaining.isEmpty do
            Macro.throwErrorAt element
              "statements after a first-order `return` are unreachable"
          let result ← expressionSyntax names result
          `(.ret $result)
      | _ =>
          Macro.throwErrorAt element
            "unsupported first-order statement"

macro_rules
  | `(first_order $input:ident do $sequence:doSeq) => do
      let elements := Lean.Parser.Term.getDoElems sequence
      codeSyntax [input.getId] elements.toList

end Builder

end Crypto.Infrastructure.Computation.FirstOrder

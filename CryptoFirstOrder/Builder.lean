import CryptoFirstOrder.Syntax
import CryptoFirstOrder.Operation
import CryptoFirstOrder.Semantics
import Lean.Parser.Do

namespace CryptoFirstOrder

open Lean Macro

/--
Surface syntax for straight-line first-order programs.

The syntax uses ordinary `do` layout and named binders, but expands immediately
to `CryptoFirstOrder.Code`. A single input uses `first_order input do`; a static typed
context uses `first_order () do` or `first_order (x, y, z) do`. No Lean
continuation, variable name, smart operation, or signature injection remains in
the resulting program.

Supported expression forms are bound names, `unit`, pairs, `value(...)`,
`fst(...)`, `snd(...)`, and booleans. Built-in smart calls are
`sample type sampler`, `unifSamp type`, `•`, `+`, `-`, unary `-`, and `*`.
Smart calls may be nested in those expression forms; the surface compiler
A-normalizes them from left to right before producing `Code`. The corresponding
named forms remain accepted. Raw primitive calls remain available as
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

scoped syntax:lead (name := builderProgramInputs)
  "first_order" "(" ident,* ")" "do" doSeq : term

universe uSource uTarget uLift

/-- Surface programs may pass native values where an `ULift` is expected. -/
scoped instance valueToULift (Value : Type uSource) :
    CoeTC Value (ULift.{uLift} Value) where
  coe := ULift.up

namespace Builder

open scoped CryptoFirstOrder
open Crypto.Infrastructure.Computation.Cost

/-- Represent an ordinary host value at an object-language boundary. -/
class ValueRepresentation (Source : Type uSource) (Target : Type uTarget) where
  represent : Source → Target

/-- Use the representation inferred from the expected object-language type. -/
def representValue
    {Source : Type uSource} {Target : Type uTarget}
    [ValueRepresentation Source Target] : Source → Target :=
  ValueRepresentation.represent

instance valueRepresentationIdentity (Value : Type uSource) :
    ValueRepresentation Value Value where
  represent value := value

instance valueRepresentationULift (Value : Type uSource) :
    ValueRepresentation Value (ULift.{uLift} Value) where
  represent := ULift.up

instance (priority := 1100) valueRepresentationTyUnit
    {Base : Type uSource} {interpret : Base → Type uTarget} :
    ValueRepresentation Unit (Ty.denote interpret (.unit : Ty Base)) where
  represent := ULift.up

instance (priority := 1100) valueRepresentationTyBool
    {Base : Type uSource} {interpret : Base → Type uTarget} :
    ValueRepresentation Bool (Ty.denote interpret (.bool : Ty Base)) where
  represent := ULift.up

instance (priority := 1100) valueRepresentationTyBase
    {Base : Type uSource} {interpret : Base → Type uTarget}
    {name : Base} {Source : Type*}
    [ValueRepresentation Source (interpret name)] :
    ValueRepresentation Source (Ty.denote interpret (.base name)) where
  represent :=
    (ValueRepresentation.represent : Source → interpret name)

instance (priority := 900) valueRepresentationProd
    {SourceLeft : Type uSource} {SourceRight : Type uTarget}
    {TargetLeft TargetRight : Type*}
    [ValueRepresentation SourceLeft TargetLeft]
    [ValueRepresentation SourceRight TargetRight] :
    ValueRepresentation (SourceLeft × SourceRight) (TargetLeft × TargetRight) where
  represent value :=
    (representValue value.1, representValue value.2)

instance (priority := 1100) valueRepresentationTyProd
    {Base : Type uSource} {interpret : Base → Type uTarget}
    {left right : Ty Base} {SourceLeft SourceRight : Type*}
    [ValueRepresentation SourceLeft (Ty.denote interpret left)]
    [ValueRepresentation SourceRight (Ty.denote interpret right)] :
    ValueRepresentation (SourceLeft × SourceRight)
      (Ty.denote interpret (.prod left right)) where
  represent value :=
    (representValue value.1, representValue value.2)

/-- Project a represented value back to the host-facing scheme type. -/
class ValueProjection (Source : Type uSource) (Target : Type uTarget) where
  project : Source → Target

/-- Use a projection inferred from the expected host-facing value type. -/
def projectValue
    {Source : Type uSource} {Target : Type uTarget}
    [ValueProjection Source Target] : Source → Target :=
  ValueProjection.project

instance valueProjectionIdentity (Value : Type uSource) :
    ValueProjection Value Value where
  project value := value

instance valueProjectionULift (Value : Type uSource) :
    ValueProjection (ULift.{uLift} Value) Value where
  project := ULift.down

instance (priority := 1100) valueProjectionTyBase
    {Base : Type uSource} {interpret : Base → Type uTarget}
    {name : Base} {Target : Type*}
    [ValueProjection (interpret name) Target] :
    ValueProjection (Ty.denote interpret (.base name)) Target where
  project :=
    (ValueProjection.project : interpret name → Target)

instance (priority := 900) valueProjectionProd
    {SourceLeft : Type uSource} {SourceRight : Type uTarget}
    {TargetLeft TargetRight : Type*}
    [ValueProjection SourceLeft TargetLeft]
    [ValueProjection SourceRight TargetRight] :
    ValueProjection (SourceLeft × SourceRight) (TargetLeft × TargetRight) where
  project value :=
    (projectValue value.1, projectValue value.2)

instance (priority := 1100) valueProjectionTyProd
    {Base : Type uSource} {interpret : Base → Type uTarget}
    {left right : Ty Base} {TargetLeft TargetRight : Type*}
    [ValueProjection (Ty.denote interpret left) TargetLeft]
    [ValueProjection (Ty.denote interpret right) TargetRight] :
    ValueProjection (Ty.denote interpret (.prod left right))
      (TargetLeft × TargetRight) where
  project value :=
    (projectValue value.1, projectValue value.2)

universe uCost uBase uValue uOp uHostInput uHostOutput

/--
Run a represented program at a host-facing boundary, inserting and removing
structural representations without exposing their `ULift` implementation.
-/
noncomputable def runCosted
    {M : CostModel.{uCost}}
    {Base : Type uBase} {interpret : Base → Type uValue}
    {S : Signature.{uBase, uOp} Base}
    (A : CostedAlgebra M interpret S)
    {Input Output : Ty Base} (program : Program interpret S Input Output)
    {HostInput : Type uHostInput} {HostOutput : Type uHostOutput}
    (input : HostInput)
    [ValueRepresentation HostInput (Ty.denote interpret Input)]
    [ValueProjection (Ty.denote interpret Output) HostOutput] :
    RandCosted M HostOutput :=
  RandCosted.map projectValue
    (Program.runCosted A program (representValue input))

/-
Typed smart constructors for first-order code.

Their expression arguments determine the primitive carrier types before Lean
searches for a signature embedding.  Each constructor immediately lowers to a
raw `Code.call`, so downstream semantics and complexity proofs continue to see
the trusted first-order syntax.
-/
namespace SmartCode

def sample
    {Base : Type uBase} {interpret : Base → Type uValue}
    {S : Signature.{uBase, uOp} Base}
    {context : List (Ty Base)} {Result : Ty Base}
    (sampleTy : Ty Base) (sampler : Sampler S sampleTy)
    (next : Code interpret S (sampleTy :: context) Result) :
    Code interpret S context Result :=
  .call sampler.operation .unit next

def unifSamp
    {Base : Type uBase} {interpret : Base → Type uValue}
    {S : Signature.{uBase, uOp} Base}
    {context : List (Ty Base)} {Result : Ty Base}
    (sampleTy : Ty Base)
    (next : Code interpret S (sampleTy :: context) Result)
    [Signature.Embedding (UniformSampleOperation.signature sampleTy) S] :
    Code interpret S context Result :=
  .call SmartOperation.unifSamp .unit next

def add
    {Base : Type uBase} {interpret : Base → Type uValue}
    {S : Signature.{uBase, uOp} Base}
    {context : List (Ty Base)} {Carrier Result : Ty Base}
    (left right : Expr interpret context Carrier)
    (next : Code interpret S (Carrier :: context) Result)
    [Signature.Embedding (AddOperation.signature Carrier) S] :
    Code interpret S context Result :=
  .call SmartOperation.add (.pair left right) next

def neg
    {Base : Type uBase} {interpret : Base → Type uValue}
    {S : Signature.{uBase, uOp} Base}
    {context : List (Ty Base)} {Carrier Result : Ty Base}
    (value : Expr interpret context Carrier)
    (next : Code interpret S (Carrier :: context) Result)
    [Signature.Embedding (NegOperation.signature Carrier) S] :
    Code interpret S context Result :=
  .call SmartOperation.neg value next

def sub
    {Base : Type uBase} {interpret : Base → Type uValue}
    {S : Signature.{uBase, uOp} Base}
    {context : List (Ty Base)} {Carrier Result : Ty Base}
    (left right : Expr interpret context Carrier)
    (next : Code interpret S (Carrier :: context) Result)
    [Signature.Embedding (SubOperation.signature Carrier) S] :
    Code interpret S context Result :=
  .call SmartOperation.sub (.pair left right) next

def smul
    {Base : Type uBase} {interpret : Base → Type uValue}
    {S : Signature.{uBase, uOp} Base}
    {context : List (Ty Base)} {Scalar Carrier Result : Ty Base}
    (scalar : Expr interpret context Scalar)
    (carrier : Expr interpret context Carrier)
    (next : Code interpret S (Carrier :: context) Result)
    [Signature.Embedding (SMulOperation.signature Scalar Carrier) S] :
    Code interpret S context Result :=
  .call SmartOperation.smul (.pair scalar carrier) next

def mul
    {Base : Type uBase} {interpret : Base → Type uValue}
    {S : Signature.{uBase, uOp} Base}
    {context : List (Ty Base)} {Value Result : Ty Base}
    (left right : Expr interpret context Value)
    (next : Code interpret S (Value :: context) Result)
    [Signature.Embedding (MulOperation.signature Value) S] :
    Code interpret S context Result :=
  .call SmartOperation.mul (.pair left right) next

end SmartCode

private def findName (target : Name) : List Name → Option Nat
  | [] => none
  | name :: names =>
      if target == name then some 0 else (findName target names).map Nat.succ

private inductive InputProjection where
  | fst
  | snd

private structure InputBinding where
  name : Name
  projection : List InputProjection

/-- Match `Ty.tuple`: the first input is `fst`, and later inputs live in `snd`. -/
private def inputBindings : List Name → List InputBinding
  | [] => []
  | [name] => [{ name, projection := [] }]
  | name :: next :: rest =>
      { name, projection := [.fst] } ::
        (inputBindings (next :: rest)).map fun binding =>
          { binding with projection := .snd :: binding.projection }

private def findInput (target : Name) : List InputBinding → Option (List InputProjection)
  | [] => none
  | binding :: bindings =>
      if target == binding.name then
        some binding.projection
      else
        findInput target bindings

private def firstDuplicate : List Name → Option Name
  | [] => none
  | name :: names =>
      if names.contains name then some name else firstDuplicate names

private def variableSyntax (index : Nat) : MacroM (TSyntax `term) := do
  let mut resultSyntax ← `(.here)
  for _ in [:index] do
    resultSyntax ← `(.there $resultSyntax)
  `(.var $resultSyntax)

private def inputSyntax
    (localCount : Nat) (projection : List InputProjection) :
    MacroM (TSyntax `term) := do
  let mut result ← variableSyntax localCount
  for step in projection do
    match step with
    | .fst => result ← `(.fst $result)
    | .snd => result ← `(.snd $result)
  pure result

private partial def expressionSyntax
    (locals : List Name) (inputs : List InputBinding)
    (expression : Syntax) : MacroM (TSyntax `term) := do
  if expression.isIdent then
    let name := expression.getId
    if let some index := findName name locals then
      return ← variableSyntax index
    if let some projection := findInput name inputs then
      return ← inputSyntax locals.length projection
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
      let product ← expressionSyntax locals inputs product
      `(.fst $product)
  | `(snd($product:term)) =>
      let product ← expressionSyntax locals inputs product
      `(.snd $product)
  | `(($left:term, $right:term)) =>
      let left ← expressionSyntax locals inputs left
      let right ← expressionSyntax locals inputs right
      `(.pair $left $right)
  | _ =>
      Macro.throwErrorAt expression
        "unsupported first-order expression"

private structure NormalizedExpression where
  bindings : List (TSyntax `doElem)
  expression : TSyntax `term
  deriving Inhabited

private structure NormalizedAction where
  bindings : List (TSyntax `doElem)
  action : TSyntax `term
  deriving Inhabited

/-
Normalize nested smart operations to fresh `let ←` bindings before the
trusted `Code` syntax is generated. Intermediate bindings remain ordinary
de Bruijn variables in the compiled program; no expression-valued operation or
additional core node is introduced.
-/
mutual
  private partial def normalizeExpression
      (expression : Syntax) : MacroM NormalizedExpression := do
    if let some normalized ← normalizeAction? expression then
      let result ← Lean.Elab.Term.mkFreshIdent expression
      let action := normalized.action
      let binding ← `(doElem| let $result:ident ← $action:term)
      return {
        bindings := normalized.bindings ++ [binding]
        expression := ⟨result.raw⟩
      }
    if expression.isIdent then
      return { bindings := [], expression := ⟨expression⟩ }
    match expression with
    | `(value($_value:term)) =>
        return { bindings := [], expression := ⟨expression⟩ }
    | `(fst($product:term)) => do
        let product ← normalizeExpression product
        let productExpression := product.expression
        let result ← `(fst($productExpression))
        return { bindings := product.bindings, expression := result }
    | `(snd($product:term)) => do
        let product ← normalizeExpression product
        let productExpression := product.expression
        let result ← `(snd($productExpression))
        return { bindings := product.bindings, expression := result }
    | `(($left:term, $right:term)) => do
        let left ← normalizeExpression left
        let right ← normalizeExpression right
        let leftExpression := left.expression
        let rightExpression := right.expression
        let result ← `(($leftExpression, $rightExpression))
        return {
          bindings := left.bindings ++ right.bindings
          expression := result
        }
    | _ =>
        if let some expanded ← expandMacro? expression then
          normalizeExpression expanded
        else
          return { bindings := [], expression := ⟨expression⟩ }

  private partial def normalizeAction?
      (action : Syntax) : MacroM (Option NormalizedAction) := do
    match action with
    | `(sample $_sampleTy:term $_sampler:term) =>
        return some { bindings := [], action := ⟨action⟩ }
    | `(unifSamp $_sampleTy:term) =>
        return some { bindings := [], action := ⟨action⟩ }
    | `($scalar:term • $carrier:term) => do
        let scalar ← normalizeExpression scalar
        let carrier ← normalizeExpression carrier
        let scalarExpression := scalar.expression
        let carrierExpression := carrier.expression
        let result ← `($scalarExpression • $carrierExpression)
        return some {
          bindings := scalar.bindings ++ carrier.bindings
          action := result
        }
    | `(smul $scalar:term $carrier:term) => do
        let scalar ← normalizeExpression scalar
        let carrier ← normalizeExpression carrier
        let scalarExpression := scalar.expression
        let carrierExpression := carrier.expression
        let result ← `(smul $scalarExpression $carrierExpression)
        return some {
          bindings := scalar.bindings ++ carrier.bindings
          action := result
        }
    | `($left:term + $right:term) => do
        let left ← normalizeExpression left
        let right ← normalizeExpression right
        let leftExpression := left.expression
        let rightExpression := right.expression
        let result ← `($leftExpression + $rightExpression)
        return some {
          bindings := left.bindings ++ right.bindings
          action := result
        }
    | `(add $left:term $right:term) => do
        let left ← normalizeExpression left
        let right ← normalizeExpression right
        let leftExpression := left.expression
        let rightExpression := right.expression
        let result ← `(add $leftExpression $rightExpression)
        return some {
          bindings := left.bindings ++ right.bindings
          action := result
        }
    | `($left:term - $right:term) => do
        let left ← normalizeExpression left
        let right ← normalizeExpression right
        let leftExpression := left.expression
        let rightExpression := right.expression
        let result ← `($leftExpression - $rightExpression)
        return some {
          bindings := left.bindings ++ right.bindings
          action := result
        }
    | `(sub $left:term $right:term) => do
        let left ← normalizeExpression left
        let right ← normalizeExpression right
        let leftExpression := left.expression
        let rightExpression := right.expression
        let result ← `(sub $leftExpression $rightExpression)
        return some {
          bindings := left.bindings ++ right.bindings
          action := result
        }
    | `(-$value:term) => do
        let value ← normalizeExpression value
        let valueExpression := value.expression
        let result ← `(-$valueExpression)
        return some { bindings := value.bindings, action := result }
    | `(neg $value:term) => do
        let value ← normalizeExpression value
        let valueExpression := value.expression
        let result ← `(neg $valueExpression)
        return some { bindings := value.bindings, action := result }
    | `($left:term * $right:term) => do
        let left ← normalizeExpression left
        let right ← normalizeExpression right
        let leftExpression := left.expression
        let rightExpression := right.expression
        let result ← `($leftExpression * $rightExpression)
        return some {
          bindings := left.bindings ++ right.bindings
          action := result
        }
    | `(mul $left:term $right:term) => do
        let left ← normalizeExpression left
        let right ← normalizeExpression right
        let leftExpression := left.expression
        let rightExpression := right.expression
        let result ← `(mul $leftExpression $rightExpression)
        return some {
          bindings := left.bindings ++ right.bindings
          action := result
        }
    | `(call $operation:term with $arguments:term) => do
        let arguments ← normalizeExpression arguments
        let argumentExpression := arguments.expression
        let result ← `(call $operation with $argumentExpression)
        return some { bindings := arguments.bindings, action := result }
    | _ =>
        if let some expanded ← expandMacro? action then
          normalizeAction? expanded
        else
          return none
end

private partial def normalizeCodeSyntax :
    List (TSyntax `doElem) → MacroM (List (TSyntax `doElem))
  | [] => pure []
  | element :: remaining => do
      let remaining ← normalizeCodeSyntax remaining
      match element with
      | `(doElem| let $name:ident ← $action:term) =>
          if let some normalized ← normalizeAction? action then
            let action := normalized.action
            let binding ← `(doElem| let $name:ident ← $action:term)
            pure (normalized.bindings ++ (binding :: remaining))
          else
            pure (element :: remaining)
      | `(doElem| let $name:ident := $value:term) => do
          let normalized ← normalizeExpression value
          unless normalized.bindings.isEmpty do
            Macro.throwErrorAt value
              "effectful first-order operations require `let name ← ...`"
          let value := normalized.expression
          let binding ← `(doElem| let $name:ident := $value:term)
          pure (binding :: remaining)
      | `(doElem| return $result:term) => do
          let normalized ← normalizeExpression result
          let result := normalized.expression
          let returnElement ← `(doElem| return $result:term)
          pure (normalized.bindings ++ (returnElement :: remaining))
      | _ =>
          pure (element :: remaining)

private partial def actionSyntax
    (locals : List Name) (inputs : List InputBinding)
    (action : Syntax) (next : TSyntax `term) : MacroM (TSyntax `term) := do
  match action with
  | `(sample $sampleTy:term $sampler:term) =>
      `(SmartCode.sample $sampleTy $sampler $next)
  | `(unifSamp $sampleTy:term) =>
      `(SmartCode.unifSamp $sampleTy $next)
  | `($scalar:term • $carrier:term) => do
      let scalar ← expressionSyntax locals inputs scalar
      let carrier ← expressionSyntax locals inputs carrier
      `(SmartCode.smul $scalar $carrier $next)
  | `(smul $scalar:term $carrier:term) => do
      let scalar ← expressionSyntax locals inputs scalar
      let carrier ← expressionSyntax locals inputs carrier
      `(SmartCode.smul $scalar $carrier $next)
  | `($left:term + $right:term) => do
      let left ← expressionSyntax locals inputs left
      let right ← expressionSyntax locals inputs right
      `(SmartCode.add $left $right $next)
  | `(add $left:term $right:term) => do
      let left ← expressionSyntax locals inputs left
      let right ← expressionSyntax locals inputs right
      `(SmartCode.add $left $right $next)
  | `($left:term - $right:term) => do
      let left ← expressionSyntax locals inputs left
      let right ← expressionSyntax locals inputs right
      `(SmartCode.sub $left $right $next)
  | `(sub $left:term $right:term) => do
      let left ← expressionSyntax locals inputs left
      let right ← expressionSyntax locals inputs right
      `(SmartCode.sub $left $right $next)
  | `(-$value:term) => do
      let value ← expressionSyntax locals inputs value
      `(SmartCode.neg $value $next)
  | `(neg $value:term) => do
      let value ← expressionSyntax locals inputs value
      `(SmartCode.neg $value $next)
  | `($left:term * $right:term) => do
      let left ← expressionSyntax locals inputs left
      let right ← expressionSyntax locals inputs right
      `(SmartCode.mul $left $right $next)
  | `(mul $left:term $right:term) => do
      let left ← expressionSyntax locals inputs left
      let right ← expressionSyntax locals inputs right
      `(SmartCode.mul $left $right $next)
  | `(call $operation:term with $arguments:term) => do
      let arguments ← expressionSyntax locals inputs arguments
      `(.call $operation $arguments $next)
  | _ =>
      if let some expanded ← expandMacro? action then
        actionSyntax locals inputs expanded next
      else
        Macro.throwErrorAt action
          "unsupported first-order operation; use a smart operation or `call operation with arguments`"

private partial def codeSyntax
    (locals : List Name) (inputs : List InputBinding) :
    List (TSyntax `doElem) → MacroM (TSyntax `term)
  | [] => Macro.throwError "first-order block must end with `return`"
  | element :: remaining =>
      match element with
      | `(doElem| let $name:ident ← $action:term) => do
          let next ← codeSyntax (name.getId :: locals) inputs remaining
          actionSyntax locals inputs action next
      | `(doElem| let $name:ident := $value:term) => do
          let value ← expressionSyntax locals inputs value
          let next ← codeSyntax (name.getId :: locals) inputs remaining
          `(.letPure $value $next)
      | `(doElem| return $result:term) => do
          unless remaining.isEmpty do
            Macro.throwErrorAt element
              "statements after a first-order `return` are unreachable"
          let result ← expressionSyntax locals inputs result
          `(.ret $result)
      | _ =>
          Macro.throwErrorAt element
            "unsupported first-order statement"

macro_rules
  | `(first_order $input:ident do $sequence:doSeq) => do
      let elements := Lean.Parser.Term.getDoElems sequence
      let elements ← normalizeCodeSyntax elements.toList
      codeSyntax [] (inputBindings [input.getId]) elements
  | `(first_order ($inputs:ident,*) do $sequence:doSeq) => do
      let names := inputs.getElems.toList.map (·.getId)
      if let some duplicate := firstDuplicate names then
        Macro.throwError s!"duplicate first-order input name `{duplicate}`"
      let elements := Lean.Parser.Term.getDoElems sequence
      let elements ← normalizeCodeSyntax elements.toList
      codeSyntax [] (inputBindings names) elements

end Builder

end CryptoFirstOrder

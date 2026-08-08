import CryptoLib.Program.Transform.Sequencing

namespace CryptoLib.Program

open CryptoLib.Core.Infrastructure.Computation.Cost

universe uCost uBase uValue uSourceOp uMiddleOp uTargetOp

/--
A typed, first-order handler from a source primitive signature to a target
signature. Each source operation is implemented by closed first-order target
code with one distinguished argument input.
-/
structure Handler
    {Base : Type uBase} (interpret : Base → Type uValue)
    (source : Signature.{uBase, uSourceOp} Base)
    (target : Signature.{uBase, uTargetOp} Base) where
  body : ∀ {Args Result},
    source.Op Args Result → Procedure interpret target Args Result

namespace Handler

/-- Inline one handled operation at a target-code call site. -/
def inline
    {Base : Type uBase} {interpret : Base → Type uValue}
    {source : Signature.{uBase, uSourceOp} Base}
    {target : Signature.{uBase, uTargetOp} Base}
    (handler : Handler interpret source target)
    {Args Result : Ty Base} (operation : source.Op Args Result)
    {context : List (Ty Base)} (args : Expr interpret context Args) :
    Code interpret target context Result :=
  (handler.body operation).body.subst (Sub.single args)

end Handler

namespace Code

/-- Compile every source primitive call to its first-order handler body. -/
def handle
    {Base : Type uBase} {interpret : Base → Type uValue}
    {source : Signature.{uBase, uSourceOp} Base}
    {target : Signature.{uBase, uTargetOp} Base}
    (handler : Handler interpret source target) :
    {context : List (Ty Base)} → {result : Ty Base} →
      Code interpret source context result →
      Code interpret target context result
  | _, _, .ret value => .ret value
  | _, _, .letPure value next => .letPure value (next.handle handler)
  | _, _, .call operation args next =>
      Code.seq (handler.inline operation args) (next.handle handler)
  | _, _, .branch condition thenCode elseCode =>
      .branch condition (thenCode.handle handler) (elseCode.handle handler)

end Code

namespace Procedure

/-- Compile a procedure by handling every primitive call in its body. -/
def handle
    {Base : Type uBase} {interpret : Base → Type uValue}
    {source : Signature.{uBase, uSourceOp} Base}
    {target : Signature.{uBase, uTargetOp} Base}
    (handler : Handler interpret source target)
    {input output : Ty Base}
    (procedure : Procedure interpret source input output) :
    Procedure interpret target input output :=
  ⟨procedure.body.handle handler⟩

end Procedure

namespace Handler

/-- The identity handler implements each operation by one identical call. -/
def id
    {Base : Type uBase} {interpret : Base → Type uValue}
    (signature : Signature.{uBase, uSourceOp} Base) :
    Handler interpret signature signature where
  body operation :=
    ⟨Code.call operation (.var .here) (.ret (.var .here))⟩

/--
Compose handlers by compiling every body of `first` with `second`. Thus
`second.comp first` handles source operations through the middle signature and
then through the target signature.
-/
def comp
    {Base : Type uBase} {interpret : Base → Type uValue}
    {source : Signature.{uBase, uSourceOp} Base}
    {middle : Signature.{uBase, uMiddleOp} Base}
    {target : Signature.{uBase, uTargetOp} Base}
    (second : Handler interpret middle target)
    (first : Handler interpret source middle) :
    Handler interpret source target where
  body operation := (first.body operation).handle second

/--
The exact source algebra induced by executing handler bodies under a target
algebra.
-/
noncomputable def inducedAlgebra
    {M : CostModel.{uCost}}
    {Base : Type uBase} {interpret : Base → Type uValue}
    {source : Signature.{uBase, uSourceOp} Base}
    {target : Signature.{uBase, uTargetOp} Base}
    (handler : Handler interpret source target)
    (targetAlgebra : CostedAlgebra M interpret target) :
    CostedAlgebra M interpret source where
  exec operation args :=
    Procedure.runCosted targetAlgebra (handler.body operation) args

end Handler

end CryptoLib.Program

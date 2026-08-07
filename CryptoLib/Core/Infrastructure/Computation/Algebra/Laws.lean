import CryptoLib.Core.Infrastructure.Computation.Algebra.Handler

namespace CryptoLib.Core.Infrastructure.Computation.Algebra

open CryptoLib.Core.Infrastructure.Computation.Cost

universe uCost uResult uOp uLeftOp uRightOp

/--
A mathematical, cost-erased specification for one exact algebra handler.

`semantics` is specification data only. Execution always uses
`CostedAlgebra.exec`, and ordinary semantics is obtained by erasing its costs.
-/
structure AlgebraLaws
    {M : CostModel.{uCost}}
    {S : Signature.{uResult, uOp}}
    (A : CostedAlgebra M S) where
  semantics : {Result : Type uResult} → S.Op Result → PMF Result
  exec_spec :
    ∀ {Result : Type uResult} (operation : S.Op Result),
      RandCosted.valueDist (A.exec operation) = semantics operation

namespace AlgebraLaws

/-- Combine mathematical specifications for a disjoint union of handlers. -/
def sum
    {M : CostModel.{uCost}}
    {left : Signature.{uResult, uLeftOp}}
    {right : Signature.{uResult, uRightOp}}
    {leftAlgebra : CostedAlgebra M left}
    {rightAlgebra : CostedAlgebra M right}
    (leftLaws : AlgebraLaws leftAlgebra)
    (rightLaws : AlgebraLaws rightAlgebra) :
    AlgebraLaws (CostedAlgebra.sum leftAlgebra rightAlgebra) where
  semantics operation :=
    match operation with
    | .inl leftOperation => leftLaws.semantics leftOperation
    | .inr rightOperation => rightLaws.semantics rightOperation
  exec_spec operation := by
    cases operation with
    | inl leftOperation => exact leftLaws.exec_spec leftOperation
    | inr rightOperation => exact rightLaws.exec_spec rightOperation

end AlgebraLaws

end CryptoLib.Core.Infrastructure.Computation.Algebra

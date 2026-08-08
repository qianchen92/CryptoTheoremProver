import CryptoLib.Algebra.Generic.Handler

namespace CryptoLib.Algebra.Generic

open CryptoLib.Core.Infrastructure.Computation.Cost

universe uCost uResult uOp uLeftOp uRightOp

/--
Independent per-operation upper bounds for one exact algebra handler.

The exact resource annotation remains solely in `CostedAlgebra.exec`; several
different certificates may bound the same handler.
-/
structure OperationBounds
    {M : CostModel.{uCost}}
    {S : Signature.{uResult, uOp}}
    (A : CostedAlgebra M S) where
  budget : {Result : Type uResult} → S.Op Result → M.Cost
  cost_le :
    ∀ {Result : Type uResult} (operation : S.Op Result)
      (result : Costed M Result),
      result ∈ (A.exec operation).support →
        M.instPartialOrder.le result.cost (budget operation)

namespace OperationBounds

/-- Combine resource certificates for a disjoint union of handlers. -/
def sum
    {M : CostModel.{uCost}}
    {left : Signature.{uResult, uLeftOp}}
    {right : Signature.{uResult, uRightOp}}
    {leftAlgebra : CostedAlgebra M left}
    {rightAlgebra : CostedAlgebra M right}
    (leftBounds : OperationBounds leftAlgebra)
    (rightBounds : OperationBounds rightAlgebra) :
    OperationBounds (CostedAlgebra.sum leftAlgebra rightAlgebra) where
  budget operation :=
    match operation with
    | .inl leftOperation => leftBounds.budget leftOperation
    | .inr rightOperation => rightBounds.budget rightOperation
  cost_le operation result hresult := by
    cases operation with
    | inl leftOperation =>
        exact leftBounds.cost_le leftOperation result hresult
    | inr rightOperation =>
        exact rightBounds.cost_le rightOperation result hresult

end OperationBounds

end CryptoLib.Algebra.Generic

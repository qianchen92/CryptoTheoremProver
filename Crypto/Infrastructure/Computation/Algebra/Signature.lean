import Crypto.Infrastructure.Computation.Cost.Distribution

namespace Crypto.Infrastructure.Computation.Algebra

open Crypto.Infrastructure.Computation.Cost

universe uCost uResult uOp uLeftOp uRightOp

/--
A heterogeneous signature of typed primitive operations.

An operation is indexed by the type of value that it returns.  This permits one
program to use several carrier types, samplers, and dependent public-parameter
families without adding unused fields to a monolithic algebra record.
-/
structure Signature where
  Op : (Result : Type uResult) → Type uOp

namespace Signature

/-- The disjoint union of two typed primitive signatures. -/
def sum
    (left : Signature.{uResult, uLeftOp})
    (right : Signature.{uResult, uRightOp}) :
    Signature.{uResult, max uLeftOp uRightOp} where
  Op Result := Sum (left.Op Result) (right.Op Result)

end Signature

/--
The single authoritative exact interpreter for a primitive signature.

Mathematical specifications and resource bounds are deliberately separate from
this executable handler.
-/
structure CostedAlgebra
    (M : CostModel.{uCost}) (S : Signature.{uResult, uOp}) where
  exec : {Result : Type uResult} → S.Op Result → RandCostedT M Result

namespace CostedAlgebra

/-- Combine exact handlers for a disjoint union of primitive signatures. -/
def sum
    {M : CostModel.{uCost}}
    {left : Signature.{uResult, uLeftOp}}
    {right : Signature.{uResult, uRightOp}}
    (leftAlgebra : CostedAlgebra M left)
    (rightAlgebra : CostedAlgebra M right) :
    CostedAlgebra M (Signature.sum left right) where
  exec operation :=
    match operation with
    | .inl leftOperation => leftAlgebra.exec leftOperation
    | .inr rightOperation => rightAlgebra.exec rightOperation

end CostedAlgebra

/--
A mathematical, cost-erased specification for an exact algebra handler.

`semantics` is a specification only: program execution always uses
`CostedAlgebra.exec`, and its ordinary semantics is obtained by erasing costs.
-/
structure AlgebraLaws
    {M : CostModel.{uCost}}
    {S : Signature.{uResult, uOp}}
    (A : CostedAlgebra M S) where
  semantics : {Result : Type uResult} → S.Op Result → PMF Result
  exec_spec :
    ∀ {Result : Type uResult} (operation : S.Op Result),
      RandCostedT.valueDist (A.exec operation) = semantics operation

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
      (result : CostedT M Result),
      result ∈ (A.exec operation).support →
        @LE.le M.Cost M.instPartialOrder.toLE result.cost (budget operation)

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

end Crypto.Infrastructure.Computation.Algebra

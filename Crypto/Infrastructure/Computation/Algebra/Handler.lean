import Crypto.Infrastructure.Computation.Algebra.Signature
import Crypto.Infrastructure.Computation.Cost.Randomized

namespace Crypto.Infrastructure.Computation.Algebra

open Crypto.Infrastructure.Computation.Cost

universe uCost uResult uOp uLeftOp uRightOp

/--
The single authoritative exact interpreter for a typed primitive signature.

Mathematical specifications and resource bounds live in separate layers; this
record contains only executable joint value/cost semantics.
-/
structure CostedAlgebra
    (M : CostModel.{uCost}) (S : Signature.{uResult, uOp}) where
  exec : {Result : Type uResult} → S.Op Result → RandCosted M Result

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

end Crypto.Infrastructure.Computation.Algebra

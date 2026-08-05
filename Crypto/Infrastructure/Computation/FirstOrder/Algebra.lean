import Crypto.Infrastructure.Computation.Cost.Randomized
import Crypto.Infrastructure.Computation.FirstOrder.Signature

namespace Crypto.Infrastructure.Computation.FirstOrder

open Crypto.Infrastructure.Computation.Cost

universe uCost uBase uValue uOp uLeftOp uRightOp

/-- The exact cost-aware interpreter for a first-order primitive signature. -/
structure CostedAlgebra
    (M : CostModel.{uCost})
    {Base : Type uBase} (interpret : Base → Type uValue)
    (S : Signature.{uBase, uOp} Base) where
  exec : {Args Result : Ty Base} →
    S.Op Args Result →
    Ty.denote interpret Args →
    RandCosted M (Ty.denote interpret Result)

namespace CostedAlgebra

/-- Combine exact handlers for a disjoint union of first-order signatures. -/
noncomputable def sum
    {M : CostModel.{uCost}}
    {Base : Type uBase} {interpret : Base → Type uValue}
    {left : Signature.{uBase, uLeftOp} Base}
    {right : Signature.{uBase, uRightOp} Base}
    (leftAlgebra : CostedAlgebra M interpret left)
    (rightAlgebra : CostedAlgebra M interpret right) :
    CostedAlgebra M interpret (Signature.sum left right) where
  exec operation args :=
    match operation with
    | .inl leftOperation => leftAlgebra.exec leftOperation args
    | .inr rightOperation => rightAlgebra.exec rightOperation args

end CostedAlgebra

end Crypto.Infrastructure.Computation.FirstOrder

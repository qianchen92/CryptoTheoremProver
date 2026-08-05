import Crypto.Infrastructure.Computation.FirstOrder.Type

namespace Crypto.Infrastructure.Computation.FirstOrder

universe uBase uOp uLeftOp uRightOp

/--
A first-order signature whose operations declare both an argument type and a
result type. Operation values contain no runtime arguments; arguments are
supplied by first-order expressions at call sites.
-/
structure Signature (Base : Type uBase) where
  Op : (Args Result : Ty Base) → Type uOp

namespace Signature

/-- The disjoint union of two first-order primitive signatures. -/
def sum
    {Base : Type uBase}
    (left : Signature.{uBase, uLeftOp} Base)
    (right : Signature.{uBase, uRightOp} Base) :
    Signature.{uBase, max uLeftOp uRightOp} Base where
  Op Args Result := Sum (left.Op Args Result) (right.Op Args Result)

end Signature

end Crypto.Infrastructure.Computation.FirstOrder

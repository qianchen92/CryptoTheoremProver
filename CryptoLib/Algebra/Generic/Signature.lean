namespace CryptoLib.Algebra.Generic

universe uResult uOp uLeftOp uRightOp

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

end CryptoLib.Algebra.Generic

import CryptoLib.Core.Infrastructure.Computation.Algebra.Handler

namespace CryptoLib.Core.Infrastructure.Computation

open CryptoLib.Core.Infrastructure.Computation.Algebra
open CryptoLib.Core.Infrastructure.Computation.Cost

universe uCost uResult uOp uIn

namespace Program

/-- Reified program code after the external input has been supplied. -/
inductive Code
    {M : CostModel.{uCost}}
    {S : Signature.{uResult, uOp}}
    (A : CostedAlgebra M S) :
    Type uResult → Type (max uResult uOp + 1) where
  | pure {Result : Type uResult} : Result → Code A Result
  | bind {First Result : Type uResult} :
      Code A First → (First → Code A Result) → Code A Result
  | call {Result : Type uResult} : S.Op Result → Code A Result
  | branch {Result : Type uResult} :
      Bool → Code A Result → Code A Result → Code A Result

end Program

/--
A typed, higher-order program over one explicit cost-aware primitive algebra.

`Input` is represented at the outer boundary; the reified body contains only
pure values, sequencing, primitive calls, and conditionals. Primitive calls
are heterogeneous because their signature is indexed by the result type.
-/
structure Program
    {M : CostModel.{uCost}}
    {S : Signature.{uResult, uOp}}
    (A : CostedAlgebra M S)
    (Input : Type uIn) (Output : Type uResult) where
  body : Input → Program.Code A Output

namespace Program

namespace Code

variable
    {M : CostModel.{uCost}}
    {S : Signature.{uResult, uOp}}
    {A : CostedAlgebra M S}

instance : Monad (Code A) where
  pure := Code.pure
  bind := Code.bind

end Code

end Program

end CryptoLib.Core.Infrastructure.Computation

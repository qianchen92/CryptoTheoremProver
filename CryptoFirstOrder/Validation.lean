import CryptoFirstOrder.Operation

namespace CryptoFirstOrder

open Crypto.Infrastructure.Computation.Cost

universe uCost uBase uValue

/--
Structural evidence that an algebra is assembled only from the built-in
first-order primitives. The Lean typeclass operations are the deliberately
exposed bottom-algebra boundary; uniform sampling itself is fixed by the
library rather than supplied as an arbitrary distribution.
-/
inductive ValidAlgebra
    (M : CostModel.{uCost})
    {Base : Type uBase} (interpret : Base → Type uValue) :
    {S : Signature.{uBase, uBase} Base} →
    CostedAlgebra M interpret S → Prop where
  | tick (Label : Type uBase) (cost : Label → M.Cost) :
      ValidAlgebra M interpret
        (TickOperation.algebra M interpret Label cost)
  | parameterizedAdd (parameter carrier : Ty Base)
      [ParameterizedAdd
        (Ty.denote interpret parameter) (Ty.denote interpret carrier)]
      (cost : Ty.denote interpret parameter → M.Cost) :
      ValidAlgebra M interpret
        (ParameterizedAddOperation.algebra M interpret parameter carrier cost)
  | add (carrier : Ty Base) [Add (Ty.denote interpret carrier)]
      (cost : M.Cost) :
      ValidAlgebra M interpret (AddOperation.algebra M interpret carrier cost)
  | neg (carrier : Ty Base) [Neg (Ty.denote interpret carrier)]
      (cost : M.Cost) :
      ValidAlgebra M interpret (NegOperation.algebra M interpret carrier cost)
  | sub (carrier : Ty Base) [Sub (Ty.denote interpret carrier)]
      (cost : M.Cost) :
      ValidAlgebra M interpret (SubOperation.algebra M interpret carrier cost)
  | smul (scalar carrier : Ty Base)
      [SMul (Ty.denote interpret scalar) (Ty.denote interpret carrier)]
      (cost : M.Cost) :
      ValidAlgebra M interpret
        (SMulOperation.algebra M interpret scalar carrier cost)
  | mul (value : Ty Base) [Mul (Ty.denote interpret value)]
      (cost : M.Cost) :
      ValidAlgebra M interpret (MulOperation.algebra M interpret value cost)
  | uniformSample (sample : Ty Base)
      [Fintype (Ty.denote interpret sample)]
      [Nonempty (Ty.denote interpret sample)]
      (cost : M.Cost) :
      ValidAlgebra M interpret
        (UniformSampleOperation.algebra M interpret sample cost)
  | sum
      {left right : Signature.{uBase, uBase} Base}
      {leftAlgebra : CostedAlgebra M interpret left}
      {rightAlgebra : CostedAlgebra M interpret right} :
      ValidAlgebra M interpret leftAlgebra →
      ValidAlgebra M interpret rightAlgebra →
      ValidAlgebra M interpret
        (CostedAlgebra.sum leftAlgebra rightAlgebra)

end CryptoFirstOrder

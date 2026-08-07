import CryptoLib.Program.Operation

namespace CryptoLib.Program.Algebra.AdditiveGroup

open CryptoLib.Core.Infrastructure.Computation.Cost
open CryptoLib.Program
open scoped CryptoLib.Program

universe uCost uCarrier

/-- The single carrier exposed by an additive-group first-order adapter. -/
inductive Base where
  | carrier
  deriving DecidableEq

abbrev carrierTy : Ty Base :=
  .base .carrier

/-- Interpret the adapter's carrier using the supplied native type. -/
abbrev interpret (Carrier : Type uCarrier) : Base → Type uCarrier
  | .carrier => Carrier

/-- Uniform sampling, addition, and negation over one carrier. -/
inductive Operation : Ty Base → Ty Base → Type where
  | sample : Operation .unit carrierTy
  | add : Operation (carrierTy ×ₜ carrierTy) carrierTy
  | neg : Operation carrierTy carrierTy

def signature : Signature Base where
  Op := Operation

instance uniformSampleEmbedding :
    Signature.Embedding
      (UniformSampleOperation.signature carrierTy) signature where
  inject operation := by
    cases operation
    exact .sample

instance addEmbedding :
    Signature.Embedding (AddOperation.signature carrierTy) signature where
  inject operation := by
    cases operation
    exact .add

instance negEmbedding :
    Signature.Embedding (NegOperation.signature carrierTy) signature where
  inject operation := by
    cases operation
    exact .neg

/-- Exact native computations used by the reusable first-order adapter. -/
structure Handler
    (M : CostModel.{uCost}) (Carrier : Type uCarrier) where
  sample : RandCosted M Carrier
  add : Carrier → Carrier → RandCosted M Carrier
  neg : Carrier → RandCosted M Carrier

/--
Expose one authoritative native handler through the fixed first-order
additive-group signature.
-/
noncomputable def algebra
    {M : CostModel.{uCost}} {Carrier : Type uCarrier}
    (handler : Handler M Carrier) :
    CostedAlgebra M (interpret Carrier) signature where
  exec operation args :=
    match operation with
    | .sample => handler.sample
    | .add => handler.add args.1 args.2
    | .neg => handler.neg args

end CryptoLib.Program.Algebra.AdditiveGroup

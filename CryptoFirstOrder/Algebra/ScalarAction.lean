import CryptoFirstOrder.Operation

namespace CryptoFirstOrder.Algebra.ScalarAction

open Crypto.Infrastructure.Computation.Cost
open CryptoFirstOrder
open scoped CryptoFirstOrder

universe uCost uScalar uCarrier

/-- Scalar and carrier names for a two-sorted first-order adapter. -/
inductive Base where
  | scalar
  | carrier
  deriving DecidableEq

abbrev scalarTy : Ty Base :=
  .base .scalar

abbrev carrierTy : Ty Base :=
  .base .carrier

/--
Interpret two possibly different native universes in one first-order value
universe. The lifts remain an internal representation boundary.
-/
abbrev interpret
    (Scalar : Type uScalar) (Carrier : Type uCarrier) :
    Base → Type (max uScalar uCarrier)
  | .scalar => ULift.{uCarrier} Scalar
  | .carrier => ULift.{uScalar} Carrier

abbrev ScalarValue (Scalar : Type uScalar) (Carrier : Type uCarrier) :=
  Ty.denote (interpret Scalar Carrier) scalarTy

abbrev CarrierValue (Scalar : Type uScalar) (Carrier : Type uCarrier) :=
  Ty.denote (interpret Scalar Carrier) carrierTy

abbrev liftScalar
    (Scalar : Type uScalar) (Carrier : Type uCarrier) :
    Scalar → ScalarValue Scalar Carrier :=
  ULift.up

abbrev liftCarrier
    (Scalar : Type uScalar) (Carrier : Type uCarrier) :
    Carrier → CarrierValue Scalar Carrier :=
  ULift.up

abbrev carrierScalarPairDown
    (Scalar : Type uScalar) (Carrier : Type uCarrier) :
    CarrierValue Scalar Carrier × ScalarValue Scalar Carrier → Carrier × Scalar :=
  fun result => (result.1.down, result.2.down)

abbrev carrierPairDown
    (Scalar : Type uScalar) (Carrier : Type uCarrier) :
    CarrierValue Scalar Carrier × CarrierValue Scalar Carrier → Carrier × Carrier :=
  fun result => (result.1.down, result.2.down)

/-- Uniform scalar sampling and the carrier operations used by ElGamal-like code. -/
inductive Operation : Ty Base → Ty Base → Type where
  | sampleScalar : Operation .unit scalarTy
  | smul : Operation (scalarTy ×ₜ carrierTy) carrierTy
  | add : Operation (carrierTy ×ₜ carrierTy) carrierTy
  | sub : Operation (carrierTy ×ₜ carrierTy) carrierTy

def signature : Signature Base where
  Op := Operation

instance uniformSampleEmbedding :
    Signature.Embedding
      (UniformSampleOperation.signature scalarTy) signature where
  inject operation := by
    cases operation
    exact .sampleScalar

instance smulEmbedding :
    Signature.Embedding
      (SMulOperation.signature scalarTy carrierTy) signature where
  inject operation := by
    cases operation
    exact .smul

instance addEmbedding :
    Signature.Embedding (AddOperation.signature carrierTy) signature where
  inject operation := by
    cases operation
    exact .add

instance subEmbedding :
    Signature.Embedding (SubOperation.signature carrierTy) signature where
  inject operation := by
    cases operation
    exact .sub

/-- Exact native computations used by the reusable scalar-action adapter. -/
structure Handler
    (M : CostModel.{uCost})
    (Scalar : Type uScalar) (Carrier : Type uCarrier) where
  sampleScalar : RandCosted M (ScalarValue Scalar Carrier)
  smul : Scalar → Carrier → RandCosted M (CarrierValue Scalar Carrier)
  add : Carrier → Carrier → RandCosted M (CarrierValue Scalar Carrier)
  sub : Carrier → Carrier → RandCosted M (CarrierValue Scalar Carrier)

/--
Expose one authoritative native handler through the fixed first-order
scalar-action signature.
-/
noncomputable def algebra
    {M : CostModel.{uCost}}
    {Scalar : Type uScalar} {Carrier : Type uCarrier}
    (handler : Handler M Scalar Carrier) :
    CostedAlgebra M (interpret Scalar Carrier) signature where
  exec operation args :=
    match operation with
    | .sampleScalar => handler.sampleScalar
    | .smul => handler.smul args.1.down args.2.down
    | .add => handler.add args.1.down args.2.down
    | .sub => handler.sub args.1.down args.2.down

end CryptoFirstOrder.Algebra.ScalarAction

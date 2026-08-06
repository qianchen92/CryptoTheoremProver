import CryptoConstruction.Primitive.Encryption.AsymmetricEncryption.ElGamal.Properties.INDCPA.Proof.ReductionClosure

/-! # Public operational-closure lemma for the DDH reduction -/

namespace CryptoConstruction.Primitive.Encryption.AsymmetricEncryption.ElGamal

open Crypto.Infrastructure.Computation.Cost

universe uCost uParameter uScalar uGroup

variable
    {M : CostModel.{uCost}}
    {measure : NatMeasure M}
    {Parameter : Type uParameter}
    {Scalar : Type uScalar}
    {Carrier : Type uGroup}

/-- Explicit polynomial efficiency data closes the operational reduction. -/
theorem ddhReductionPPTClosed
    (F : Family M Parameter Scalar Carrier)
    (efficiency : ReductionEfficiencyCertificate measure F) :
    DDHReductionPPTClosed measure F := by
  exact ddhReductionPPTClosed_proof F efficiency

end CryptoConstruction.Primitive.Encryption.AsymmetricEncryption.ElGamal

import CryptoLib.Instantiation.Primitive.Encryption.AsymmetricEncryption.ElGamal.Properties.INDCPA.Proof.ReductionClosure

/-! # Public operational-closure lemma for the DDH reduction -/

namespace CryptoLib.Instantiation.Primitive.Encryption.AsymmetricEncryption.ElGamal

open CryptoLib.Core.Infrastructure.Computation.Cost

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

end CryptoLib.Instantiation.Primitive.Encryption.AsymmetricEncryption.ElGamal

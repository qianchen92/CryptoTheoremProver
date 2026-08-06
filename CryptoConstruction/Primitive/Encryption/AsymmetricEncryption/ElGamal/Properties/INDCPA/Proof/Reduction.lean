import CryptoConstruction.Primitive.Encryption.AsymmetricEncryption.ElGamal.Properties.INDCPA.Lemma.ReductionClosure

/-! # DDH indistinguishability of one ElGamal hybrid transition -/

namespace CryptoConstruction.Primitive.Encryption.AsymmetricEncryption.ElGamal

open Crypto.Infrastructure.Computation.Cost
open Crypto.Primitive.Encryption.AsymmetricEncryption

universe uCost uParameter uScalar uGroup

variable
    {M : CostModel.{uCost}}
    {measure : NatMeasure M}
    {Parameter : Type uParameter}
    {Scalar : Type uScalar}
    {Carrier : Type uGroup}

/-- A certified semantic reduction turns the DDH assumption into one adjacent
ElGamal hybrid transition. -/
theorem ddhReduction_indistinguishable
    (F : Family M Parameter Scalar Carrier)
    (adversary : Crypto.Infrastructure.Complexity.PPTOracleMachine M measure
      (PublicInput Parameter (PublicKey (Carrier := Carrier)))
      (fun _sec _input => Bool)
      (indCPAOracleSpec (Message (Carrier := Carrier)) (Ciphertext (Carrier := Carrier))))
    (rightMessage : Bool)
    (hDDH : Crypto.Assumption.DL.DDH.Assumption M measure F)
    (certificate : DDHReductionCertificate F measure adversary rightMessage) :
    Crypto.Infrastructure.GameBased.Indistinguishable
      (realReductionGame F adversary.toOracleMachine rightMessage)
      (randomReductionGame F adversary.toOracleMachine rightMessage) := by
  have hProblem := hDDH
    (concreteDDHReductionPPT F certificate.efficiency adversary rightMessage)
  exact
    (Crypto.Infrastructure.GameBased.Indistinguishable.of_eq
      certificate.realGame_eq.symm).trans
      (hProblem.trans
        (Crypto.Infrastructure.GameBased.Indistinguishable.of_eq
          certificate.randomGame_eq))

end CryptoConstruction.Primitive.Encryption.AsymmetricEncryption.ElGamal

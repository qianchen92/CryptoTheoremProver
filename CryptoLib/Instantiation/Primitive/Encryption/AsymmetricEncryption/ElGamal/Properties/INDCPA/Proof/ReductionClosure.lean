import CryptoLib.Instantiation.Primitive.Encryption.AsymmetricEncryption.ElGamal.Properties.INDCPA.Proof.ReductionGame

/-! # Canonical reduction certificates and compiler closure -/

namespace CryptoLib.Instantiation.Primitive.Encryption.AsymmetricEncryption.ElGamal

open CryptoLib.Core.Infrastructure.Computation.Cost
open CryptoLib.Core.Infrastructure.Computation
open CryptoLib.Core.Infrastructure.Computation.Oracle
open CryptoLib.Core.Primitive.Encryption.AsymmetricEncryption

universe uCost uParameter uScalar uGroup

variable
    {M : CostModel.{uCost}}
    {measure : NatMeasure M}
    {Parameter : Type uParameter}
    {Scalar : Type uScalar}
    {Carrier : Type uGroup}

/--
Compatibility certificate for the concrete compiler output.  Unlike the old
existential interface, it contains no arbitrary machine: both games are fixed
to `concreteDDHReductionPPT` built from its stored efficiency certificate.
-/
structure DDHReductionCertificate
    (F : Family M Parameter Scalar Carrier)
    (measure : NatMeasure M)
    (adversary : CryptoLib.Core.Infrastructure.Complexity.PPTOracleMachine M measure
      (PublicInput Parameter (PublicKey (Carrier := Carrier)))
      (fun _sec _input => Bool)
      (indCPAOracleSpec
        (Message (Carrier := Carrier)) (Ciphertext (Carrier := Carrier))))
    (rightMessage : Bool) where
  efficiency : ReductionEfficiencyCertificate measure F
  realGame_eq :
    CryptoLib.Core.Infrastructure.GameBased.Distinguishing.securityGame
        (CryptoLib.Core.Assumption.DL.DDH.realSample F)
        (concreteDDHReductionPPT F efficiency adversary
          rightMessage).toProbabilisticMachine =
      realReductionGame F adversary.toOracleMachine rightMessage
  randomGame_eq :
    CryptoLib.Core.Infrastructure.GameBased.Distinguishing.securityGame
        (CryptoLib.Core.Assumption.DL.DDH.randomSample F)
        (concreteDDHReductionPPT F efficiency adversary
          rightMessage).toProbabilisticMachine =
      randomReductionGame F adversary.toOracleMachine rightMessage

/--
The operational closure obligation for the standard black-box reduction:
every admitted PPT IND-CPA oracle adversary can be compiled, for either
challenge message, to an admitted PPT DDH distinguisher with the semantic
distribution above.
-/
def DDHReductionPPTClosed
    (measure : NatMeasure M)
    (F : Family M Parameter Scalar Carrier) : Prop :=
  ∀ adversary : CryptoLib.Core.Infrastructure.Complexity.PPTOracleMachine
      M measure
      (PublicInput Parameter (PublicKey (Carrier := Carrier)))
      (fun _sec _input => Bool)
      (indCPAOracleSpec
        (Message (Carrier := Carrier)) (Ciphertext (Carrier := Carrier))),
    ∀ rightMessage : Bool,
      Nonempty (DDHReductionCertificate F measure
        adversary rightMessage)

/-- Canonical certificate produced by the concrete compiler. -/
noncomputable def ddhReductionCertificate
    (F : Family M Parameter Scalar Carrier)
    (efficiency : ReductionEfficiencyCertificate measure F)
    (adversary : CryptoLib.Core.Infrastructure.Complexity.PPTOracleMachine
      M measure
      (PublicInput Parameter (PublicKey (Carrier := Carrier)))
      (fun _sec _input => Bool)
      (indCPAOracleSpec
        (Message (Carrier := Carrier)) (Ciphertext (Carrier := Carrier))))
    (rightMessage : Bool) :
    DDHReductionCertificate F measure adversary rightMessage where
  efficiency := efficiency
  realGame_eq := concreteRealReductionGame_eq F efficiency adversary rightMessage
  randomGame_eq :=
    concreteRandomReductionGame_eq F efficiency adversary rightMessage

/-- Proof that explicit efficiency data closes the operational reduction. -/
theorem ddhReductionPPTClosed_proof
    (F : Family M Parameter Scalar Carrier)
    (efficiency : ReductionEfficiencyCertificate measure F) :
    DDHReductionPPTClosed measure F := by
  intro adversary rightMessage
  exact ⟨ddhReductionCertificate F efficiency adversary rightMessage⟩

end CryptoLib.Instantiation.Primitive.Encryption.AsymmetricEncryption.ElGamal

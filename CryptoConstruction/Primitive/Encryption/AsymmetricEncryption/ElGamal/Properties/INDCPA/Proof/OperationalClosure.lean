import CryptoConstruction.Primitive.Encryption.AsymmetricEncryption.ElGamal.Properties.INDCPA.Lemma.Efficiency

/-! # PPT operational closure of the concrete DDH reduction -/

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

/-- Concrete admitted DDH distinguisher for either IND-CPA challenge bit. -/
noncomputable def concreteDDHReductionPPT
    (F : Family M Parameter Scalar Carrier)
    (efficiency : ReductionEfficiencyCertificate measure F)
    (adversary : Crypto.Infrastructure.Complexity.PPTOracleMachine
      M measure
      (PublicInput Parameter (PublicKey (Carrier := Carrier)))
      (fun _sec _input => Bool)
      (indCPAOracleSpec
        (Message (Carrier := Carrier)) (Ciphertext (Carrier := Carrier))))
    (rightMessage : Bool) :
    Crypto.Infrastructure.Complexity.PPTMachine M measure
      (fun _sec => Crypto.Assumption.DL.DDH.ChallengeInput F)
      (fun _sec _challenge => Bool) :=
  Crypto.Infrastructure.Complexity.PPTMachine.ofAdmittedTimedMachine
    (concreteDDHReductionTimed F efficiency adversary.toTimedOracleMachine
      rightMessage)
    (concreteReductionRuntime_isPoly F efficiency adversary)
    (concreteDDHReduction_admission F efficiency adversary rightMessage)

end CryptoConstruction.Primitive.Encryption.AsymmetricEncryption.ElGamal

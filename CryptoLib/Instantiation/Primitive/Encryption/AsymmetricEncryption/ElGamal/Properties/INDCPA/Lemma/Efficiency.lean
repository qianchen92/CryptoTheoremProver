import CryptoLib.Instantiation.Primitive.Encryption.AsymmetricEncryption.ElGamal.Properties.INDCPA.Proof.Efficiency

/-! # Public efficiency lemmas for the concrete DDH reduction -/

namespace CryptoLib.Instantiation.Primitive.Encryption.AsymmetricEncryption.ElGamal

open CryptoLib.Core.Infrastructure.Computation.Cost
open CryptoLib.Primitive.Encryption.AsymmetricEncryption

universe uCost uParameter uScalar uGroup

variable
    {M : CostModel.{uCost}}
    {measure : NatMeasure M}
    {Parameter : Type uParameter}
    {Scalar : Type uScalar}
    {Carrier : Type uGroup}

@[simp] theorem concreteDDHReductionTimed_runtime
    (F : Family M Parameter Scalar Carrier)
    (efficiency : ReductionEfficiencyCertificate measure F)
    (adversary : CryptoLib.Oracle.Complexity.TimedOracleMachine
      M measure
      (PublicInput Parameter (PublicKey (Carrier := Carrier)))
      (fun _sec _input => Bool)
      (indCPAOracleSpec
        (Message (Carrier := Carrier)) (Ciphertext (Carrier := Carrier))))
    (rightMessage : Bool) :
    (concreteDDHReductionTimed F efficiency adversary rightMessage).runtime =
      concreteReductionRuntime efficiency adversary := by
  exact concreteDDHReductionTimed_runtime_proof F efficiency adversary
    rightMessage

theorem reductionOperationalAdapter_close
    (F : Family M Parameter Scalar Carrier)
    (efficiency : ReductionEfficiencyCertificate measure F)
    (adversary : CryptoLib.Oracle.Complexity.OracleMachine M
      (PublicInput Parameter (PublicKey (Carrier := Carrier)))
      (fun _sec _input => Bool)
      (indCPAOracleSpec
        (Message (Carrier := Carrier)) (Ciphertext (Carrier := Carrier))))
    (rightMessage : Bool) :
    (reductionOperationalAdapter F efficiency rightMessage).close adversary =
      (concreteDDHReduction F efficiency adversary rightMessage).run := by
  exact reductionOperationalAdapter_close_proof F efficiency adversary
    rightMessage

@[simp] theorem reductionOperationalAdapter_closedRuntime
    (F : Family M Parameter Scalar Carrier)
    (efficiency : ReductionEfficiencyCertificate measure F)
    (adversary : CryptoLib.Oracle.Complexity.TimedOracleMachine
      M measure
      (PublicInput Parameter (PublicKey (Carrier := Carrier)))
      (fun _sec _input => Bool)
      (indCPAOracleSpec
        (Message (Carrier := Carrier)) (Ciphertext (Carrier := Carrier))))
    (rightMessage : Bool) :
    (reductionOperationalAdapter F efficiency rightMessage).closedRuntime
        (adversary.localRuntime, adversary.totalQueryRuntime) =
      concreteReductionRuntime efficiency adversary := by
  exact reductionOperationalAdapter_closedRuntime_proof F efficiency adversary
    rightMessage

/-- The exact concrete-reduction runtime is polynomially bounded. -/
theorem concreteReductionRuntime_isPoly
    (F : Family M Parameter Scalar Carrier)
    (efficiency : ReductionEfficiencyCertificate measure F)
    (adversary : CryptoLib.Oracle.Complexity.PPTOracleMachine
      M measure
      (PublicInput Parameter (PublicKey (Carrier := Carrier)))
      (fun _sec _input => Bool)
      (indCPAOracleSpec
        (Message (Carrier := Carrier)) (Ciphertext (Carrier := Carrier)))) :
    CryptoLib.Core.Infrastructure.Asymptotic.IsPolyBounded
      (concreteReductionRuntime efficiency adversary.toTimedOracleMachine) := by
  exact concreteReductionRuntime_isPoly_proof F efficiency adversary

/-- Controlled adapter composition supplies admission for the reduction. -/
theorem concreteDDHReduction_admission
    (F : Family M Parameter Scalar Carrier)
    (efficiency : ReductionEfficiencyCertificate measure F)
    (adversary : CryptoLib.Oracle.Complexity.PPTOracleMachine
      M measure
      (PublicInput Parameter (PublicKey (Carrier := Carrier)))
      (fun _sec _input => Bool)
      (indCPAOracleSpec
        (Message (Carrier := Carrier)) (Ciphertext (Carrier := Carrier))))
    (rightMessage : Bool) :
    CryptoLib.Core.Infrastructure.Complexity.PPTAdmissible M measure
      (concreteDDHReductionTimed F efficiency adversary.toTimedOracleMachine
        rightMessage).run
      (concreteDDHReductionTimed F efficiency adversary.toTimedOracleMachine
        rightMessage).runtime := by
  exact concreteDDHReduction_admission_proof F efficiency adversary rightMessage

end CryptoLib.Instantiation.Primitive.Encryption.AsymmetricEncryption.ElGamal

import CryptoConstruction.Primitive.Encryption.AsymmetricEncryption.ElGamal.Properties.INDCPA.Proof.OperationalMachine

/-! # Proofs of the concrete DDH reduction's efficiency properties -/

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

/-- Proof that the timed reduction exposes the declared runtime expression. -/
theorem concreteDDHReductionTimed_runtime_proof
    (F : Family M Parameter Scalar Carrier)
    (efficiency : ReductionEfficiencyCertificate measure F)
    (adversary : Crypto.Infrastructure.Complexity.TimedOracleMachine
      M measure
      (PublicInput Parameter (PublicKey (Carrier := Carrier)))
      (fun _sec _input => Bool)
      (indCPAOracleSpec
        (Message (Carrier := Carrier)) (Ciphertext (Carrier := Carrier))))
    (rightMessage : Bool) :
    (concreteDDHReductionTimed F efficiency adversary rightMessage).runtime =
      concreteReductionRuntime efficiency adversary := by
  rfl

/-- Proof that the validated adapter closes to the concrete reduction run. -/
theorem reductionOperationalAdapter_close_proof
    (F : Family M Parameter Scalar Carrier)
    (efficiency : ReductionEfficiencyCertificate measure F)
    (adversary : Crypto.Infrastructure.Complexity.OracleMachine M
      (PublicInput Parameter (PublicKey (Carrier := Carrier)))
      (fun _sec _input => Bool)
      (indCPAOracleSpec
        (Message (Carrier := Carrier)) (Ciphertext (Carrier := Carrier))))
    (rightMessage : Bool) :
    (reductionOperationalAdapter F efficiency rightMessage).close adversary =
      (concreteDDHReduction F efficiency adversary rightMessage).run := by
  rfl

/-- Proof that adapter closure computes the declared composed runtime. -/
theorem reductionOperationalAdapter_closedRuntime_proof
    (F : Family M Parameter Scalar Carrier)
    (efficiency : ReductionEfficiencyCertificate measure F)
    (adversary : Crypto.Infrastructure.Complexity.TimedOracleMachine
      M measure
      (PublicInput Parameter (PublicKey (Carrier := Carrier)))
      (fun _sec _input => Bool)
      (indCPAOracleSpec
        (Message (Carrier := Carrier)) (Ciphertext (Carrier := Carrier))))
    (rightMessage : Bool) :
    (reductionOperationalAdapter F efficiency rightMessage).closedRuntime
        (adversary.localRuntime, adversary.totalQueryRuntime) =
      concreteReductionRuntime efficiency adversary := by
  rfl

/-- Proof of polynomial closure for the exact reduction runtime expression. -/
theorem concreteReductionRuntime_isPoly_proof
    (F : Family M Parameter Scalar Carrier)
    (efficiency : ReductionEfficiencyCertificate measure F)
    (adversary : Crypto.Infrastructure.Complexity.PPTOracleMachine
      M measure
      (PublicInput Parameter (PublicKey (Carrier := Carrier)))
      (fun _sec _input => Bool)
      (indCPAOracleSpec
        (Message (Carrier := Carrier)) (Ciphertext (Carrier := Carrier)))) :
    Crypto.Infrastructure.Asymptotic.IsPolyBounded
      (concreteReductionRuntime efficiency adversary.toTimedOracleMachine) := by
  exact Crypto.Infrastructure.Asymptotic.IsPolyBounded.max
    efficiency.rejectRuntime_isPoly
    (Crypto.Infrastructure.Asymptotic.IsPolyBounded.add
      efficiency.prepareRuntime_isPoly
      (Crypto.Infrastructure.Asymptotic.IsPolyBounded.add
        adversary.localRuntime_isPoly
        (Crypto.Infrastructure.Asymptotic.IsPolyBounded.mul
          adversary.totalQueryRuntime_isPoly
          efficiency.queryRuntime_isPoly)))

/-- Proof that controlled adapter composition generates PPT admission. -/
theorem concreteDDHReduction_admission_proof
    (F : Family M Parameter Scalar Carrier)
    (efficiency : ReductionEfficiencyCertificate measure F)
    (adversary : Crypto.Infrastructure.Complexity.PPTOracleMachine
      M measure
      (PublicInput Parameter (PublicKey (Carrier := Carrier)))
      (fun _sec _input => Bool)
      (indCPAOracleSpec
        (Message (Carrier := Carrier)) (Ciphertext (Carrier := Carrier))))
    (rightMessage : Bool) :
    Crypto.Infrastructure.Complexity.PPTAdmissible M measure
      (concreteDDHReductionTimed F efficiency adversary.toTimedOracleMachine
        rightMessage).run
      (concreteDDHReductionTimed F efficiency adversary.toTimedOracleMachine
        rightMessage).runtime := by
  simpa only [reductionOperationalAdapter_close_proof,
      reductionOperationalAdapter_closedRuntime_proof,
      concreteDDHReductionTimed_runtime_proof] using
    (Crypto.Infrastructure.Complexity.PPTAdmissible.ofControlledOracleAdapter
      adversary.toOracleMachine
      (reductionOperationalAdapter F efficiency rightMessage)
      adversary.localRuntime adversary.totalQueryRuntime (by
        change Crypto.Infrastructure.Complexity.OperationalRealization
          adversary.toOracleMachine
          (adversary.localRuntime, adversary.totalQueryRuntime)
        exact adversary.admission))

end CryptoConstruction.Primitive.Encryption.AsymmetricEncryption.ElGamal

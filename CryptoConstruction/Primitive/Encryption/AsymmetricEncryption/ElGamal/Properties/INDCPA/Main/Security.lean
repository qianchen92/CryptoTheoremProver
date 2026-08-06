import CryptoConstruction.Primitive.Encryption.AsymmetricEncryption.ElGamal.Properties.INDCPA.Lemma.GameHop
import CryptoConstruction.Primitive.Encryption.AsymmetricEncryption.ElGamal.Properties.INDCPA.Proof.GameSequence

/-! # ElGamal IND-CPA security from DDH -/

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

/--
ElGamal is IND-CPA secure under DDH.  Operational closure is constructed in
the library; the caller supplies only the explicit reduction-efficiency data.
-/
theorem indCPASecure_of_ddh
    (F : Family M Parameter Scalar Carrier)
    (hDDH : Crypto.Assumption.DL.DDH.Assumption M measure F)
    (efficiency : ReductionEfficiencyCertificate measure F) :
    INDCPASecure M measure (scheme F) := by
  intro adversary
  exact (gameSequence F adversary.toOracleMachine).endpoints_indistinguishable
    (gameSequence_stepIndistinguishable F adversary.toOracleMachine
      (realGame_G₀_indistinguishable F adversary.toOracleMachine)
      (G₀_G₁_indistinguishable F adversary hDDH efficiency)
      (G₁_randomGame_indistinguishable F adversary.toOracleMachine))

end CryptoConstruction.Primitive.Encryption.AsymmetricEncryption.ElGamal

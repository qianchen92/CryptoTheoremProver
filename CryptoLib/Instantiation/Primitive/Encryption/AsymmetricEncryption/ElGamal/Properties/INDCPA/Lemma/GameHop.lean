import CryptoLib.Instantiation.Primitive.Encryption.AsymmetricEncryption.ElGamal.Properties.INDCPA.Proof.GameHop

/-! # ElGamal IND-CPA game-hop lemmas -/

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

/-- The real IND-CPA game and `G₀` are definitionally identical. -/
theorem realGame_G₀_indistinguishable
    (F : Family M Parameter Scalar Carrier)
    (adversary : CryptoLib.Oracle.Complexity.OracleMachine M
      (PublicInput Parameter (PublicKey (Carrier := Carrier)))
      (fun _sec _input => Bool)
      (indCPAOracleSpec
        (Message (Carrier := Carrier)) (Ciphertext (Carrier := Carrier)))) :
    CryptoLib.Core.Infrastructure.GameBased.Indistinguishable
      (indCPASecurityGame (scheme F) adversary false)
      (G₀ F adversary) := by
  exact realGame_G₀_indistinguishable_proof F adversary

/-- `G₀` and `G₁` are computationally indistinguishable under DDH. -/
theorem G₀_G₁_indistinguishable
    (F : Family M Parameter Scalar Carrier)
    (adversary : CryptoLib.Oracle.Complexity.PPTOracleMachine M measure
      (PublicInput Parameter (PublicKey (Carrier := Carrier)))
      (fun _sec _input => Bool)
      (indCPAOracleSpec
        (Message (Carrier := Carrier)) (Ciphertext (Carrier := Carrier))))
    (hDDH : CryptoLib.Assumption.DL.DDH.Assumption M measure F)
    (efficiency : ReductionEfficiencyCertificate measure F) :
    CryptoLib.Core.Infrastructure.GameBased.Indistinguishable
      (G₀ F adversary.toOracleMachine)
      (G₁ F adversary.toOracleMachine) := by
  exact G₀_G₁_indistinguishable_proof F adversary hDDH efficiency

/-- `G₁` and the random IND-CPA game are definitionally identical. -/
theorem G₁_randomGame_indistinguishable
    (F : Family M Parameter Scalar Carrier)
    (adversary : CryptoLib.Oracle.Complexity.OracleMachine M
      (PublicInput Parameter (PublicKey (Carrier := Carrier)))
      (fun _sec _input => Bool)
      (indCPAOracleSpec
        (Message (Carrier := Carrier)) (Ciphertext (Carrier := Carrier)))) :
    CryptoLib.Core.Infrastructure.GameBased.Indistinguishable
      (G₁ F adversary)
      (indCPASecurityGame (scheme F) adversary true) := by
  exact G₁_randomGame_indistinguishable_proof F adversary

end CryptoLib.Instantiation.Primitive.Encryption.AsymmetricEncryption.ElGamal

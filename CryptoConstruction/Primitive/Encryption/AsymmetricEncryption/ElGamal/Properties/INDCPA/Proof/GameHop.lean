import CryptoConstruction.Primitive.Encryption.AsymmetricEncryption.ElGamal.Properties.INDCPA.Definition.Game
import CryptoConstruction.Primitive.Encryption.AsymmetricEncryption.ElGamal.Properties.INDCPA.Lemma.RealGame
import CryptoConstruction.Primitive.Encryption.AsymmetricEncryption.ElGamal.Properties.INDCPA.Lemma.RandomGame
import CryptoConstruction.Primitive.Encryption.AsymmetricEncryption.ElGamal.Properties.INDCPA.Proof.Reduction

/-! # Proofs of the ElGamal IND-CPA game hops -/

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

/-- `G₀` is the real IND-CPA game by definition. -/
theorem realGame_G₀_indistinguishable_proof
    (F : Family M Parameter Scalar Carrier)
    (adversary : Crypto.Infrastructure.Complexity.OracleMachine M
      (PublicInput Parameter (PublicKey (Carrier := Carrier)))
      (fun _sec _input => Bool)
      (indCPAOracleSpec
        (Message (Carrier := Carrier)) (Ciphertext (Carrier := Carrier)))) :
    Crypto.Infrastructure.GameBased.Indistinguishable
      (indCPASecurityGame (scheme F) adversary false)
      (G₀ F adversary) := by
  exact Crypto.Infrastructure.GameBased.Indistinguishable.refl _

/-- DDH makes `G₀` and `G₁` computationally indistinguishable. -/
theorem G₀_G₁_indistinguishable_proof
    (F : Family M Parameter Scalar Carrier)
    (adversary : Crypto.Infrastructure.Complexity.PPTOracleMachine M measure
      (PublicInput Parameter (PublicKey (Carrier := Carrier)))
      (fun _sec _input => Bool)
      (indCPAOracleSpec
        (Message (Carrier := Carrier)) (Ciphertext (Carrier := Carrier))))
    (hDDH : Crypto.Assumption.DL.DDH.Assumption M measure F)
    (efficiency : ReductionEfficiencyCertificate measure F) :
    Crypto.Infrastructure.GameBased.Indistinguishable
      (G₀ F adversary.toOracleMachine)
      (G₁ F adversary.toOracleMachine) := by
  have hG₀_eq_real :
      G₀ F adversary.toOracleMachine =
        realReductionGame F adversary.toOracleMachine false := by
    simpa only [G₀] using
      indCPASecurityGame_eq_realReductionGame F
        adversary.toOracleMachine false
  have hReal_random_left :=
    ddhReduction_indistinguishable F adversary false hDDH
      (ddhReductionCertificate F efficiency adversary false)
  have hRandom_left_hybrid :
      Crypto.Infrastructure.GameBased.Indistinguishable
        (randomReductionGame F adversary.toOracleMachine false)
        (randomHybridGame F adversary.toOracleMachine) :=
    Crypto.Infrastructure.GameBased.Indistinguishable.of_eq
      (randomReductionGame_eq_randomHybridGame F
        adversary.toOracleMachine false)
  have hHybrid_random_right :
      Crypto.Infrastructure.GameBased.Indistinguishable
        (randomHybridGame F adversary.toOracleMachine)
        (randomReductionGame F adversary.toOracleMachine true) :=
    (Crypto.Infrastructure.GameBased.Indistinguishable.of_eq
      (randomReductionGame_eq_randomHybridGame F
        adversary.toOracleMachine true)).symm
  have hRandom_real_right :=
    (ddhReduction_indistinguishable F adversary true hDDH
      (ddhReductionCertificate F efficiency adversary true)).symm
  have hReal_eq_G₁ :
      realReductionGame F adversary.toOracleMachine true =
        G₁ F adversary.toOracleMachine := by
    simpa only [G₁] using
      (indCPASecurityGame_eq_realReductionGame F
        adversary.toOracleMachine true).symm
  exact
    (Crypto.Infrastructure.GameBased.Indistinguishable.of_eq hG₀_eq_real).trans
      (hReal_random_left.trans
        (hRandom_left_hybrid.trans
          (hHybrid_random_right.trans
            (hRandom_real_right.trans
              (Crypto.Infrastructure.GameBased.Indistinguishable.of_eq
                hReal_eq_G₁)))))

/-- `G₁` is the random IND-CPA game by definition. -/
theorem G₁_randomGame_indistinguishable_proof
    (F : Family M Parameter Scalar Carrier)
    (adversary : Crypto.Infrastructure.Complexity.OracleMachine M
      (PublicInput Parameter (PublicKey (Carrier := Carrier)))
      (fun _sec _input => Bool)
      (indCPAOracleSpec
        (Message (Carrier := Carrier)) (Ciphertext (Carrier := Carrier)))) :
    Crypto.Infrastructure.GameBased.Indistinguishable
      (G₁ F adversary)
      (indCPASecurityGame (scheme F) adversary true) := by
  exact Crypto.Infrastructure.GameBased.Indistinguishable.refl _

end CryptoConstruction.Primitive.Encryption.AsymmetricEncryption.ElGamal

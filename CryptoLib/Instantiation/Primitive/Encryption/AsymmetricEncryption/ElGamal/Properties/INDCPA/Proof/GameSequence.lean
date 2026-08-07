import CryptoLib.Core.Infrastructure.GameBased.Hybrid
import CryptoLib.Instantiation.Primitive.Encryption.AsymmetricEncryption.ElGamal.Properties.INDCPA.Definition.Game
import CryptoLib.Instantiation.Primitive.Encryption.AsymmetricEncryption.ElGamal.Properties.INDCPA.Lemma.RealGame
import CryptoLib.Instantiation.Primitive.Encryption.AsymmetricEncryption.ElGamal.Properties.INDCPA.Lemma.RandomGame

/-! # ElGamal hybrid sequence and advantage bound -/

namespace CryptoLib.Instantiation.Primitive.Encryption.AsymmetricEncryption.ElGamal

open CryptoLib.Core.Infrastructure.Computation.Cost
open CryptoLib.Core.Infrastructure.Computation
open CryptoLib.Core.Infrastructure.Computation.Oracle
open CryptoLib.Core.Primitive.Encryption.AsymmetricEncryption

universe uCost uParameter uScalar uGroup

variable
    {M : CostModel.{uCost}}
    {Parameter : Type uParameter}
    {Scalar : Type uScalar}
    {Carrier : Type uGroup}

/-- The ElGamal sequence has three transitions and four games. The outer
transitions are definitional identities; the middle transition contains the
DDH reduction. -/
noncomputable def gameSequence
    (F : Family M Parameter Scalar Carrier)
    (adversary : CryptoLib.Core.Infrastructure.Complexity.OracleMachine M
      (PublicInput Parameter (PublicKey (Carrier := Carrier)))
      (fun _sec _input => Bool)
      (indCPAOracleSpec (Message (Carrier := Carrier)) (Ciphertext (Carrier := Carrier)))) :
    CryptoLib.Core.Infrastructure.GameBased.Hybrid Bool :=
  CryptoLib.Core.Infrastructure.GameBased.Hybrid.ofList
    (indCPASecurityGame (scheme F) adversary false)
    [G₀ F adversary,
      G₁ F adversary,
      indCPASecurityGame (scheme F) adversary true]

@[simp] theorem gameSequence_length
    (F : Family M Parameter Scalar Carrier)
    (adversary : CryptoLib.Core.Infrastructure.Complexity.OracleMachine M
      (PublicInput Parameter (PublicKey (Carrier := Carrier)))
      (fun _sec _input => Bool)
      (indCPAOracleSpec (Message (Carrier := Carrier)) (Ciphertext (Carrier := Carrier)))) :
    (gameSequence F adversary).length = 3 :=
  rfl

@[simp] theorem gameSequence_first
    (F : Family M Parameter Scalar Carrier)
    (adversary : CryptoLib.Core.Infrastructure.Complexity.OracleMachine M
      (PublicInput Parameter (PublicKey (Carrier := Carrier)))
      (fun _sec _input => Bool)
      (indCPAOracleSpec (Message (Carrier := Carrier)) (Ciphertext (Carrier := Carrier)))) :
    (gameSequence F adversary).first =
      indCPASecurityGame (scheme F) adversary false :=
  rfl

@[simp] theorem gameSequence_last
    (F : Family M Parameter Scalar Carrier)
    (adversary : CryptoLib.Core.Infrastructure.Complexity.OracleMachine M
      (PublicInput Parameter (PublicKey (Carrier := Carrier)))
      (fun _sec _input => Bool)
      (indCPAOracleSpec (Message (Carrier := Carrier)) (Ciphertext (Carrier := Carrier)))) :
    (gameSequence F adversary).last =
      indCPASecurityGame (scheme F) adversary true :=
  rfl

/-- Three explicit game-hop lemmas establish every adjacent transition of the
ElGamal hybrid sequence. -/
theorem gameSequence_stepIndistinguishable
    (F : Family M Parameter Scalar Carrier)
    (adversary : CryptoLib.Core.Infrastructure.Complexity.OracleMachine M
      (PublicInput Parameter (PublicKey (Carrier := Carrier)))
      (fun _sec _input => Bool)
      (indCPAOracleSpec (Message (Carrier := Carrier)) (Ciphertext (Carrier := Carrier))))
    (hReal_G₀ : CryptoLib.Core.Infrastructure.GameBased.Indistinguishable
      (indCPASecurityGame (scheme F) adversary false)
      (G₀ F adversary))
    (hG₀_G₁ : CryptoLib.Core.Infrastructure.GameBased.Indistinguishable
      (G₀ F adversary) (G₁ F adversary))
    (hG₁_random : CryptoLib.Core.Infrastructure.GameBased.Indistinguishable
      (G₁ F adversary)
      (indCPASecurityGame (scheme F) adversary true)) :
    (gameSequence F adversary).StepIndistinguishable := by
  rw [gameSequence,
    CryptoLib.Core.Infrastructure.GameBased.Hybrid.ofList_stepIndistinguishable_iff]
  simp only [List.isChain_cons_cons, List.isChain_singleton, and_true]
  exact ⟨hReal_G₀, hG₀_G₁, hG₁_random⟩

/-- If both semantic DDH reductions have negligible gaps, then the original
left and right ElGamal IND-CPA games are indistinguishable. -/
theorem indCPA_indistinguishable_of_reductions
    (F : Family M Parameter Scalar Carrier)
    (adversary : CryptoLib.Core.Infrastructure.Complexity.OracleMachine M
      (PublicInput Parameter (PublicKey (Carrier := Carrier)))
      (fun _sec _input => Bool)
      (indCPAOracleSpec (Message (Carrier := Carrier)) (Ciphertext (Carrier := Carrier))))
    (hleft : CryptoLib.Core.Infrastructure.GameBased.Indistinguishable
      (realReductionGame F adversary false)
      (randomReductionGame F adversary false))
    (hright : CryptoLib.Core.Infrastructure.GameBased.Indistinguishable
      (realReductionGame F adversary true)
      (randomReductionGame F adversary true)) :
    CryptoLib.Core.Infrastructure.GameBased.Indistinguishable
      (indCPASecurityGame (scheme F) adversary false)
      (indCPASecurityGame (scheme F) adversary true) := by
  have hG₀_real : CryptoLib.Core.Infrastructure.GameBased.Indistinguishable
      (G₀ F adversary) (realReductionGame F adversary false) :=
    (CryptoLib.Core.Infrastructure.GameBased.Indistinguishable.of_eq
      (by
        simpa only [G₀] using
          indCPASecurityGame_eq_realReductionGame F adversary false))
  have hRandom_left_hybrid :
      CryptoLib.Core.Infrastructure.GameBased.Indistinguishable
        (randomReductionGame F adversary false)
        (randomHybridGame F adversary) :=
    CryptoLib.Core.Infrastructure.GameBased.Indistinguishable.of_eq
      (randomReductionGame_eq_randomHybridGame F adversary false)
  have hHybrid_random_right :
      CryptoLib.Core.Infrastructure.GameBased.Indistinguishable
        (randomHybridGame F adversary)
        (randomReductionGame F adversary true) :=
    (CryptoLib.Core.Infrastructure.GameBased.Indistinguishable.of_eq
      (randomReductionGame_eq_randomHybridGame F adversary true)).symm
  have hReal_G₁ : CryptoLib.Core.Infrastructure.GameBased.Indistinguishable
      (realReductionGame F adversary true) (G₁ F adversary) :=
    CryptoLib.Core.Infrastructure.GameBased.Indistinguishable.of_eq (by
      simpa only [G₁] using
        (indCPASecurityGame_eq_realReductionGame F adversary true).symm)
  have hG₀_G₁ : CryptoLib.Core.Infrastructure.GameBased.Indistinguishable
      (G₀ F adversary) (G₁ F adversary) :=
    hG₀_real.trans
      (hleft.trans
        (hRandom_left_hybrid.trans
          (hHybrid_random_right.trans
            (hright.symm.trans hReal_G₁))))
  exact (gameSequence F adversary).endpoints_indistinguishable
    (gameSequence_stepIndistinguishable F adversary
      (CryptoLib.Core.Infrastructure.GameBased.Indistinguishable.refl _)
      hG₀_G₁
      (CryptoLib.Core.Infrastructure.GameBased.Indistinguishable.refl _))

/-- The middle `G₀ → G₁` advantage is bounded by the two concrete DDH
reduction advantages; the two outer sequence advantages are zero. -/
theorem indCPAAdvantage_le_ddhAdvantages
    (F : Family M Parameter Scalar Carrier)
    (adversary : CryptoLib.Core.Infrastructure.Complexity.OracleMachine M
      (PublicInput Parameter (PublicKey (Carrier := Carrier)))
      (fun _sec _input => Bool)
      (indCPAOracleSpec (Message (Carrier := Carrier)) (Ciphertext (Carrier := Carrier))))
    (sec : CryptoLib.Core.SecPar) :
    INDCPAAdvantage (scheme F) adversary sec ≤
      CryptoLib.Core.Infrastructure.GameBased.Advantage
          (realReductionGame F adversary false)
          (randomReductionGame F adversary false) sec +
        CryptoLib.Core.Infrastructure.GameBased.Advantage
          (realReductionGame F adversary true)
          (randomReductionGame F adversary true) sec := by
  have h := (gameSequence F adversary).endpointAdvantage_le_sum sec
  change CryptoLib.Core.Infrastructure.GameBased.Advantage
      (indCPASecurityGame (scheme F) adversary false)
      (indCPASecurityGame (scheme F) adversary true) sec ≤
    ∑ step : Fin 3,
      CryptoLib.Core.Infrastructure.GameBased.Advantage
        ((gameSequence F adversary).before step)
        ((gameSequence F adversary).after step) sec at h
  rw [Fin.sum_univ_three] at h
  change CryptoLib.Core.Infrastructure.GameBased.Advantage
      (indCPASecurityGame (scheme F) adversary false)
      (indCPASecurityGame (scheme F) adversary true) sec ≤
    (CryptoLib.Core.Infrastructure.GameBased.Advantage
        (indCPASecurityGame (scheme F) adversary false) (G₀ F adversary) sec +
      CryptoLib.Core.Infrastructure.GameBased.Advantage
        (G₀ F adversary) (G₁ F adversary) sec) +
      CryptoLib.Core.Infrastructure.GameBased.Advantage
        (G₁ F adversary)
        (indCPASecurityGame (scheme F) adversary true) sec at h
  have hfirstZero : CryptoLib.Core.Infrastructure.GameBased.Advantage
      (indCPASecurityGame (scheme F) adversary false) (G₀ F adversary) sec =
      0 := by
    change CryptoLib.Core.Infrastructure.GameBased.Advantage
      (indCPASecurityGame (scheme F) adversary false)
      (indCPASecurityGame (scheme F) adversary false) sec = 0
    exact congrFun
      (CryptoLib.Core.Infrastructure.GameBased.Advantage.self
        (indCPASecurityGame (scheme F) adversary false)) sec
  have hlastZero : CryptoLib.Core.Infrastructure.GameBased.Advantage
      (G₁ F adversary)
      (indCPASecurityGame (scheme F) adversary true) sec = 0 := by
    change CryptoLib.Core.Infrastructure.GameBased.Advantage
      (indCPASecurityGame (scheme F) adversary true)
      (indCPASecurityGame (scheme F) adversary true) sec = 0
    exact congrFun
      (CryptoLib.Core.Infrastructure.GameBased.Advantage.self
        (indCPASecurityGame (scheme F) adversary true)) sec
  have hEndpoint_middle : CryptoLib.Core.Infrastructure.GameBased.Advantage
      (indCPASecurityGame (scheme F) adversary false)
      (indCPASecurityGame (scheme F) adversary true) sec ≤
      CryptoLib.Core.Infrastructure.GameBased.Advantage
        (G₀ F adversary) (G₁ F adversary) sec := by
    calc
      CryptoLib.Core.Infrastructure.GameBased.Advantage
          (indCPASecurityGame (scheme F) adversary false)
          (indCPASecurityGame (scheme F) adversary true) sec ≤
        (CryptoLib.Core.Infrastructure.GameBased.Advantage
            (indCPASecurityGame (scheme F) adversary false)
            (G₀ F adversary) sec +
          CryptoLib.Core.Infrastructure.GameBased.Advantage
            (G₀ F adversary) (G₁ F adversary) sec) +
          CryptoLib.Core.Infrastructure.GameBased.Advantage
            (G₁ F adversary)
            (indCPASecurityGame (scheme F) adversary true) sec := h
      _ = CryptoLib.Core.Infrastructure.GameBased.Advantage
          (G₀ F adversary) (G₁ F adversary) sec := by
        rw [hfirstZero, hlastZero, zero_add, add_zero]
  have hleftAdvantage : CryptoLib.Core.Infrastructure.GameBased.Advantage
      (G₀ F adversary) (randomHybridGame F adversary) sec =
      CryptoLib.Core.Infrastructure.GameBased.Advantage
        (realReductionGame F adversary false)
        (randomReductionGame F adversary false) sec := by
    rw [G₀, indCPASecurityGame_eq_realReductionGame F adversary false]
    rw [← randomReductionGame_eq_randomHybridGame F adversary false]
  have hrightAdvantage : CryptoLib.Core.Infrastructure.GameBased.Advantage
      (randomHybridGame F adversary) (G₁ F adversary) sec =
      CryptoLib.Core.Infrastructure.GameBased.Advantage
        (realReductionGame F adversary true)
        (randomReductionGame F adversary true) sec := by
    rw [G₁]
    rw [← randomReductionGame_eq_randomHybridGame F adversary true]
    rw [indCPASecurityGame_eq_realReductionGame F adversary true]
    rw [CryptoLib.Core.Infrastructure.GameBased.Advantage.symm
      (G₀ := randomReductionGame F adversary true)
      (G₁ := realReductionGame F adversary true)]
  unfold INDCPAAdvantage
  calc
    CryptoLib.Core.Infrastructure.GameBased.Advantage
        (indCPASecurityGame (scheme F) adversary false)
        (indCPASecurityGame (scheme F) adversary true) sec ≤
      CryptoLib.Core.Infrastructure.GameBased.Advantage
        (G₀ F adversary) (G₁ F adversary) sec := hEndpoint_middle
    _ ≤ CryptoLib.Core.Infrastructure.GameBased.Advantage
          (G₀ F adversary) (randomHybridGame F adversary) sec +
        CryptoLib.Core.Infrastructure.GameBased.Advantage
          (randomHybridGame F adversary) (G₁ F adversary) sec :=
      CryptoLib.Core.Infrastructure.GameBased.Advantage.triangle sec
    _ = CryptoLib.Core.Infrastructure.GameBased.Advantage
          (realReductionGame F adversary false)
          (randomReductionGame F adversary false) sec +
        CryptoLib.Core.Infrastructure.GameBased.Advantage
          (realReductionGame F adversary true)
          (randomReductionGame F adversary true) sec := by
      rw [hleftAdvantage, hrightAdvantage]

end CryptoLib.Instantiation.Primitive.Encryption.AsymmetricEncryption.ElGamal

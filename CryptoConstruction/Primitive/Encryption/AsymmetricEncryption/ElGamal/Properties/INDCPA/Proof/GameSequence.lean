import Crypto.Infrastructure.GameBased.Hybrid
import CryptoConstruction.Primitive.Encryption.AsymmetricEncryption.ElGamal.Properties.INDCPA.Definition.Game
import CryptoConstruction.Primitive.Encryption.AsymmetricEncryption.ElGamal.Properties.INDCPA.Lemma.RealGame
import CryptoConstruction.Primitive.Encryption.AsymmetricEncryption.ElGamal.Properties.INDCPA.Lemma.RandomGame

/-! # ElGamal hybrid sequence and advantage bound -/

namespace CryptoConstruction.Primitive.Encryption.AsymmetricEncryption.ElGamal

open Crypto.Infrastructure.Computation.Cost
open Crypto.Infrastructure.Computation
open Crypto.Infrastructure.Computation.Oracle
open Crypto.Primitive.Encryption.AsymmetricEncryption

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
    (adversary : Crypto.Infrastructure.Complexity.OracleMachine M
      (PublicInput Parameter (PublicKey (Carrier := Carrier)))
      (fun _sec _input => Bool)
      (indCPAOracleSpec (Message (Carrier := Carrier)) (Ciphertext (Carrier := Carrier)))) :
    Crypto.Infrastructure.GameBased.Hybrid Bool :=
  Crypto.Infrastructure.GameBased.Hybrid.ofList
    (indCPASecurityGame (scheme F) adversary false)
    [G₀ F adversary,
      G₁ F adversary,
      indCPASecurityGame (scheme F) adversary true]

@[simp] theorem gameSequence_length
    (F : Family M Parameter Scalar Carrier)
    (adversary : Crypto.Infrastructure.Complexity.OracleMachine M
      (PublicInput Parameter (PublicKey (Carrier := Carrier)))
      (fun _sec _input => Bool)
      (indCPAOracleSpec (Message (Carrier := Carrier)) (Ciphertext (Carrier := Carrier)))) :
    (gameSequence F adversary).length = 3 :=
  rfl

@[simp] theorem gameSequence_first
    (F : Family M Parameter Scalar Carrier)
    (adversary : Crypto.Infrastructure.Complexity.OracleMachine M
      (PublicInput Parameter (PublicKey (Carrier := Carrier)))
      (fun _sec _input => Bool)
      (indCPAOracleSpec (Message (Carrier := Carrier)) (Ciphertext (Carrier := Carrier)))) :
    (gameSequence F adversary).first =
      indCPASecurityGame (scheme F) adversary false :=
  rfl

@[simp] theorem gameSequence_last
    (F : Family M Parameter Scalar Carrier)
    (adversary : Crypto.Infrastructure.Complexity.OracleMachine M
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
    (adversary : Crypto.Infrastructure.Complexity.OracleMachine M
      (PublicInput Parameter (PublicKey (Carrier := Carrier)))
      (fun _sec _input => Bool)
      (indCPAOracleSpec (Message (Carrier := Carrier)) (Ciphertext (Carrier := Carrier))))
    (hReal_G₀ : Crypto.Infrastructure.GameBased.Indistinguishable
      (indCPASecurityGame (scheme F) adversary false)
      (G₀ F adversary))
    (hG₀_G₁ : Crypto.Infrastructure.GameBased.Indistinguishable
      (G₀ F adversary) (G₁ F adversary))
    (hG₁_random : Crypto.Infrastructure.GameBased.Indistinguishable
      (G₁ F adversary)
      (indCPASecurityGame (scheme F) adversary true)) :
    (gameSequence F adversary).StepIndistinguishable := by
  rw [gameSequence,
    Crypto.Infrastructure.GameBased.Hybrid.ofList_stepIndistinguishable_iff]
  simp only [List.isChain_cons_cons, List.isChain_singleton, and_true]
  exact ⟨hReal_G₀, hG₀_G₁, hG₁_random⟩

/-- If both semantic DDH reductions have negligible gaps, then the original
left and right ElGamal IND-CPA games are indistinguishable. -/
theorem indCPA_indistinguishable_of_reductions
    (F : Family M Parameter Scalar Carrier)
    (adversary : Crypto.Infrastructure.Complexity.OracleMachine M
      (PublicInput Parameter (PublicKey (Carrier := Carrier)))
      (fun _sec _input => Bool)
      (indCPAOracleSpec (Message (Carrier := Carrier)) (Ciphertext (Carrier := Carrier))))
    (hleft : Crypto.Infrastructure.GameBased.Indistinguishable
      (realReductionGame F adversary false)
      (randomReductionGame F adversary false))
    (hright : Crypto.Infrastructure.GameBased.Indistinguishable
      (realReductionGame F adversary true)
      (randomReductionGame F adversary true)) :
    Crypto.Infrastructure.GameBased.Indistinguishable
      (indCPASecurityGame (scheme F) adversary false)
      (indCPASecurityGame (scheme F) adversary true) := by
  have hG₀_real : Crypto.Infrastructure.GameBased.Indistinguishable
      (G₀ F adversary) (realReductionGame F adversary false) :=
    (Crypto.Infrastructure.GameBased.Indistinguishable.of_eq
      (by
        simpa only [G₀] using
          indCPASecurityGame_eq_realReductionGame F adversary false))
  have hRandom_left_hybrid :
      Crypto.Infrastructure.GameBased.Indistinguishable
        (randomReductionGame F adversary false)
        (randomHybridGame F adversary) :=
    Crypto.Infrastructure.GameBased.Indistinguishable.of_eq
      (randomReductionGame_eq_randomHybridGame F adversary false)
  have hHybrid_random_right :
      Crypto.Infrastructure.GameBased.Indistinguishable
        (randomHybridGame F adversary)
        (randomReductionGame F adversary true) :=
    (Crypto.Infrastructure.GameBased.Indistinguishable.of_eq
      (randomReductionGame_eq_randomHybridGame F adversary true)).symm
  have hReal_G₁ : Crypto.Infrastructure.GameBased.Indistinguishable
      (realReductionGame F adversary true) (G₁ F adversary) :=
    Crypto.Infrastructure.GameBased.Indistinguishable.of_eq (by
      simpa only [G₁] using
        (indCPASecurityGame_eq_realReductionGame F adversary true).symm)
  have hG₀_G₁ : Crypto.Infrastructure.GameBased.Indistinguishable
      (G₀ F adversary) (G₁ F adversary) :=
    hG₀_real.trans
      (hleft.trans
        (hRandom_left_hybrid.trans
          (hHybrid_random_right.trans
            (hright.symm.trans hReal_G₁))))
  exact (gameSequence F adversary).endpoints_indistinguishable
    (gameSequence_stepIndistinguishable F adversary
      (Crypto.Infrastructure.GameBased.Indistinguishable.refl _)
      hG₀_G₁
      (Crypto.Infrastructure.GameBased.Indistinguishable.refl _))

/-- The middle `G₀ → G₁` advantage is bounded by the two concrete DDH
reduction advantages; the two outer sequence advantages are zero. -/
theorem indCPAAdvantage_le_ddhAdvantages
    (F : Family M Parameter Scalar Carrier)
    (adversary : Crypto.Infrastructure.Complexity.OracleMachine M
      (PublicInput Parameter (PublicKey (Carrier := Carrier)))
      (fun _sec _input => Bool)
      (indCPAOracleSpec (Message (Carrier := Carrier)) (Ciphertext (Carrier := Carrier))))
    (sec : Crypto.SecPar) :
    INDCPAAdvantage (scheme F) adversary sec ≤
      Crypto.Infrastructure.GameBased.Advantage
          (realReductionGame F adversary false)
          (randomReductionGame F adversary false) sec +
        Crypto.Infrastructure.GameBased.Advantage
          (realReductionGame F adversary true)
          (randomReductionGame F adversary true) sec := by
  have h := (gameSequence F adversary).endpointAdvantage_le_sum sec
  change Crypto.Infrastructure.GameBased.Advantage
      (indCPASecurityGame (scheme F) adversary false)
      (indCPASecurityGame (scheme F) adversary true) sec ≤
    ∑ step : Fin 3,
      Crypto.Infrastructure.GameBased.Advantage
        ((gameSequence F adversary).before step)
        ((gameSequence F adversary).after step) sec at h
  rw [Fin.sum_univ_three] at h
  change Crypto.Infrastructure.GameBased.Advantage
      (indCPASecurityGame (scheme F) adversary false)
      (indCPASecurityGame (scheme F) adversary true) sec ≤
    (Crypto.Infrastructure.GameBased.Advantage
        (indCPASecurityGame (scheme F) adversary false) (G₀ F adversary) sec +
      Crypto.Infrastructure.GameBased.Advantage
        (G₀ F adversary) (G₁ F adversary) sec) +
      Crypto.Infrastructure.GameBased.Advantage
        (G₁ F adversary)
        (indCPASecurityGame (scheme F) adversary true) sec at h
  have hfirstZero : Crypto.Infrastructure.GameBased.Advantage
      (indCPASecurityGame (scheme F) adversary false) (G₀ F adversary) sec =
      0 := by
    change Crypto.Infrastructure.GameBased.Advantage
      (indCPASecurityGame (scheme F) adversary false)
      (indCPASecurityGame (scheme F) adversary false) sec = 0
    exact congrFun
      (Crypto.Infrastructure.GameBased.Advantage.self
        (indCPASecurityGame (scheme F) adversary false)) sec
  have hlastZero : Crypto.Infrastructure.GameBased.Advantage
      (G₁ F adversary)
      (indCPASecurityGame (scheme F) adversary true) sec = 0 := by
    change Crypto.Infrastructure.GameBased.Advantage
      (indCPASecurityGame (scheme F) adversary true)
      (indCPASecurityGame (scheme F) adversary true) sec = 0
    exact congrFun
      (Crypto.Infrastructure.GameBased.Advantage.self
        (indCPASecurityGame (scheme F) adversary true)) sec
  have hEndpoint_middle : Crypto.Infrastructure.GameBased.Advantage
      (indCPASecurityGame (scheme F) adversary false)
      (indCPASecurityGame (scheme F) adversary true) sec ≤
      Crypto.Infrastructure.GameBased.Advantage
        (G₀ F adversary) (G₁ F adversary) sec := by
    calc
      Crypto.Infrastructure.GameBased.Advantage
          (indCPASecurityGame (scheme F) adversary false)
          (indCPASecurityGame (scheme F) adversary true) sec ≤
        (Crypto.Infrastructure.GameBased.Advantage
            (indCPASecurityGame (scheme F) adversary false)
            (G₀ F adversary) sec +
          Crypto.Infrastructure.GameBased.Advantage
            (G₀ F adversary) (G₁ F adversary) sec) +
          Crypto.Infrastructure.GameBased.Advantage
            (G₁ F adversary)
            (indCPASecurityGame (scheme F) adversary true) sec := h
      _ = Crypto.Infrastructure.GameBased.Advantage
          (G₀ F adversary) (G₁ F adversary) sec := by
        rw [hfirstZero, hlastZero, zero_add, add_zero]
  have hleftAdvantage : Crypto.Infrastructure.GameBased.Advantage
      (G₀ F adversary) (randomHybridGame F adversary) sec =
      Crypto.Infrastructure.GameBased.Advantage
        (realReductionGame F adversary false)
        (randomReductionGame F adversary false) sec := by
    rw [G₀, indCPASecurityGame_eq_realReductionGame F adversary false]
    rw [← randomReductionGame_eq_randomHybridGame F adversary false]
  have hrightAdvantage : Crypto.Infrastructure.GameBased.Advantage
      (randomHybridGame F adversary) (G₁ F adversary) sec =
      Crypto.Infrastructure.GameBased.Advantage
        (realReductionGame F adversary true)
        (randomReductionGame F adversary true) sec := by
    rw [G₁]
    rw [← randomReductionGame_eq_randomHybridGame F adversary true]
    rw [indCPASecurityGame_eq_realReductionGame F adversary true]
    rw [Crypto.Infrastructure.GameBased.Advantage.symm
      (G₀ := randomReductionGame F adversary true)
      (G₁ := realReductionGame F adversary true)]
  unfold INDCPAAdvantage
  calc
    Crypto.Infrastructure.GameBased.Advantage
        (indCPASecurityGame (scheme F) adversary false)
        (indCPASecurityGame (scheme F) adversary true) sec ≤
      Crypto.Infrastructure.GameBased.Advantage
        (G₀ F adversary) (G₁ F adversary) sec := hEndpoint_middle
    _ ≤ Crypto.Infrastructure.GameBased.Advantage
          (G₀ F adversary) (randomHybridGame F adversary) sec +
        Crypto.Infrastructure.GameBased.Advantage
          (randomHybridGame F adversary) (G₁ F adversary) sec :=
      Crypto.Infrastructure.GameBased.Advantage.triangle sec
    _ = Crypto.Infrastructure.GameBased.Advantage
          (realReductionGame F adversary false)
          (randomReductionGame F adversary false) sec +
        Crypto.Infrastructure.GameBased.Advantage
          (realReductionGame F adversary true)
          (randomReductionGame F adversary true) sec := by
      rw [hleftAdvantage, hrightAdvantage]

end CryptoConstruction.Primitive.Encryption.AsymmetricEncryption.ElGamal

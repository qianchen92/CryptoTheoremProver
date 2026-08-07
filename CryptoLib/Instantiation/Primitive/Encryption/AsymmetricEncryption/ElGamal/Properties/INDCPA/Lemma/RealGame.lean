import CryptoLib.Instantiation.Primitive.Encryption.AsymmetricEncryption.ElGamal.Properties.INDCPA.Definition.RealGame

/-! # Real-game oracle and distribution lemmas -/

namespace CryptoLib.Instantiation.Primitive.Encryption.AsymmetricEncryption.ElGamal

open CryptoLib.Core.Infrastructure.Computation.Cost
open CryptoLib.Core.Infrastructure.Computation
open CryptoLib.Core.Infrastructure.Computation.Oracle
open CryptoLib.Core.Primitive.Encryption.AsymmetricEncryption
open scoped DDHParameter

universe uCost uParameter uScalar uGroup

variable
    {M : CostModel.{uCost}}
    {Parameter : Type uParameter}
    {Scalar : Type uScalar}
    {Carrier : Type uGroup}

private theorem indCPAEncryptionOracle_eq_lazyReal
    (F : Family M Parameter Scalar Carrier)
    (sec : CryptoLib.Core.SecPar)
    (parameter : Parameter) (pk : Carrier) (rightMessage : Bool) :
    indCPAEncryptionOracle (scheme F) sec
        (indCPAPublicInput F sec parameter pk) rightMessage =
      indCPALazyRealOracle F sec parameter pk rightMessage := by
  let pp := F.publicParam parameter
  dsimp [indCPAEncryptionOracle, indCPALazyRealOracle,
    OracleEnv.withLazyOneShotSeed]
  congr
  funext name querySec used query
  cases name
  change Carrier × Carrier at query
  cases used
  · simp only [Bool.false_eq_true, ↓reduceIte, scheme_encryptDist,
      PMF.bind_bind, PMF.pure_bind]
    congr 1
    funext seed
    symm
    exact PMF.pure_map _ _
  · simp only [↓reduceIte]
    symm
    exact PMF.pure_map _ _

private theorem runWithEnv_indCPAEncryptionOracle_eq_bind_fixedReal
    (F : Family M Parameter Scalar Carrier)
    (adversary : CryptoLib.Core.Infrastructure.Complexity.OracleMachine M
      (PublicInput Parameter (PublicKey (Carrier := Carrier)))
      (fun _sec _input => Bool)
      (indCPAOracleSpec
        (Message (Carrier := Carrier)) (Ciphertext (Carrier := Carrier))))
    (sec : CryptoLib.Core.SecPar)
    (parameter : Parameter) (pk : Carrier) (rightMessage : Bool) :
    adversary.runWithEnv sec (indCPAPublicInput F sec parameter pk)
        (indCPAEncryptionOracle (scheme F) sec
          (indCPAPublicInput F sec parameter pk) rightMessage) =
      PMF.bind
          (@CryptoLib.Core.Infrastructure.Probability.uniformPMF
            Scalar (F.publicParam parameter).fintypeScalar
            ⟨(F.publicParam parameter).commMonoidScalar.one⟩) fun r =>
        adversary.runWithEnv sec (indCPAPublicInput F sec parameter pk)
          (indCPAFixedRealOracle F sec parameter pk rightMessage r) := by
  let pp := F.publicParam parameter
  letI : Nonempty Scalar := ⟨pp.commMonoidScalar.one⟩
  rw [indCPAEncryptionOracle_eq_lazyReal F sec parameter pk rightMessage]
  unfold CryptoLib.Core.Infrastructure.Complexity.OracleMachine.runWithEnv
  simp only [indCPALazyRealOracle, indCPAFixedRealOracle]
  rw [OracleEnv.runWithEnv_withLazyOneShotSeed]
  rw [PMF.map_bind]

private theorem fixedRealOracle_eq_reductionOracle_realChallenge
    (F : Family M Parameter Scalar Carrier)
    (sec : CryptoLib.Core.SecPar)
    (parameter : Parameter) (a b : Scalar) (rightMessage : Bool) :
    indCPAFixedRealOracle F sec parameter
        ((F.publicParam parameter).smul.smul a
          (F.publicParam parameter).generator) rightMessage b =
      reductionOracle F sec
        (CryptoLib.Core.Assumption.DL.DDH.realChallenge F parameter a b)
        rightMessage := by
  let pp := F.publicParam parameter
  letI : AddGroup Carrier := pp.addGroup
  letI : SMul Scalar Carrier := pp.smul
  letI : CommMonoid Scalar := pp.commMonoidScalar
  have hshared : b • (a • pp.generator) = (a * b) • pp.generator := by
    calc
      b • (a • pp.generator) = a • (b • pp.generator) :=
        pp.scalarAction_commutes b a
      _ = (a * b) • pp.generator :=
        (pp.mulScalarAction a b).symm
  dsimp [indCPAFixedRealOracle, OracleEnv.withFixedOneShotSeed, reductionOracle,
    indCPARealSeedAnswer, indCPAAfterChallenge]
  congr
  funext name querySec used query
  cases name
  change Carrier × Carrier at query
  cases used
  · simp only [Bool.false_eq_true, ↓reduceIte,
      CryptoLib.Core.Assumption.DL.DDH.realChallenge]
    calc
      _ = PMF.pure ((some (b • pp.generator,
          (if rightMessage then query.2 else query.1) +
            b • (a • pp.generator)), true)) :=
        PMF.pure_map
          (fun response : Option (Carrier × Carrier) =>
            (response, true))
          (some (b • pp.generator,
            (if rightMessage then query.2 else query.1) +
              b • (a • pp.generator)))
      _ = _ := by
        rw [hshared]
        rfl
  · simp only [↓reduceIte]
    exact PMF.pure_map _ _

/-- In the real DDH game, the reduction perfectly simulates the selected
ElGamal IND-CPA challenge game. -/
theorem indCPASecurityGame_eq_realReductionGame
    (F : Family M Parameter Scalar Carrier)
    (adversary : CryptoLib.Core.Infrastructure.Complexity.OracleMachine M
      (PublicInput Parameter (PublicKey (Carrier := Carrier)))
      (fun _sec _input => Bool)
      (indCPAOracleSpec
        (Message (Carrier := Carrier)) (Ciphertext (Carrier := Carrier))))
    (rightMessage : Bool) :
    indCPASecurityGame (scheme F) adversary rightMessage =
      realReductionGame F adversary rightMessage := by
  funext sec
  cases rightMessage <;>
    simp only [indCPASecurityGame, Bool.false_eq_true, if_false, if_true,
      CryptoLib.Core.Infrastructure.GameBased.OracleDistinguishing.leftSecurityGame,
      CryptoLib.Core.Infrastructure.GameBased.OracleDistinguishing.rightSecurityGame,
      CryptoLib.Core.Infrastructure.GameBased.OracleDistinguishing.securityGame,
      indCPAProblem, realReductionGame, semanticReductionGame,
      CryptoLib.Core.Assumption.DL.DDH.realSample_eq, scheme_setupDist,
      scheme_keygenDist, semanticDDHReduction,
      PMF.bind_bind, PMF.pure_bind]
  all_goals
    congr 1
    funext parameter
    let pp := F.publicParam parameter
    congr 1
    funext a
    change adversary.runWithEnv sec
        (indCPAPublicInput F sec parameter (pp.smul.smul a pp.generator))
        (indCPAEncryptionOracle (scheme F) sec
          (indCPAPublicInput F sec parameter (pp.smul.smul a pp.generator)) _) = _
    rw [runWithEnv_indCPAEncryptionOracle_eq_bind_fixedReal]
    congr 1
    funext b
    rw [fixedRealOracle_eq_reductionOracle_realChallenge F]
    rfl

end CryptoLib.Instantiation.Primitive.Encryption.AsymmetricEncryption.ElGamal

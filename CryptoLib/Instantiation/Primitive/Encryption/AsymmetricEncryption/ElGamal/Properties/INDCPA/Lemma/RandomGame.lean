import CryptoLib.Instantiation.Primitive.Encryption.AsymmetricEncryption.ElGamal.Properties.INDCPA.Definition.RandomGame

/-! # Random-game oracle and distribution lemmas -/

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

private theorem randomMaskResponse_eq_uniform
    (pp : PublicParam.{uCost, uScalar, uGroup} M Scalar Carrier)
    (firstComponent message : Carrier) :
    PMF.map (fun z => (some (firstComponent, pp.addGroup.add message z) :
        Option (Carrier × Carrier)))
        (@CryptoLib.Core.Infrastructure.Probability.uniformPMF
          Carrier pp.fintypeCarrier ⟨pp.addGroup.zero⟩) =
      PMF.map (fun z => (some (firstComponent, z) :
        Option (Carrier × Carrier)))
        (@CryptoLib.Core.Infrastructure.Probability.uniformPMF
          Carrier pp.fintypeCarrier ⟨pp.addGroup.zero⟩) := by
  letI : AddGroup Carrier := pp.addGroup
  letI : Fintype Carrier := pp.fintypeCarrier
  letI : Nonempty Carrier := ⟨pp.addGroup.zero⟩
  have hshift := CryptoLib.Core.Infrastructure.Probability.map_add_left_uniformPMF
    pp.Carrier message
  have hmapped := congrArg
      (PMF.map (fun z => (some (firstComponent, z) :
      Option (Carrier × Carrier)))) hshift
  simpa only [PMF.map_comp, Function.comp_apply] using hmapped

private theorem lazyRandomMaskOracle_eq_uniformCiphertextOracle
    (F : Family M Parameter Scalar Carrier)
    (sec : CryptoLib.Core.SecPar)
    (parameter : Parameter) (pk : Carrier) (rightMessage : Bool) :
    indCPALazyRandomMaskOracle F sec parameter pk rightMessage =
      indCPAUniformCiphertextOracle F sec parameter pk := by
  let pp := F.publicParam parameter
  letI : AddGroup Carrier := pp.addGroup
  letI : SMul Scalar Carrier := pp.smul
  dsimp [indCPALazyRandomMaskOracle, indCPAUniformCiphertextOracle,
    OracleEnv.withLazyOneShotSeed, indCPARandomMaskAnswer,
    indCPAUniformCiphertextAnswer, indCPAAfterChallenge]
  congr
  funext name querySec used query
  cases name
  cases used
  · change Carrier × Carrier at query
    simp only [Bool.false_eq_true, if_false, indCPARandomSeedDist,
      PMF.bind_bind, PMF.pure_bind, PMF.pure_map]
    congr 1
    funext r
    have hresponse := randomMaskResponse_eq_uniform pp
      (r • pp.generator) (if rightMessage then query.2 else query.1)
    have hmapped := congrArg
      (PMF.map (fun response => (response, true))) hresponse
    calc
      PMF.bind (@CryptoLib.Core.Infrastructure.Probability.uniformPMF
          Carrier pp.fintypeCarrier ⟨pp.addGroup.zero⟩)
          (fun z => PMF.map (fun response => (response, true))
            (PMF.pure (some (r • pp.generator,
              (if rightMessage then query.2 else query.1) + z)))) =
        PMF.map
          (fun z => ((some (r • pp.generator,
            (if rightMessage then query.2 else query.1) + z) :
              Option (Carrier × Carrier)), true))
          (@CryptoLib.Core.Infrastructure.Probability.uniformPMF
            Carrier pp.fintypeCarrier ⟨pp.addGroup.zero⟩) := by
            rw [← PMF.bind_pure_comp]
            congr 1
            funext z
            exact PMF.pure_map _ _
      _ = PMF.map
          (fun z => ((some (r • pp.generator, z) :
            Option (Carrier × Carrier)), true))
          (@CryptoLib.Core.Infrastructure.Probability.uniformPMF
            Carrier pp.fintypeCarrier ⟨pp.addGroup.zero⟩) := by
            simpa only [PMF.map_comp, Function.comp_apply] using hmapped
      _ = PMF.bind (@CryptoLib.Core.Infrastructure.Probability.uniformPMF
          Carrier pp.fintypeCarrier ⟨pp.addGroup.zero⟩)
          (fun z => PMF.pure
            ((some (r • pp.generator, z) :
              Option (Carrier × Carrier)), true)) := by
            symm
            simpa only [Function.comp_apply] using
              PMF.bind_pure_comp
                (fun z => ((some (r • pp.generator, z) :
                  Option (Carrier × Carrier)), true))
                (@CryptoLib.Core.Infrastructure.Probability.uniformPMF
                  Carrier pp.fintypeCarrier ⟨pp.addGroup.zero⟩)
  · rfl

private theorem fixedRandomMaskOracle_eq_reductionOracle_randomChallenge
    (F : Family M Parameter Scalar Carrier)
    (sec : CryptoLib.Core.SecPar)
    (parameter : Parameter) (a b : Scalar) (z : Carrier)
    (rightMessage : Bool) :
    indCPAFixedRandomMaskOracle F sec parameter
        ((F.publicParam parameter).smul.smul a
          (F.publicParam parameter).generator) rightMessage (b, z) =
      reductionOracle F sec
        (CryptoLib.Core.Assumption.DL.DDH.randomChallenge F parameter a b z)
        rightMessage := by
  dsimp [indCPAFixedRandomMaskOracle, OracleEnv.withFixedOneShotSeed,
    reductionOracle, indCPARandomMaskAnswer, indCPAAfterChallenge]
  congr
  funext name querySec used query
  cases name
  cases used
  · simp only [Bool.false_eq_true, ↓reduceIte]
    exact PMF.pure_map _ _
  · simp only [↓reduceIte]
    exact PMF.pure_map _ _

private theorem runWithEnv_lazyRandomMaskOracle_eq_bind_fixedRandom
    (F : Family M Parameter Scalar Carrier)
    (adversary : CryptoLib.Core.Infrastructure.Complexity.OracleMachine M
      (PublicInput Parameter (PublicKey (Carrier := Carrier)))
      (fun _sec _input => Bool)
      (indCPAOracleSpec
        (Message (Carrier := Carrier)) (Ciphertext (Carrier := Carrier))))
    (sec : CryptoLib.Core.SecPar)
    (parameter : Parameter) (pk : Carrier) (rightMessage : Bool) :
    adversary.runWithEnv sec (indCPAPublicInput F sec parameter pk)
        (indCPALazyRandomMaskOracle F sec parameter pk rightMessage) =
      PMF.bind (indCPARandomSeedDist (F.publicParam parameter)) fun seed =>
        adversary.runWithEnv sec (indCPAPublicInput F sec parameter pk)
          (indCPAFixedRandomMaskOracle F sec parameter pk rightMessage seed) := by
  let pp := F.publicParam parameter
  letI : Nonempty (Scalar × Carrier) :=
    ⟨(pp.commMonoidScalar.one, pp.addGroup.zero)⟩
  unfold CryptoLib.Core.Infrastructure.Complexity.OracleMachine.runWithEnv
  simp only [indCPALazyRandomMaskOracle, indCPAFixedRandomMaskOracle]
  rw [OracleEnv.runWithEnv_withLazyOneShotSeed]
  rw [PMF.map_bind]

/-- In the random DDH game, either selected message reduces to the same
message-independent random-ciphertext hybrid. -/
theorem randomReductionGame_eq_randomHybridGame
    (F : Family M Parameter Scalar Carrier)
    (adversary : CryptoLib.Core.Infrastructure.Complexity.OracleMachine M
      (PublicInput Parameter (PublicKey (Carrier := Carrier)))
      (fun _sec _input => Bool)
      (indCPAOracleSpec
        (Message (Carrier := Carrier)) (Ciphertext (Carrier := Carrier))))
    (rightMessage : Bool) :
    randomReductionGame F adversary rightMessage =
      randomHybridGame F adversary := by
  funext sec
  simp only [randomReductionGame, semanticReductionGame,
    CryptoLib.Core.Assumption.DL.DDH.randomSample_eq, semanticDDHReduction,
    randomHybridGame,
    PMF.bind_bind, PMF.pure_bind]
  congr 1
  funext parameter
  let pp := F.publicParam parameter
  congr 1
  funext a
  rw [← lazyRandomMaskOracle_eq_uniformCiphertextOracle
    F sec parameter (pp.smul.smul a pp.generator) rightMessage]
  rw [runWithEnv_lazyRandomMaskOracle_eq_bind_fixedRandom F]
  simp only [indCPARandomSeedDist, PMF.bind_bind, PMF.pure_bind]
  congr 1
  funext b
  congr 1
  funext z
  rw [fixedRandomMaskOracle_eq_reductionOracle_randomChallenge F]
  rfl

end CryptoLib.Instantiation.Primitive.Encryption.AsymmetricEncryption.ElGamal

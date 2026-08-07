import CryptoLib.Core.Infrastructure.Computation.Oracle.DeferredSampling
import CryptoLib.Instantiation.Primitive.Encryption.AsymmetricEncryption.ElGamal.Properties.INDCPA.Definition.ReductionGame

/-! # Random-mask oracle and common hybrid-game definitions -/

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

noncomputable def indCPARandomSeedDist
    (pp : PublicParam.{uCost, uScalar, uGroup} M Scalar Carrier) :
    PMF (Scalar × Carrier) :=
  PMF.bind
      (@CryptoLib.Core.Infrastructure.Probability.uniformPMF
        Scalar pp.fintypeScalar ⟨pp.commMonoidScalar.one⟩) fun r =>
    PMF.bind
        (@CryptoLib.Core.Infrastructure.Probability.uniformPMF
          Carrier pp.fintypeCarrier ⟨pp.addGroup.zero⟩) fun z =>
      PMF.pure (r, z)

noncomputable def indCPARandomMaskAnswer
    (F : Family M Parameter Scalar Carrier)
    (sec : CryptoLib.Core.SecPar)
    (parameter : Parameter) (pk : Carrier) (rightMessage : Bool)
    (seed : Scalar × Carrier)
    (name : (indCPAOracleSpec (Message (Carrier := Carrier)) (Ciphertext (Carrier := Carrier)) sec
      (indCPAPublicInput F sec parameter pk)).Name)
    (_querySec : CryptoLib.Core.SecPar)
    (query : (indCPAOracleSpec (Message (Carrier := Carrier)) (Ciphertext (Carrier := Carrier)) sec
      (indCPAPublicInput F sec parameter pk)).Query name) :
    PMF ((indCPAOracleSpec (Message (Carrier := Carrier)) (Ciphertext (Carrier := Carrier)) sec
      (indCPAPublicInput F sec parameter pk)).Response name) := by
  cases name
  let pp := F.publicParam parameter
  change Carrier × Carrier at query
  change PMF (Option (Carrier × Carrier))
  exact PMF.pure
    (some (pp.smul.smul seed.1 pp.generator,
      pp.addGroup.add (if rightMessage then query.2 else query.1) seed.2))

noncomputable def indCPAUniformCiphertextAnswer
    (F : Family M Parameter Scalar Carrier)
    (sec : CryptoLib.Core.SecPar)
    (parameter : Parameter) (pk : Carrier) (seed : Scalar × Carrier)
    (name : (indCPAOracleSpec (Message (Carrier := Carrier)) (Ciphertext (Carrier := Carrier)) sec
      (indCPAPublicInput F sec parameter pk)).Name)
    (_querySec : CryptoLib.Core.SecPar)
    (_query : (indCPAOracleSpec (Message (Carrier := Carrier)) (Ciphertext (Carrier := Carrier)) sec
      (indCPAPublicInput F sec parameter pk)).Query name) :
    PMF ((indCPAOracleSpec (Message (Carrier := Carrier)) (Ciphertext (Carrier := Carrier)) sec
      (indCPAPublicInput F sec parameter pk)).Response name) := by
  cases name
  exact PMF.pure
    (some ((F.publicParam parameter).smul.smul seed.1
      (F.publicParam parameter).generator, seed.2))

noncomputable def indCPAFixedRandomMaskOracle
    (F : Family M Parameter Scalar Carrier)
    (sec : CryptoLib.Core.SecPar)
    (parameter : Parameter) (pk : Carrier) (rightMessage : Bool)
    (seed : Scalar × Carrier) :
    OracleEnv (indCPAOracleSpec (Message (Carrier := Carrier)) (Ciphertext (Carrier := Carrier)) sec
      (indCPAPublicInput F sec parameter pk)) :=
  OracleEnv.withFixedOneShotSeed
    (indCPARandomMaskAnswer F sec parameter pk rightMessage)
    (indCPAAfterChallenge F sec parameter pk) seed

noncomputable def indCPALazyRandomMaskOracle
    (F : Family M Parameter Scalar Carrier)
    (sec : CryptoLib.Core.SecPar)
    (parameter : Parameter) (pk : Carrier) (rightMessage : Bool) :
    OracleEnv (indCPAOracleSpec (Message (Carrier := Carrier)) (Ciphertext (Carrier := Carrier)) sec
      (indCPAPublicInput F sec parameter pk)) :=
  OracleEnv.withLazyOneShotSeed (indCPARandomSeedDist (F.publicParam parameter))
    (indCPARandomMaskAnswer F sec parameter pk rightMessage)
    (indCPAAfterChallenge F sec parameter pk)

noncomputable def indCPAUniformCiphertextOracle
    (F : Family M Parameter Scalar Carrier)
    (sec : CryptoLib.Core.SecPar)
    (parameter : Parameter) (pk : Carrier) :
    OracleEnv (indCPAOracleSpec (Message (Carrier := Carrier)) (Ciphertext (Carrier := Carrier)) sec
      (indCPAPublicInput F sec parameter pk)) :=
  OracleEnv.withLazyOneShotSeed (indCPARandomSeedDist (F.publicParam parameter))
    (indCPAUniformCiphertextAnswer F sec parameter pk)
    (indCPAAfterChallenge F sec parameter pk)

/-- The common random-ciphertext hybrid. Its challenge response is independent
of which challenge message the adversary selected. -/
noncomputable def randomHybridGame
    (F : Family M Parameter Scalar Carrier)
    (adversary : CryptoLib.Core.Infrastructure.Complexity.OracleMachine M
      (PublicInput Parameter (PublicKey (Carrier := Carrier)))
      (fun _sec _input => Bool)
      (indCPAOracleSpec
        (Message (Carrier := Carrier)) (Ciphertext (Carrier := Carrier)))) :
    CryptoLib.Core.Infrastructure.Computation.Game Bool :=
  fun sec =>
    PMF.bind (F.setupDist sec) fun parameter =>
      let pp := F.publicParam parameter
      PMF.bind
          (@CryptoLib.Core.Infrastructure.Probability.uniformPMF
            Scalar pp.fintypeScalar ⟨pp.commMonoidScalar.one⟩) fun a =>
        adversary.runWithEnv sec
          (indCPAPublicInput F sec parameter (pp.smul.smul a pp.generator))
          (indCPAUniformCiphertextOracle F sec parameter
            (pp.smul.smul a pp.generator))

end CryptoLib.Instantiation.Primitive.Encryption.AsymmetricEncryption.ElGamal

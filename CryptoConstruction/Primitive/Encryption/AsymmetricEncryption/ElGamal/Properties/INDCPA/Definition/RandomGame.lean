import Crypto.Infrastructure.Computation.Oracle.DeferredSampling
import CryptoConstruction.Primitive.Encryption.AsymmetricEncryption.ElGamal.Properties.INDCPA.Definition.ReductionGame

/-! # Random-mask oracle and common hybrid-game definitions -/

namespace CryptoConstruction.Primitive.Encryption.AsymmetricEncryption.ElGamal

open Crypto.Infrastructure.Computation.Cost
open Crypto.Infrastructure.Computation
open Crypto.Infrastructure.Computation.Oracle
open Crypto.Primitive.Encryption.AsymmetricEncryption
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
      (@Crypto.Infrastructure.Probability.uniformPMF
        Scalar pp.fintypeScalar ⟨pp.commMonoidScalar.one⟩) fun r =>
    PMF.bind
        (@Crypto.Infrastructure.Probability.uniformPMF
          Carrier pp.fintypeCarrier ⟨pp.addGroup.zero⟩) fun z =>
      PMF.pure (r, z)

noncomputable def indCPARandomMaskAnswer
    (F : Family M Parameter Scalar Carrier)
    (sec : Crypto.SecPar)
    (parameter : Parameter) (pk : Carrier) (rightMessage : Bool)
    (seed : Scalar × Carrier)
    (name : (indCPAOracleSpec (Message (Carrier := Carrier)) (Ciphertext (Carrier := Carrier)) sec
      (indCPAPublicInput F sec parameter pk)).Name)
    (_querySec : Crypto.SecPar)
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
    (sec : Crypto.SecPar)
    (parameter : Parameter) (pk : Carrier) (seed : Scalar × Carrier)
    (name : (indCPAOracleSpec (Message (Carrier := Carrier)) (Ciphertext (Carrier := Carrier)) sec
      (indCPAPublicInput F sec parameter pk)).Name)
    (_querySec : Crypto.SecPar)
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
    (sec : Crypto.SecPar)
    (parameter : Parameter) (pk : Carrier) (rightMessage : Bool)
    (seed : Scalar × Carrier) :
    OracleEnv (indCPAOracleSpec (Message (Carrier := Carrier)) (Ciphertext (Carrier := Carrier)) sec
      (indCPAPublicInput F sec parameter pk)) :=
  OracleEnv.withFixedOneShotSeed
    (indCPARandomMaskAnswer F sec parameter pk rightMessage)
    (indCPAAfterChallenge F sec parameter pk) seed

noncomputable def indCPALazyRandomMaskOracle
    (F : Family M Parameter Scalar Carrier)
    (sec : Crypto.SecPar)
    (parameter : Parameter) (pk : Carrier) (rightMessage : Bool) :
    OracleEnv (indCPAOracleSpec (Message (Carrier := Carrier)) (Ciphertext (Carrier := Carrier)) sec
      (indCPAPublicInput F sec parameter pk)) :=
  OracleEnv.withLazyOneShotSeed (indCPARandomSeedDist (F.publicParam parameter))
    (indCPARandomMaskAnswer F sec parameter pk rightMessage)
    (indCPAAfterChallenge F sec parameter pk)

noncomputable def indCPAUniformCiphertextOracle
    (F : Family M Parameter Scalar Carrier)
    (sec : Crypto.SecPar)
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
    (adversary : Crypto.Infrastructure.Complexity.OracleMachine M
      (PublicInput Parameter (PublicKey (Carrier := Carrier)))
      (fun _sec _input => Bool)
      (indCPAOracleSpec
        (Message (Carrier := Carrier)) (Ciphertext (Carrier := Carrier)))) :
    Crypto.Infrastructure.Computation.Game Bool :=
  fun sec =>
    PMF.bind (F.setupDist sec) fun parameter =>
      let pp := F.publicParam parameter
      PMF.bind
          (@Crypto.Infrastructure.Probability.uniformPMF
            Scalar pp.fintypeScalar ⟨pp.commMonoidScalar.one⟩) fun a =>
        adversary.runWithEnv sec
          (indCPAPublicInput F sec parameter (pp.smul.smul a pp.generator))
          (indCPAUniformCiphertextOracle F sec parameter
            (pp.smul.smul a pp.generator))

end CryptoConstruction.Primitive.Encryption.AsymmetricEncryption.ElGamal

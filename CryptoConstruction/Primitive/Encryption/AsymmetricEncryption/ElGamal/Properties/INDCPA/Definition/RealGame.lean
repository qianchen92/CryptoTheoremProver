import Crypto.Infrastructure.Computation.Oracle.DeferredSampling
import CryptoConstruction.Primitive.Encryption.AsymmetricEncryption.ElGamal.Properties.INDCPA.Definition.ReductionGame

/-! # Real ElGamal challenge-oracle definitions -/

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

noncomputable def indCPARealSeedAnswer
    (F : Family M Parameter Scalar Carrier)
    (sec : Crypto.SecPar)
    (parameter : Parameter)
    (pk : Carrier) (rightMessage : Bool) (r : Scalar)
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
    (some (pp.smul.smul r pp.generator,
      pp.addGroup.add (if rightMessage then query.2 else query.1)
        (pp.smul.smul r pk)))

noncomputable def indCPAFixedRealOracle
    (F : Family M Parameter Scalar Carrier)
    (sec : Crypto.SecPar)
    (parameter : Parameter)
    (pk : Carrier) (rightMessage : Bool) (r : Scalar) :
    OracleEnv (indCPAOracleSpec (Message (Carrier := Carrier)) (Ciphertext (Carrier := Carrier)) sec
      (indCPAPublicInput F sec parameter pk)) :=
  OracleEnv.withFixedOneShotSeed
    (indCPARealSeedAnswer F sec parameter pk rightMessage)
    (indCPAAfterChallenge F sec parameter pk) r

noncomputable def indCPALazyRealOracle
    (F : Family M Parameter Scalar Carrier)
    (sec : Crypto.SecPar)
    (parameter : Parameter) (pk : Carrier) (rightMessage : Bool) :
    OracleEnv (indCPAOracleSpec (Message (Carrier := Carrier)) (Ciphertext (Carrier := Carrier)) sec
      (indCPAPublicInput F sec parameter pk)) :=
  OracleEnv.withLazyOneShotSeed
    (@Crypto.Infrastructure.Probability.uniformPMF
      Scalar (F.publicParam parameter).fintypeScalar
      ⟨(F.publicParam parameter).commMonoidScalar.one⟩)
    (indCPARealSeedAnswer F sec parameter pk rightMessage)
    (indCPAAfterChallenge F sec parameter pk)

end CryptoConstruction.Primitive.Encryption.AsymmetricEncryption.ElGamal

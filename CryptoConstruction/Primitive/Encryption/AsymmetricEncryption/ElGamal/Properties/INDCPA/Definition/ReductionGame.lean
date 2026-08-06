import CryptoConstruction.Primitive.Encryption.AsymmetricEncryption.ElGamal.Properties.INDCPA.Definition.Reduction

/-! # Semantic DDH reduction games and shared IND-CPA inputs -/

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

/-- Compose the pure reduction specification with an arbitrary DDH sample. -/
noncomputable def semanticReductionGame
    (F : Family M Parameter Scalar Carrier)
    (sample : Crypto.SecPar → PMF
      (Crypto.Assumption.DL.DDH.ChallengeInput F))
    (adversary : Crypto.Infrastructure.Complexity.OracleMachine M
      (PublicInput Parameter (PublicKey (Carrier := Carrier)))
      (fun _sec _input => Bool)
      (indCPAOracleSpec
        (Message (Carrier := Carrier)) (Ciphertext (Carrier := Carrier))))
    (rightMessage : Bool) :
    Crypto.Infrastructure.Computation.Game Bool :=
  fun sec => PMF.bind (sample sec)
    (semanticDDHReduction F adversary rightMessage sec)

/-- Run the semantic reduction against genuine DDH tuples. -/
noncomputable def realReductionGame
    (F : Family M Parameter Scalar Carrier)
    (adversary : Crypto.Infrastructure.Complexity.OracleMachine M
      (PublicInput Parameter (PublicKey (Carrier := Carrier)))
      (fun _sec _input => Bool)
      (indCPAOracleSpec
        (Message (Carrier := Carrier)) (Ciphertext (Carrier := Carrier))))
    (rightMessage : Bool) :
    Crypto.Infrastructure.Computation.Game Bool :=
  semanticReductionGame F (Crypto.Assumption.DL.DDH.realSample F)
    adversary rightMessage

/-- Run the semantic reduction against random DDH tuples. -/
noncomputable def randomReductionGame
    (F : Family M Parameter Scalar Carrier)
    (adversary : Crypto.Infrastructure.Complexity.OracleMachine M
      (PublicInput Parameter (PublicKey (Carrier := Carrier)))
      (fun _sec _input => Bool)
      (indCPAOracleSpec
        (Message (Carrier := Carrier)) (Ciphertext (Carrier := Carrier))))
    (rightMessage : Bool) :
    Crypto.Infrastructure.Computation.Game Bool :=
  semanticReductionGame F (Crypto.Assumption.DL.DDH.randomSample F)
    adversary rightMessage

/-- Public IND-CPA input assembled from a setup parameter and public key. -/
def indCPAPublicInput
    (_F : Family M Parameter Scalar Carrier)
    (sec : Crypto.SecPar)
    (parameter : Parameter) (pk : Carrier) :
    PublicInput Parameter (PublicKey (Carrier := Carrier)) sec where
  param := parameter
  publicKey := pk

/-- Every IND-CPA query after the one-shot challenge receives no response. -/
noncomputable def indCPAAfterChallenge
    (F : Family M Parameter Scalar Carrier)
    (sec : Crypto.SecPar)
    (parameter : Parameter) (pk : Carrier)
    (name : (indCPAOracleSpec
      (Message (Carrier := Carrier)) (Ciphertext (Carrier := Carrier)) sec
      (indCPAPublicInput F sec parameter pk)).Name)
    (_querySec : Crypto.SecPar)
    (_query : (indCPAOracleSpec
      (Message (Carrier := Carrier)) (Ciphertext (Carrier := Carrier)) sec
      (indCPAPublicInput F sec parameter pk)).Query name) :
    PMF ((indCPAOracleSpec
      (Message (Carrier := Carrier)) (Ciphertext (Carrier := Carrier)) sec
      (indCPAPublicInput F sec parameter pk)).Response name) := by
  cases name
  exact PMF.pure none

end CryptoConstruction.Primitive.Encryption.AsymmetricEncryption.ElGamal

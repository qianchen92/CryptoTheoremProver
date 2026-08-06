import CryptoConstruction.Primitive.Encryption.AsymmetricEncryption.ElGamal.Scheme
import Crypto.Primitive.Encryption.AsymmetricEncryption.Properties.INDCPA

/-! # Endpoint aliases for the ElGamal IND-CPA hybrid -/

namespace CryptoConstruction.Primitive.Encryption.AsymmetricEncryption.ElGamal

open Crypto.Infrastructure.Computation.Cost
open Crypto.Primitive.Encryption.AsymmetricEncryption

universe uCost uParameter uScalar uGroup

variable
    {M : CostModel.{uCost}}
    {Parameter : Type uParameter}
    {Scalar : Type uScalar}
    {Carrier : Type uGroup}

/-- `G₀` is definitionally the real, left-message IND-CPA game. -/
noncomputable def G₀
    (F : Family M Parameter Scalar Carrier)
    (adversary : Crypto.Infrastructure.Complexity.OracleMachine M
      (PublicInput Parameter (PublicKey (Carrier := Carrier)))
      (fun _sec _input => Bool)
      (indCPAOracleSpec
        (Message (Carrier := Carrier)) (Ciphertext (Carrier := Carrier)))) :
    Crypto.Infrastructure.Computation.Game Bool :=
  indCPASecurityGame (scheme F) adversary false

/-- `G₁` is definitionally the random, right-message IND-CPA game. -/
noncomputable def G₁
    (F : Family M Parameter Scalar Carrier)
    (adversary : Crypto.Infrastructure.Complexity.OracleMachine M
      (PublicInput Parameter (PublicKey (Carrier := Carrier)))
      (fun _sec _input => Bool)
      (indCPAOracleSpec
        (Message (Carrier := Carrier)) (Ciphertext (Carrier := Carrier)))) :
    Crypto.Infrastructure.Computation.Game Bool :=
  indCPASecurityGame (scheme F) adversary true

end CryptoConstruction.Primitive.Encryption.AsymmetricEncryption.ElGamal

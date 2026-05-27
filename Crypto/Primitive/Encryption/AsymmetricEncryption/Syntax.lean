import Crypto.Infrastructure.Asymptotic.SecurityParameter
import Mathlib.Probability.ProbabilityMassFunction.Basic

namespace Crypto.Primitive.Encryption.AsymmetricEncryption

universe uSecPar uParam uPublicKey uSecretKey uMessage uCiphertext

/-- Syntax for asymmetric encryption schemes. -/
structure Scheme
    (SecPar : Type uSecPar)
    (Param : Type uParam)
    (PublicKey : Param → Type uPublicKey)
    (SecretKey : Param → Type uSecretKey)
    (Message : Param → Type uMessage)
    (Ciphertext : Param → Type uCiphertext) where
  setup : SecPar → PMF Param
  keygen :
    (pp : Param) →
    PMF (PublicKey pp × SecretKey pp)
  encrypt :
    (pp : Param) →
    PublicKey pp →
    Message pp →
    PMF (Ciphertext pp)
  decrypt :
    (pp : Param) →
    SecretKey pp →
    Ciphertext pp →
    Message pp

end Crypto.Primitive.Encryption.AsymmetricEncryption

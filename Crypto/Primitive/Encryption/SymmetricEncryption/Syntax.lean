import Crypto.Infrastructure.Asymptotic.SecurityParameter
import Mathlib.Probability.ProbabilityMassFunction.Basic

namespace Crypto.Primitive.Encryption.SymmetricEncryption

universe uParam uMessage uCiphertext uKey

/-- Syntax for symmetric encryption schemes. -/
structure Scheme
    (Param : Crypto.SecPar → Type uParam)
    (Key : {sec : Crypto.SecPar} → Param sec → Type uKey)
    (Message : {sec : Crypto.SecPar} → Param sec → Type uMessage)
    (Ciphertext : {sec : Crypto.SecPar} → Param sec → Type uCiphertext) where
  setup : (sec : Crypto.SecPar) → PMF (Param sec)
  keygen : {sec : Crypto.SecPar} → (pp : Param sec) → PMF (Key pp)
  encrypt :
    {sec : Crypto.SecPar} →
    (pp : Param sec) →
    Key pp →
    Message pp →
    PMF (Ciphertext pp)
  decrypt :
    {sec : Crypto.SecPar} →
    (pp : Param sec) →
    Key pp →
    Ciphertext pp →
    Message pp

end Crypto.Primitive.Encryption.SymmetricEncryption

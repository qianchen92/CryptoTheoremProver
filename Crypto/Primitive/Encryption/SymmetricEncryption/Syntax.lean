import Crypto.Foundation.SecurityParameter
import Mathlib.Probability.ProbabilityMassFunction.Basic

namespace Crypto.Primitive.Encryption.SymmetricEncryption

universe uMessage uCiphertext uKey

/-- Syntax for symmetric encryption schemes. -/
structure Scheme
    (Key : Type uKey) (Message : Type uMessage) (Ciphertext : Type uCiphertext) where
  keygen : Crypto.SecPar → PMF Key
  encrypt : Crypto.SecPar → Key → Message → PMF Ciphertext
  decrypt : Crypto.SecPar → Key → Ciphertext → Message

end Crypto.Primitive.Encryption.SymmetricEncryption

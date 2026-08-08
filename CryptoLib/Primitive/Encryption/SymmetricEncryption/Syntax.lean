import CryptoLib.Core.Infrastructure.SecurityParameter
import CryptoLib.Core.Infrastructure.Computation.Cost.Randomized
import Mathlib.Probability.ProbabilityMassFunction.Basic

namespace CryptoLib.Primitive.Encryption.SymmetricEncryption

open CryptoLib.Core.Infrastructure.Computation.Cost

universe uCost uSecPar uParam uMessage uCiphertext uKey

variable
    (M : CostModel.{uCost})
    (SecPar : Type uSecPar)
    (Param : Type uParam)
    (Key : Param → Type uKey)
    (Message : Param → Type uMessage)
    (Ciphertext : Param → Type uCiphertext)

/--
Syntax for cost-annotated symmetric-encryption schemes.

Every execution path, including decryption, carries its exact resource cost in
the same model. Correctness and security definitions erase costs only at the
observation point through the accessors below.
-/
structure Scheme where
  setup :
    SecPar →
      RandCosted M Param
  keygen :
    (pp : Param) →
      RandCosted M (Key pp)
  encrypt :
    (pp : Param) →
    Key pp →
    Message pp →
      RandCosted M (Ciphertext pp)
  decrypt :
    (pp : Param) →
    Key pp →
    Ciphertext pp →
      RandCosted M (Message pp)

namespace Scheme

variable
    {M SecPar Param Key Message Ciphertext}
    (E : Scheme M SecPar Param Key Message Ciphertext)

/-- Ordinary setup distribution observed by correctness and security notions. -/
noncomputable def setupDist (sec : SecPar) : PMF Param :=
  RandCosted.valueDist (E.setup sec)

/-- Ordinary key-generation distribution with execution costs erased. -/
noncomputable def keygenDist (pp : Param) : PMF (Key pp) :=
  RandCosted.valueDist (E.keygen pp)

/-- Ordinary encryption distribution with execution costs erased. -/
noncomputable def encryptDist
    (pp : Param) (key : Key pp) (message : Message pp) :
    PMF (Ciphertext pp) :=
  RandCosted.valueDist (E.encrypt pp key message)

/-- Ordinary decryption distribution with execution costs erased. -/
noncomputable def decryptDist
    (pp : Param) (key : Key pp) (ciphertext : Ciphertext pp) :
    PMF (Message pp) :=
  RandCosted.valueDist (E.decrypt pp key ciphertext)

end Scheme

end CryptoLib.Primitive.Encryption.SymmetricEncryption

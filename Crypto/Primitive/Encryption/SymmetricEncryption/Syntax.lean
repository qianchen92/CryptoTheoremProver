import Crypto.Infrastructure.Asymptotic.SecurityParameter
import Crypto.Infrastructure.Computation.Cost.Distribution
import Mathlib.Probability.ProbabilityMassFunction.Basic

namespace Crypto.Primitive.Encryption.SymmetricEncryption

universe uSecPar uParam uMessage uCiphertext uKey

/--
Syntax for cost-annotated symmetric-encryption schemes.

Every randomized execution path carries its cost, and deterministic decryption
returns a costed value.  Correctness and security definitions erase costs only
at the observation point through the accessors below.
-/
structure Scheme
    (SecPar : Type uSecPar)
    (Param : Type uParam)
    (Key : Param → Type uKey)
    (Message : Param → Type uMessage)
    (Ciphertext : Param → Type uCiphertext) where
  setup :
    SecPar →
      Crypto.Infrastructure.Computation.Cost.RandCosted Param
  keygen :
    (pp : Param) →
      Crypto.Infrastructure.Computation.Cost.RandCosted (Key pp)
  encrypt :
    (pp : Param) →
    Key pp →
    Message pp →
      Crypto.Infrastructure.Computation.Cost.RandCosted (Ciphertext pp)
  decrypt :
    (pp : Param) →
    Key pp →
    Ciphertext pp →
      Crypto.Infrastructure.Computation.Cost.Costed (Message pp)

namespace Scheme

/-- Ordinary setup distribution observed by correctness and security notions. -/
noncomputable def setupDist
    {SecPar : Type uSecPar}
    {Param : Type uParam}
    {Key : Param → Type uKey}
    {Message : Param → Type uMessage}
    {Ciphertext : Param → Type uCiphertext}
    (E : Scheme SecPar Param Key Message Ciphertext)
    (sec : SecPar) : PMF Param :=
  Crypto.Infrastructure.Computation.Cost.RandCosted.valueDist (E.setup sec)

/-- Ordinary key-generation distribution with execution costs erased. -/
noncomputable def keygenDist
    {SecPar : Type uSecPar}
    {Param : Type uParam}
    {Key : Param → Type uKey}
    {Message : Param → Type uMessage}
    {Ciphertext : Param → Type uCiphertext}
    (E : Scheme SecPar Param Key Message Ciphertext)
    (pp : Param) : PMF (Key pp) :=
  Crypto.Infrastructure.Computation.Cost.RandCosted.valueDist (E.keygen pp)

/-- Ordinary encryption distribution with execution costs erased. -/
noncomputable def encryptDist
    {SecPar : Type uSecPar}
    {Param : Type uParam}
    {Key : Param → Type uKey}
    {Message : Param → Type uMessage}
    {Ciphertext : Param → Type uCiphertext}
    (E : Scheme SecPar Param Key Message Ciphertext)
    (pp : Param) (key : Key pp) (message : Message pp) :
    PMF (Ciphertext pp) :=
  Crypto.Infrastructure.Computation.Cost.RandCosted.valueDist
    (E.encrypt pp key message)

/-- Deterministic decryption result with its execution cost erased. -/
def decryptValue
    {SecPar : Type uSecPar}
    {Param : Type uParam}
    {Key : Param → Type uKey}
    {Message : Param → Type uMessage}
    {Ciphertext : Param → Type uCiphertext}
    (E : Scheme SecPar Param Key Message Ciphertext)
    (pp : Param) (key : Key pp) (ciphertext : Ciphertext pp) :
    Message pp :=
  (E.decrypt pp key ciphertext).val

end Scheme

end Crypto.Primitive.Encryption.SymmetricEncryption

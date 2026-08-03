import Crypto.Infrastructure.Asymptotic.SecurityParameter
import Crypto.Infrastructure.Computation.Cost.Distribution
import Mathlib.Probability.ProbabilityMassFunction.Basic

namespace Crypto.Primitive.Encryption.SymmetricEncryption

universe uCost uSecPar uParam uMessage uCiphertext uKey

/--
Syntax for cost-annotated symmetric-encryption schemes.

Every execution path, including decryption, carries its exact resource cost in
the same model. Correctness and security definitions erase costs only at the
observation point through the accessors below.
-/
structure Scheme
    (M : Crypto.Infrastructure.Computation.Cost.CostModel.{uCost})
    (SecPar : Type uSecPar)
    (Param : Type uParam)
    (Key : Param → Type uKey)
    (Message : Param → Type uMessage)
    (Ciphertext : Param → Type uCiphertext) where
  setup :
    SecPar →
      Crypto.Infrastructure.Computation.Cost.RandCostedT M Param
  keygen :
    (pp : Param) →
      Crypto.Infrastructure.Computation.Cost.RandCostedT M (Key pp)
  encrypt :
    (pp : Param) →
    Key pp →
    Message pp →
      Crypto.Infrastructure.Computation.Cost.RandCostedT M (Ciphertext pp)
  decrypt :
    (pp : Param) →
    Key pp →
    Ciphertext pp →
      Crypto.Infrastructure.Computation.Cost.RandCostedT M (Message pp)

namespace Scheme

/-- Ordinary setup distribution observed by correctness and security notions. -/
noncomputable def setupDist
    {M : Crypto.Infrastructure.Computation.Cost.CostModel.{uCost}}
    {SecPar : Type uSecPar}
    {Param : Type uParam}
    {Key : Param → Type uKey}
    {Message : Param → Type uMessage}
    {Ciphertext : Param → Type uCiphertext}
    (E : Scheme M SecPar Param Key Message Ciphertext)
    (sec : SecPar) : PMF Param :=
  Crypto.Infrastructure.Computation.Cost.RandCostedT.valueDist (E.setup sec)

/-- Ordinary key-generation distribution with execution costs erased. -/
noncomputable def keygenDist
    {M : Crypto.Infrastructure.Computation.Cost.CostModel.{uCost}}
    {SecPar : Type uSecPar}
    {Param : Type uParam}
    {Key : Param → Type uKey}
    {Message : Param → Type uMessage}
    {Ciphertext : Param → Type uCiphertext}
    (E : Scheme M SecPar Param Key Message Ciphertext)
    (pp : Param) : PMF (Key pp) :=
  Crypto.Infrastructure.Computation.Cost.RandCostedT.valueDist (E.keygen pp)

/-- Ordinary encryption distribution with execution costs erased. -/
noncomputable def encryptDist
    {M : Crypto.Infrastructure.Computation.Cost.CostModel.{uCost}}
    {SecPar : Type uSecPar}
    {Param : Type uParam}
    {Key : Param → Type uKey}
    {Message : Param → Type uMessage}
    {Ciphertext : Param → Type uCiphertext}
    (E : Scheme M SecPar Param Key Message Ciphertext)
    (pp : Param) (key : Key pp) (message : Message pp) :
    PMF (Ciphertext pp) :=
  Crypto.Infrastructure.Computation.Cost.RandCostedT.valueDist
    (E.encrypt pp key message)

/-- Ordinary decryption distribution with execution costs erased. -/
noncomputable def decryptDist
    {M : Crypto.Infrastructure.Computation.Cost.CostModel.{uCost}}
    {SecPar : Type uSecPar}
    {Param : Type uParam}
    {Key : Param → Type uKey}
    {Message : Param → Type uMessage}
    {Ciphertext : Param → Type uCiphertext}
    (E : Scheme M SecPar Param Key Message Ciphertext)
    (pp : Param) (key : Key pp) (ciphertext : Ciphertext pp) :
    PMF (Message pp) :=
  Crypto.Infrastructure.Computation.Cost.RandCostedT.valueDist
    (E.decrypt pp key ciphertext)

end Scheme

end Crypto.Primitive.Encryption.SymmetricEncryption

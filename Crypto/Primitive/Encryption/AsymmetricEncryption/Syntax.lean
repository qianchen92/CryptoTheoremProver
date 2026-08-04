import Crypto.Infrastructure.SecurityParameter
import Crypto.Infrastructure.Computation.Cost.Randomized
import Mathlib.Probability.ProbabilityMassFunction.Basic

namespace Crypto.Primitive.Encryption.AsymmetricEncryption

universe uCost uSecPar uParam uPublicKey uSecretKey uMessage uCiphertext

/--
Syntax for cost-annotated public-key encryption schemes.

Every execution path, including decryption, carries its exact resource cost in
the same model. Correctness and security definitions erase costs only at the
observation point through the accessors below.
-/
structure Scheme
    (M : Crypto.Infrastructure.Computation.Cost.CostModel.{uCost})
    (SecPar : Type uSecPar)
    (Param : Type uParam)
    (PublicKey : Param → Type uPublicKey)
    (SecretKey : Param → Type uSecretKey)
    (Message : Param → Type uMessage)
    (Ciphertext : Param → Type uCiphertext) where
  setup :
    SecPar →
      Crypto.Infrastructure.Computation.Cost.RandCosted M Param
  keygen :
    (pp : Param) →
      Crypto.Infrastructure.Computation.Cost.RandCosted M
        (PublicKey pp × SecretKey pp)
  encrypt :
    (pp : Param) →
    PublicKey pp →
    Message pp →
      Crypto.Infrastructure.Computation.Cost.RandCosted M (Ciphertext pp)
  decrypt :
    (pp : Param) →
    SecretKey pp →
    Ciphertext pp →
      Crypto.Infrastructure.Computation.Cost.RandCosted M (Message pp)

namespace Scheme

variable
    {M : Crypto.Infrastructure.Computation.Cost.CostModel.{uCost}}
    {SecPar : Type uSecPar}
    {Param : Type uParam}
    {PublicKey : Param → Type uPublicKey}
    {SecretKey : Param → Type uSecretKey}
    {Message : Param → Type uMessage}
    {Ciphertext : Param → Type uCiphertext}
    (E : Scheme M SecPar Param PublicKey SecretKey Message Ciphertext)

/-- Ordinary setup distribution observed by correctness and security notions. -/
noncomputable def setupDist (sec : SecPar) : PMF Param :=
  Crypto.Infrastructure.Computation.Cost.RandCosted.valueDist (E.setup sec)

/-- Ordinary key-generation distribution with execution costs erased. -/
noncomputable def keygenDist
    (pp : Param) : PMF (PublicKey pp × SecretKey pp) :=
  Crypto.Infrastructure.Computation.Cost.RandCosted.valueDist (E.keygen pp)

/-- Ordinary encryption distribution with execution costs erased. -/
noncomputable def encryptDist
    (pp : Param) (publicKey : PublicKey pp) (message : Message pp) :
    PMF (Ciphertext pp) :=
  Crypto.Infrastructure.Computation.Cost.RandCosted.valueDist
    (E.encrypt pp publicKey message)

/-- Ordinary decryption distribution with execution costs erased. -/
noncomputable def decryptDist
    (pp : Param) (secretKey : SecretKey pp) (ciphertext : Ciphertext pp) :
    PMF (Message pp) :=
  Crypto.Infrastructure.Computation.Cost.RandCosted.valueDist
    (E.decrypt pp secretKey ciphertext)

end Scheme

end Crypto.Primitive.Encryption.AsymmetricEncryption

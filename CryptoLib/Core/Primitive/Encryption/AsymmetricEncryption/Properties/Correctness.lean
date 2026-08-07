import CryptoLib.Core.Primitive.Encryption.AsymmetricEncryption.Syntax
import Mathlib.Probability.ProbabilityMassFunction.Monad

namespace CryptoLib.Core.Primitive.Encryption.AsymmetricEncryption

open CryptoLib.Core.Infrastructure.Computation.Cost

universe uCost uSecPar uParam uPublicKey uSecretKey uMessage uCiphertext

variable
    {M : CostModel.{uCost}}
    {SecPar : Type uSecPar}
    {Param : Type uParam}
    {PublicKey : Param → Type uPublicKey}
    {SecretKey : Param → Type uSecretKey}
    {Message : Param → Type uMessage}
    {Ciphertext : Param → Type uCiphertext}

/-- Perfect correctness for an asymmetric encryption scheme. -/
def Correct
    (E : Scheme M SecPar Param PublicKey SecretKey Message Ciphertext) : Prop :=
  ∀ (sec : SecPar)
    (pp : Param)
    (publicKey : PublicKey pp) (secretKey : SecretKey pp)
    (message : Message pp),
    pp ∈ (E.setupDist sec).support →
    (publicKey, secretKey) ∈ (E.keygenDist pp).support →
    (PMF.bind (E.encryptDist pp publicKey message) fun ciphertext =>
      E.decryptDist pp secretKey ciphertext) = PMF.pure message

end CryptoLib.Core.Primitive.Encryption.AsymmetricEncryption

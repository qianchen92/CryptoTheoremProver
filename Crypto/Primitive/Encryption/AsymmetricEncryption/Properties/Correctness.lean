import Crypto.Primitive.Encryption.AsymmetricEncryption.Syntax
import Mathlib.Probability.ProbabilityMassFunction.Monad

namespace Crypto.Primitive.Encryption.AsymmetricEncryption

universe uCost uSecPar uParam uPublicKey uSecretKey uMessage uCiphertext

/-- Perfect correctness for an asymmetric encryption scheme. -/
def Correct
    {M : Crypto.Infrastructure.Computation.Cost.CostModel.{uCost}}
    {SecPar : Type uSecPar}
    {Param : Type uParam}
    {PublicKey : Param → Type uPublicKey}
    {SecretKey : Param → Type uSecretKey}
    {Message : Param → Type uMessage}
    {Ciphertext : Param → Type uCiphertext}
    (E : Scheme M SecPar Param PublicKey SecretKey Message Ciphertext) : Prop :=
  ∀ (sec : SecPar)
    (pp : Param)
    (publicKey : PublicKey pp) (secretKey : SecretKey pp)
    (message : Message pp),
    pp ∈ (E.setupDist sec).support →
    (publicKey, secretKey) ∈ (E.keygenDist pp).support →
    (PMF.bind (E.encryptDist pp publicKey message) fun ciphertext =>
      E.decryptDist pp secretKey ciphertext) = PMF.pure message

end Crypto.Primitive.Encryption.AsymmetricEncryption

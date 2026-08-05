import Crypto.Primitive.Encryption.SymmetricEncryption.Syntax
import Mathlib.Probability.ProbabilityMassFunction.Monad

namespace Crypto.Primitive.Encryption.SymmetricEncryption

open Crypto.Infrastructure.Computation.Cost

universe uCost uSecPar uParam uMessage uCiphertext uKey

variable
    {M : CostModel.{uCost}}
    {SecPar : Type uSecPar}
    {Param : Type uParam}
    {Key : Param → Type uKey}
    {Message : Param → Type uMessage}
    {Ciphertext : Param → Type uCiphertext}

/-- Perfect correctness for a symmetric encryption scheme. -/
def Correct
    (E : Scheme M SecPar Param Key Message Ciphertext) : Prop :=
  ∀ (sec : SecPar)
    (pp : Param)
    (message : Message pp) (key : Key pp),
    pp ∈ (E.setupDist sec).support →
    key ∈ (E.keygenDist pp).support →
    (PMF.bind (E.encryptDist pp key message) fun ciphertext =>
      E.decryptDist pp key ciphertext) = PMF.pure message

end Crypto.Primitive.Encryption.SymmetricEncryption

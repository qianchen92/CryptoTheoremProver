import Crypto.Primitive.Encryption.SymmetricEncryption.Syntax

namespace Crypto.Primitive.Encryption.SymmetricEncryption

universe uParam uMessage uCiphertext uKey

/-- Perfect correctness for a symmetric encryption scheme. -/
def Correct
    {Param : Crypto.SecPar → Type uParam}
    {Key : {sec : Crypto.SecPar} → Param sec → Type uKey}
    {Message : {sec : Crypto.SecPar} → Param sec → Type uMessage}
    {Ciphertext : {sec : Crypto.SecPar} → Param sec → Type uCiphertext}
    (E : Scheme Param Key Message Ciphertext) : Prop :=
  ∀ (sec : Crypto.SecPar)
    (pp : Param sec)
    (message : Message pp) (key : Key pp) (ciphertext : Ciphertext pp),
    pp ∈ (E.setup sec).support →
    key ∈ (E.keygen pp).support →
    ciphertext ∈ (E.encrypt pp key message).support →
    E.decrypt pp key ciphertext = message

end Crypto.Primitive.Encryption.SymmetricEncryption

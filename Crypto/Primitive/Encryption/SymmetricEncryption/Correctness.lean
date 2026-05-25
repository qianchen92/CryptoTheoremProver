import Crypto.Primitive.Encryption.SymmetricEncryption.Syntax

namespace Crypto.Primitive.Encryption.SymmetricEncryption

universe uMessage uCiphertext uKey

/-- Perfect correctness for a symmetric encryption scheme. -/
def Correct {Key : Type uKey} {Message : Type uMessage} {Ciphertext : Type uCiphertext}
    (E : Scheme Key Message Ciphertext) : Prop :=
  ∀ sec message key ciphertext,
    key ∈ (E.keygen sec).support →
    ciphertext ∈ (E.encrypt sec key message).support →
    E.decrypt sec key ciphertext = message

end Crypto.Primitive.Encryption.SymmetricEncryption

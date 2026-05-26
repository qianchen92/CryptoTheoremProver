import Crypto.Primitive.Encryption.SymmetricEncryption.Instantiations.OneTimePad.Construction
import Crypto.Primitive.Encryption.SymmetricEncryption.Properties.Correctness

namespace Crypto.Primitive.Encryption.SymmetricEncryption.Instantiations.OneTimePad

universe uGroup

open Crypto.Primitive.Encryption.SymmetricEncryption

/-- Correctness of the group one-time pad. -/
theorem correct
    (GroupFamily : Crypto.SecPar → Type uGroup)
    [∀ sec, AddGroup (GroupFamily sec)] [∀ sec, Fintype (GroupFamily sec)]
    [∀ sec, Nonempty (GroupFamily sec)] :
    Correct (scheme GroupFamily) := by
  intro _sec _pp message key ciphertext _hpp _hkey hciphertext
  simp [scheme] at hciphertext ⊢
  subst ciphertext
  simp

end Crypto.Primitive.Encryption.SymmetricEncryption.Instantiations.OneTimePad

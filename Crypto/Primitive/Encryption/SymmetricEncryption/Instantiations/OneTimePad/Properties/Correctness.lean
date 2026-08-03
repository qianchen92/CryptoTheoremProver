import Crypto.Primitive.Encryption.SymmetricEncryption.Instantiations.OneTimePad.Scheme
import Crypto.Primitive.Encryption.SymmetricEncryption.Properties.Correctness

namespace Crypto.Primitive.Encryption.SymmetricEncryption.Instantiations.OneTimePad

universe uGroup

open Crypto.Primitive.Encryption.SymmetricEncryption
open scoped OneTimePadParameter

/-- Correctness of the group one-time pad. -/
theorem correct
    (F : Family.{uGroup}) :
    Correct (scheme F) := by
  intro _sec _pp message key _hpp _hkey
  simp

end Crypto.Primitive.Encryption.SymmetricEncryption.Instantiations.OneTimePad

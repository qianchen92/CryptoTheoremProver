import CryptoConstruction.Primitive.Encryption.SymmetricEncryption.OneTimePad.Properties.Semantics
import Crypto.Primitive.Encryption.SymmetricEncryption.Properties.Correctness

namespace CryptoConstruction.Primitive.Encryption.SymmetricEncryption.OneTimePad

universe uCost uGroup

open scoped OneTimePadParameter

variable
    {M : Crypto.Infrastructure.Computation.Cost.CostModel.{uCost}}
    (F : Family.{uCost, uGroup} M)

/-- Correctness of the group one-time pad. -/
theorem correct :
    Crypto.Primitive.Encryption.SymmetricEncryption.Correct (scheme F) := by
  intro _sec _pp message key _hpp _hkey
  simp

end CryptoConstruction.Primitive.Encryption.SymmetricEncryption.OneTimePad

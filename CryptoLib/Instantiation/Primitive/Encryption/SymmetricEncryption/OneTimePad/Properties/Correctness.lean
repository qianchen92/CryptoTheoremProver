import CryptoLib.Instantiation.Primitive.Encryption.SymmetricEncryption.OneTimePad.Properties.Semantics
import CryptoLib.Core.Primitive.Encryption.SymmetricEncryption.Properties.Correctness

namespace CryptoLib.Instantiation.Primitive.Encryption.SymmetricEncryption.OneTimePad

universe uCost uGroup

open scoped OneTimePadParameter

variable
    {M : CryptoLib.Core.Infrastructure.Computation.Cost.CostModel.{uCost}}
    (F : Family.{uCost, uGroup} M)

/-- Correctness of the group one-time pad. -/
theorem correct :
    CryptoLib.Core.Primitive.Encryption.SymmetricEncryption.Correct (scheme F) := by
  intro _sec _pp message key _hpp _hkey
  simp

end CryptoLib.Instantiation.Primitive.Encryption.SymmetricEncryption.OneTimePad

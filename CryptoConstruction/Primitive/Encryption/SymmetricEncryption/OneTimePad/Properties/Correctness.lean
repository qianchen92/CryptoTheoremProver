import CryptoConstruction.Primitive.Encryption.SymmetricEncryption.OneTimePad.Properties.Semantics
import Crypto.Primitive.Encryption.SymmetricEncryption.Properties.Correctness

namespace CryptoConstruction.Primitive.Encryption.SymmetricEncryption.OneTimePad

universe uCost uGroup

open Crypto.Infrastructure.Computation.Cost
open Crypto.Primitive.Encryption.SymmetricEncryption
open scoped OneTimePadParameter

/-- Correctness of the group one-time pad. -/
theorem correct
    {M : CostModel.{uCost}} (F : Family M) :
    Correct (scheme F) := by
  intro _sec _pp message key _hpp _hkey
  simp

end CryptoConstruction.Primitive.Encryption.SymmetricEncryption.OneTimePad

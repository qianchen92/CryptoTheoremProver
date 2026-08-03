import Crypto.Primitive.Encryption.SymmetricEncryption.Instantiations.OneTimePad.Scheme
import Crypto.Primitive.Encryption.SymmetricEncryption.Properties.Correctness

namespace Crypto.Primitive.Encryption.SymmetricEncryption.Instantiations.OneTimePad

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

end Crypto.Primitive.Encryption.SymmetricEncryption.Instantiations.OneTimePad

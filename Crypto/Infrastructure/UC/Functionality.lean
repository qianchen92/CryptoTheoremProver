import Crypto.Infrastructure.UC.Protocol

namespace Crypto.Infrastructure.UC

open Crypto.Infrastructure.Computation.Cost

universe uCost uAddress uPayload uPort uCapability
universe uState uLeakage uErasure uOutput

/--
An ideal functionality is intentionally not an alias for `Protocol`.

The two wrappers may use the same exact ITM kernel interface, but their roles
in the real and ideal worlds are distinct in types and cannot be interchanged
without an explicit construction.
-/
structure IdealFunctionality
    (M : CostModel.{uCost})
    {Address : Type uAddress}
    (schema : PortSchema.{uAddress, uPayload, uPort, uCapability} Address)
    (LocalAddress : Type uAddress)
    (embed : LocalAddress → Address) where
  machine : AddressedITM.{uCost, uAddress, uPayload, uPort, uCapability,
    uState, uLeakage, uErasure, uOutput} M schema LocalAddress embed

end Crypto.Infrastructure.UC

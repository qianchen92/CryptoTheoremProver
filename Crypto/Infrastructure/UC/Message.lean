import Crypto.Infrastructure.UC.Port

namespace Crypto.Infrastructure.UC

universe uAddress uPayload uPort uCapability

variable {Address : Type uAddress}
variable (schema : PortSchema.{uAddress, uPayload, uPort, uCapability} Address)

/-- A fully typed message with a proof-carrying connection capability. -/
structure Message where
  Payload : Type uPayload
  source : Endpoint schema .output Payload
  target : Endpoint schema .input Payload
  capability : schema.CanConnect source.port target.port
  payload : Payload

/-- A message viewed from its statically known target address. -/
structure Incoming (target : Address) where
  Payload : Type uPayload
  source : Endpoint schema .output Payload
  targetPort : schema.Port target .input Payload
  capability : schema.CanConnect source.port targetPort
  payload : Payload

/-- A message viewed from its statically known source address. -/
structure Emission (source : Address) where
  Payload : Type uPayload
  sourcePort : schema.Port source .output Payload
  target : Endpoint schema .input Payload
  capability : schema.CanConnect sourcePort target.port
  payload : Payload

namespace Incoming

/-- Forget the target index while retaining the typed capability. -/
def toMessage {target : Address} (incoming : Incoming schema target) : Message schema where
  Payload := incoming.Payload
  source := incoming.source
  target := ⟨target, incoming.targetPort⟩
  capability := incoming.capability
  payload := incoming.payload

end Incoming

namespace Emission

variable {source : Address}

/-- Forget the source index while retaining the typed capability. -/
def toMessage (emission : Emission schema source) : Message schema where
  Payload := emission.Payload
  source := ⟨source, emission.sourcePort⟩
  target := emission.target
  capability := emission.capability
  payload := emission.payload

/-- Routing policy is determined by the capability carried by an emission. -/
def routingPolicy (emission : Emission schema source) : RoutingPolicy :=
  schema.route emission.sourcePort emission.target.port emission.capability

end Emission

end Crypto.Infrastructure.UC

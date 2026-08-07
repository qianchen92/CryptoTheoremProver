import CryptoLib.Core.Infrastructure.UC.Session

namespace CryptoLib.Core.Infrastructure.UC

universe uAddress uPayload uPort uCapability

/-- Whether an endpoint receives or emits a payload. -/
inductive Direction where
  | input
  | output
  deriving DecidableEq, Repr

/-- Which component controls delivery of a routed message. -/
inductive DeliveryAuthority where
  | kernel
  | adversary
  deriving DecidableEq, Repr

/--
The complete routing policy attached to one typed connection capability.

The constructors expose observation, delay/delivery, forgery, and broadcast
authority as separate projections below.  Broadcast permission does not cause
kernel fanout: an explicit broadcast component must serialize deliveries.
-/
inductive RoutingPolicy where
  | direct
  | adversarialAuthenticated
  | adversarialForgeable
  | adversarialBroadcast
  deriving DecidableEq, Repr

namespace RoutingPolicy

/-- Whether the adversarial network observes the message. -/
def observable : RoutingPolicy → Bool
  | .direct => false
  | .adversarialAuthenticated | .adversarialForgeable
  | .adversarialBroadcast => true

/-- Which component has authority to schedule the next delivery. -/
def deliveryAuthority : RoutingPolicy → DeliveryAuthority
  | .direct => .kernel
  | .adversarialAuthenticated | .adversarialForgeable
  | .adversarialBroadcast => .adversary

/-- Whether the adversarial network may delay delivery. -/
def delayable : RoutingPolicy → Bool
  | .direct => false
  | .adversarialAuthenticated | .adversarialForgeable
  | .adversarialBroadcast => true

/-- Whether the adversarial network may forge a sender. -/
def forgeable : RoutingPolicy → Bool
  | .adversarialForgeable => true
  | .direct | .adversarialAuthenticated | .adversarialBroadcast => false

/-- Whether the connection may enter an explicit broadcast component. -/
def broadcastable : RoutingPolicy → Bool
  | .adversarialBroadcast => true
  | .direct | .adversarialAuthenticated | .adversarialForgeable => false

end RoutingPolicy

/--
A result-indexed collection of typed ports and connection capabilities.

`CanConnect` is data, rather than a Boolean side condition.  Consequently an
ill-typed or unauthorized message cannot be constructed and later rejected by
the interpreter.
-/
structure PortSchema (Address : Type uAddress) where
  Port : Address → Direction → (Payload : Type uPayload) → Type uPort
  CanConnect : {Payload : Type uPayload} → {source target : Address} →
    Port source .output Payload → Port target .input Payload → Type uCapability
  CanSendAs : (controller claimedSource : Address) → Type uCapability
  route : {Payload : Type uPayload} → {source target : Address} →
    (sourcePort : Port source .output Payload) →
    (targetPort : Port target .input Payload) →
    CanConnect sourcePort targetPort → RoutingPolicy

/-- One typed input or output endpoint. -/
structure Endpoint
    {Address : Type uAddress} (schema : PortSchema.{uAddress, uPayload, uPort, uCapability} Address)
    (direction : Direction) (Payload : Type uPayload) where
  address : Address
  port : schema.Port address direction Payload

end CryptoLib.Core.Infrastructure.UC

import CryptoLib.UC.Configuration
import CryptoLib.UC.Port
import CryptoLib.UC.ITM

namespace CryptoLib.Protocol

open CryptoLib.UC
open CryptoLib.Core.Infrastructure.Computation.Cost

universe uCost uAddress uPayload uPort uCapability
universe uState uLeakage uErasure uOutput

/--
The four disjoint address spaces of a closed UC execution.

The `system` summand is occupied by a protocol in a real execution and by an
ideal functionality in an ideal execution.  Tagging addresses here makes
ownership decidable from the address itself and prevents one component from
silently sharing another component's local-state cell.
-/
inductive ClosedWorldAddress
    (EnvironmentAddress ProtocolAddress AdversaryAddress NetworkAddress :
      Type uAddress) where
  | environment (address : EnvironmentAddress)
  | system (address : ProtocolAddress)
  | adversary (address : AdversaryAddress)
  | network (address : NetworkAddress)
  deriving DecidableEq, Repr

section AddressedComponents

variable
  (M : CostModel.{uCost})
  {Address : Type uAddress}
  (schema : PortSchema.{uAddress, uPayload, uPort, uCapability} Address)
  (LocalAddress : Type uAddress)
  (embed : LocalAddress → Address)

/--
An exactly interpreted ITM family over one owned portion of a global address
space.

The embedding is part of the type.  Hence activations and emitted actions use
the global port schema while state, leakage, erasure, and output remain indexed
by the component's local address.
-/
structure AddressedITM where
  State : CryptoLib.Core.SecPar → LocalAddress → Type uState
  Leakage : CryptoLib.Core.SecPar → LocalAddress → Type uLeakage
  Erasure : CryptoLib.Core.SecPar → LocalAddress → Type uErasure
  Output : CryptoLib.Core.SecPar → LocalAddress → Type uOutput
  init : ∀ sec address, RandCosted M (State sec address)
  activate : ∀ sec address,
    State sec address → ActivationInput schema (embed address) →
      RandCosted M
        (ActivationResult (State sec address)
          (LocalAction schema (embed address)
            (Erasure sec address) (Output sec address)))
  applyErasure : ∀ sec address,
    Erasure sec address → State sec address → Costed M (State sec address)
  leak : ∀ sec address,
    State sec address → Costed M (Leakage sec address)

/--
The environment component of a closed execution.

An environment-owned terminal output is intrinsically Boolean.  The equality
is indexed by the security parameter and local address because `AddressedITM`
allows dependent output families.  The closed-world projection defined in
`Composition` transports only environment-owned outputs along this equality;
outputs from every other role map to `false`.

Consequently there is no unmeasured postprocessing function outside the ITM:
computing the distinguishing bit is part of the environment's certified
activation handler.
-/
structure Environment where
  machine : AddressedITM.{uCost, uAddress, uPayload, uPort, uCapability,
    uState, uLeakage, uErasure, uOutput} M schema LocalAddress embed
  output_isBool : ∀ sec address,
    machine.Output sec address = ULift.{uOutput} Bool

/-- The real protocol component of a closed execution. -/
structure Protocol where
  machine : AddressedITM.{uCost, uAddress, uPayload, uPort, uCapability,
    uState, uLeakage, uErasure, uOutput} M schema LocalAddress embed

/-- The real-world network adversary component. -/
structure Adversary where
  machine : AddressedITM.{uCost, uAddress, uPayload, uPort, uCapability,
    uState, uLeakage, uErasure, uOutput} M schema LocalAddress embed

/-- The ideal-world simulator component. -/
structure Simulator where
  machine : AddressedITM.{uCost, uAddress, uPayload, uPort, uCapability,
    uState, uLeakage, uErasure, uOutput} M schema LocalAddress embed

/--
The explicit network component and the routing actions it gives to the kernel.

`observe`, `control`, and `leakage` all return ordinary typed activations.  The
network therefore cannot inject an untyped payload into the FIFO.  Broadcast
is implemented by this component's ordinary continuation/resume states, not by
a hidden kernel fanout.
-/
structure Network where
  machine : AddressedITM.{uCost, uAddress, uPayload, uPort, uCapability,
    uState, uLeakage, uErasure, uOutput} M schema LocalAddress embed
  observe : ∀ {source : Address},
    Emission schema source → QueuedActivation schema
  control : QueuedActivation schema → QueuedActivation schema
  leakage : ∀ {Leakage : Address → Type uLeakage},
    (target : Address) → Leakage target → QueuedActivation schema

end AddressedComponents

end CryptoLib.Protocol

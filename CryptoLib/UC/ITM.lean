import CryptoLib.Core.Infrastructure.Computation.Cost.Randomized
import CryptoLib.UC.Message

namespace CryptoLib.UC

open CryptoLib.Core.Infrastructure.Computation.Cost

universe uCost uAddress uPayload uPort uCapability
universe uState uLeakage uErasure uOutput

variable {Address : Type uAddress}
variable (schema : PortSchema.{uAddress, uPayload, uPort, uCapability} Address)

/-- The payload consumed by one activation of a target ITM. -/
inductive ActivationInput (target : Address) where
  | message (incoming : Incoming schema target)
  | resume

/--
Exactly one externally visible action produced by an activation.

Multiple sends, erasures, or subroutine starts are serialized by storing a
continuation in local state and requesting a later `resume` activation.
-/
inductive LocalAction (source : Address) (Erasure : Type uErasure)
    (Output : Type uOutput) where
  | yield
  | emit (emission : Emission schema source)
  | emitAs (claimedSource : Address)
      (authorization : schema.CanSendAs source claimedSource)
      (emission : Emission schema claimedSource)
  | erase (request : Erasure)
  | spawn (target : Address) (initial : ActivationInput schema target)
  | requestCorruption (target : Address)
  | output (value : Output)

/-- The next local state and the single action produced by one activation. -/
structure ActivationResult (State : Type uState) (Action : Type uOutput) where
  state : State
  action : Action

/--
A family of exactly costed interactive machines indexed by their addresses.

The family owns local state, erasure, and corruption-leakage semantics.  It
does not own scheduling, routing, or the global corruption policy.
-/
structure ITMFamily
    (M : CostModel.{uCost})
    (Address : Type uAddress)
    (schema : PortSchema.{uAddress, uPayload, uPort, uCapability} Address) where
  State : CryptoLib.Core.SecPar → Address → Type uState
  Leakage : CryptoLib.Core.SecPar → Address → Type uLeakage
  Erasure : CryptoLib.Core.SecPar → Address → Type uErasure
  Output : CryptoLib.Core.SecPar → Address → Type uOutput
  init : ∀ sec address, RandCosted M (State sec address)
  activate : ∀ sec address,
    State sec address → ActivationInput schema address →
      RandCosted M
        (ActivationResult (State sec address)
          (LocalAction schema address (Erasure sec address) (Output sec address)))
  applyErasure : ∀ sec address,
    Erasure sec address → State sec address → Costed M (State sec address)
  leak : ∀ sec address,
    State sec address → Costed M (Leakage sec address)

end CryptoLib.UC

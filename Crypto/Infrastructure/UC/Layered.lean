import Crypto.Infrastructure.UC.Context

namespace Crypto.Infrastructure.UC.Layered

open Crypto.Infrastructure.Computation.Cost

universe uCost uAddress uPayload uPort uCapability
universe uState uLeakage uErasure uOutput

/-- Public shape and corruption threshold of a layered execution. -/
structure Parameters where
  partiesPerLayer : Nat
  maxCorrupt : Nat
  layers : Nat

namespace Parameters

/-- The honest-majority threshold used by Shamir-style layered MPC. -/
def HonestMajority (params : Parameters) : Prop :=
  3 * params.maxCorrupt < params.partiesPerLayer

/-- The exact threshold form frequently used by layered MPC constructions. -/
def ExactShamirThreshold (params : Parameters) : Prop :=
  params.partiesPerLayer = 3 * params.maxCorrupt + 1

theorem exactShamirThreshold_honestMajority
    {params : Parameters} (threshold : params.ExactShamirThreshold) :
    params.HonestMajority := by
  unfold ExactShamirThreshold at threshold
  unfold HonestMajority
  rw [threshold]
  exact Nat.lt_succ_self (3 * params.maxCorrupt)

end Parameters

/-- Parties are indexed by a layer and a position in that layer. -/
abbrev PartyId (params : Parameters) :=
  Fin params.layers × Fin params.partiesPerLayer

namespace PartyId

variable {params : Parameters}

def layer (party : PartyId params) : Fin params.layers :=
  party.1

def index (party : PartyId params) : Fin params.partiesPerLayer :=
  party.2

end PartyId

/-- Explicit trusted managers used by layered executions. -/
inductive TrustedRole where
  | corruptionManager
  | broadcastManager
  deriving DecidableEq, Repr

/-- Typed external boundary roles of a layered ideal functionality. -/
inductive BoundaryRole where
  | input (index : Nat)
  | output (index : Nat)
  deriving DecidableEq, Repr

/-- Every machine name installed in the layered system component. -/
inductive Role (params : Parameters) where
  | party (id : PartyId params)
  | trusted (role : TrustedRole)
  | boundary (role : BoundaryRole)
  deriving DecidableEq, Repr

/-- A session-indexed address in the system portion of a layered world. -/
abbrev SystemAddress (Tag : Type uAddress) (params : Parameters) :=
  Crypto.Infrastructure.UC.Address Tag (Role params)

namespace Corruption

variable {Tag EnvironmentAddress AdversarialAddress NetworkAddress : Type uAddress}
variable [DecidableEq Tag] [DecidableEq EnvironmentAddress]
variable [DecidableEq AdversarialAddress] [DecidableEq NetworkAddress]
variable {params : Parameters}

abbrev GlobalAddress
    (Tag EnvironmentAddress AdversarialAddress NetworkAddress : Type uAddress)
    (params : Parameters) :=
  WorldAddress EnvironmentAddress (SystemAddress Tag params)
    AdversarialAddress NetworkAddress

/-- Decide whether a global address is a party in one exact session and layer. -/
def isPartyAt
    (sid : SID Tag) (layer : Fin params.layers)
    (address : GlobalAddress Tag EnvironmentAddress
      AdversarialAddress NetworkAddress params) : Bool :=
  match address with
  | .system systemAddress =>
      match systemAddress.name with
      | .party party =>
          decide (systemAddress.sid = sid ∧ party.layer = layer)
      | .trusted _ | .boundary _ => false
  | .environment _ | .adversary _ | .network _ => false

/-- Corrupted parties in one exact session/layer cell. -/
def partiesAt
    (corrupted : Finset (GlobalAddress Tag EnvironmentAddress
      AdversarialAddress NetworkAddress params))
    (sid : SID Tag) (layer : Fin params.layers) :
    Finset (GlobalAddress Tag EnvironmentAddress
      AdversarialAddress NetworkAddress params) :=
  corrupted.filter fun address =>
    isPartyAt (EnvironmentAddress := EnvironmentAddress)
      (AdversarialAddress := AdversarialAddress)
      (NetworkAddress := NetworkAddress) sid layer address

/-- Number of corruptions in one exact session/layer cell. -/
def countAt
    (corrupted : Finset (GlobalAddress Tag EnvironmentAddress
      AdversarialAddress NetworkAddress params))
    (sid : SID Tag) (layer : Fin params.layers) : Nat :=
  (partiesAt (Tag := Tag) (EnvironmentAddress := EnvironmentAddress)
    (AdversarialAddress := AdversarialAddress)
    (NetworkAddress := NetworkAddress) corrupted sid layer).card

/-- Trusted, boundary, environment, adversarial, and network addresses are incorruptible. -/
def OnlyParties
    (corrupted : Finset (GlobalAddress Tag EnvironmentAddress
      AdversarialAddress NetworkAddress params)) : Prop :=
  ∀ address ∈ corrupted,
    ∃ sid party,
      address = ClosedWorldAddress.system
        ({ sid := sid, name := Role.party party } : SystemAddress Tag params)

/-- The threshold is enforced independently in every session and layer. -/
def Eligible
    (params : Parameters)
    (corrupted : Finset (GlobalAddress Tag EnvironmentAddress
      AdversarialAddress NetworkAddress params)) : Prop :=
  OnlyParties (Tag := Tag) (EnvironmentAddress := EnvironmentAddress)
      (AdversarialAddress := AdversarialAddress)
      (NetworkAddress := NetworkAddress) corrupted ∧
    ∀ sid (layer : Fin params.layers),
      countAt (Tag := Tag) (EnvironmentAddress := EnvironmentAddress)
        (AdversarialAddress := AdversarialAddress)
        (NetworkAddress := NetworkAddress) corrupted sid layer ≤ params.maxCorrupt

/--
Dynamic layered corruption as the actual policy consumed by the global kernel.

The session identifier is part of the count key, so corruptions in a child or
independent root session cannot spend another session's threshold.
-/
noncomputable def layeredPolicy
    (params : Parameters) :
    CorruptionPolicy (GlobalAddress Tag EnvironmentAddress
      AdversarialAddress NetworkAddress params) := by
  classical
  exact CorruptionPolicy.dynamic
    (Eligible (Tag := Tag) (EnvironmentAddress := EnvironmentAddress)
      (AdversarialAddress := AdversarialAddress)
      (NetworkAddress := NetworkAddress) params)
    (fun _corrupted => inferInstance)

end Corruption

/-- A party address retains both its UC session and its layer-local identity. -/
abbrev PartyAddress (Tag : Type uAddress) (params : Parameters) : Type uAddress :=
  Crypto.Infrastructure.UC.Address Tag (PartyId params)

/-- A boundary address retains the session in which the boundary is active. -/
abbrev BoundaryAddress (Tag : Type uAddress) : Type uAddress :=
  Crypto.Infrastructure.UC.Address Tag BoundaryRole

section CanonicalEmbeddings

variable {Tag EnvironmentAddress AdversarialAddress NetworkAddress : Type uAddress}
variable {params : Parameters}

/-- Canonical embedding of a session-indexed party into the system summand. -/
def partyEmbed :
    PartyAddress Tag params →
      Corruption.GlobalAddress Tag EnvironmentAddress
        AdversarialAddress NetworkAddress params :=
  fun address => .system ⟨address.sid, .party address.name⟩

/-- Canonical address of the broadcast manager in one session. -/
def broadcastManagerEmbed :
    SID Tag → Corruption.GlobalAddress Tag EnvironmentAddress
      AdversarialAddress NetworkAddress params :=
  fun sid => .system ⟨sid, .trusted .broadcastManager⟩

/-- Canonical address of the corruption manager in one session. -/
def corruptionManagerEmbed :
    SID Tag → Corruption.GlobalAddress Tag EnvironmentAddress
      AdversarialAddress NetworkAddress params :=
  fun sid => .system ⟨sid, .trusted .corruptionManager⟩

/-- Canonical embedding of a typed boundary endpoint into the system summand. -/
def boundaryEmbed :
    BoundaryAddress Tag → Corruption.GlobalAddress Tag EnvironmentAddress
      AdversarialAddress NetworkAddress params :=
  fun address => .system ⟨address.sid, .boundary address.name⟩

end CanonicalEmbeddings

/--
One exact layered party ITM.

Its activation handler returns exactly one `LocalAction`; a protocol that wants
to send several private messages or broadcast to several recipients stores a
continuation in `State` and emits subsequent actions after queued `resume`
activations.
-/
structure PartyStep
    (M : CostModel.{uCost}) (params : Parameters) (Tag : Type uAddress)
    {Address : Type uAddress}
    (schema : PortSchema.{uAddress, uPayload, uPort, uCapability} Address)
    (embed : PartyAddress Tag params → Address) where
  State : Crypto.SecPar → PartyAddress Tag params → Type uState
  Leakage : Crypto.SecPar → PartyAddress Tag params → Type uLeakage
  Erasure : Crypto.SecPar → PartyAddress Tag params → Type uErasure
  Output : Crypto.SecPar → PartyAddress Tag params → Type uOutput
  init : ∀ sec party, RandCosted M (State sec party)
  activate : ∀ sec party,
    State sec party → ActivationInput schema (embed party) →
      RandCosted M
        (ActivationResult (State sec party)
          (LocalAction schema (embed party)
            (Erasure sec party) (Output sec party)))
  applyErasure : ∀ sec party,
    Erasure sec party → State sec party → Costed M (State sec party)
  leak : ∀ sec party,
    State sec party → Costed M (Leakage sec party)

namespace PartyStep

/-- Install a party step as an address-owned exact ITM family. -/
def toAddressedITM
    {M : CostModel.{uCost}} {params : Parameters} {Tag : Type uAddress}
    {Address : Type uAddress}
    {schema : PortSchema.{uAddress, uPayload, uPort, uCapability} Address}
    {embed : PartyAddress Tag params → Address}
    (step : PartyStep.{uCost, uAddress, uPayload, uPort, uCapability,
      uState, uLeakage, uErasure, uOutput} M params Tag schema embed) :
    AddressedITM.{uCost, uAddress, uPayload, uPort, uCapability,
      uState, uLeakage, uErasure, uOutput}
      M schema (PartyAddress Tag params) embed where
  State := step.State
  Leakage := step.Leakage
  Erasure := step.Erasure
  Output := step.Output
  init := step.init
  activate := step.activate
  applyErasure := step.applyErasure
  leak := step.leak

end PartyStep

/-- An explicit broadcast manager; fanout is serialized by its ITM state. -/
structure BroadcastManager
    (M : CostModel.{uCost})
    {Address : Type uAddress}
    (schema : PortSchema.{uAddress, uPayload, uPort, uCapability} Address)
    (LocalAddress : Type uAddress) (embed : LocalAddress → Address) where
  machine : AddressedITM.{uCost, uAddress, uPayload, uPort, uCapability,
    uState, uLeakage, uErasure, uOutput} M schema LocalAddress embed

/-- An explicit corruption manager installed as an ordinary exact component. -/
structure CorruptionManager
    (M : CostModel.{uCost})
    {Address : Type uAddress}
    (schema : PortSchema.{uAddress, uPayload, uPort, uCapability} Address)
    (LocalAddress : Type uAddress) (embed : LocalAddress → Address) where
  machine : AddressedITM.{uCost, uAddress, uPayload, uPort, uCapability,
    uState, uLeakage, uErasure, uOutput} M schema LocalAddress embed

/-- Session-indexed input/output boundary machines of the real protocol. -/
structure BoundaryComponent
    (M : CostModel.{uCost})
    {Address : Type uAddress}
    (schema : PortSchema.{uAddress, uPayload, uPort, uCapability} Address)
    (LocalAddress : Type uAddress) (embed : LocalAddress → Address) where
  machine : AddressedITM.{uCost, uAddress, uPayload, uPort, uCapability,
    uState, uLeakage, uErasure, uOutput} M schema LocalAddress embed

/--
All exact machines installed in the real system summand of a layered world.

Every constructor of `Role` has exactly one owner.  The dispatcher below is
therefore total without a dummy state, a blanket instance, or an ignored
manager field.
-/
structure SystemComponents
    (M : CostModel.{uCost}) (params : Parameters)
    (Tag EnvironmentAddress AdversarialAddress NetworkAddress : Type uAddress)
    (schema : PortSchema.{uAddress, uPayload, uPort, uCapability}
      (Corruption.GlobalAddress Tag EnvironmentAddress
        AdversarialAddress NetworkAddress params)) where
  parties : PartyStep.{uCost, uAddress, uPayload, uPort, uCapability,
    uState, uLeakage, uErasure, uOutput}
    M params Tag schema partyEmbed
  broadcast : BroadcastManager.{uCost, uAddress, uPayload, uPort, uCapability,
    uState, uLeakage, uErasure, uOutput}
    M schema (SID Tag) broadcastManagerEmbed
  corruption : CorruptionManager.{uCost, uAddress, uPayload, uPort, uCapability,
    uState, uLeakage, uErasure, uOutput}
    M schema (SID Tag) corruptionManagerEmbed
  boundary : BoundaryComponent.{uCost, uAddress, uPayload, uPort, uCapability,
    uState, uLeakage, uErasure, uOutput}
    M schema (BoundaryAddress Tag) boundaryEmbed

namespace SystemComponents

variable {M : CostModel.{uCost}} {params : Parameters}
variable {Tag EnvironmentAddress AdversarialAddress NetworkAddress : Type uAddress}
variable {schema : PortSchema.{uAddress, uPayload, uPort, uCapability}
  (Corruption.GlobalAddress Tag EnvironmentAddress
    AdversarialAddress NetworkAddress params)}

/--
Dispatch the four layered component classes as the one system-owned ITM used
by `composeReal`.

The address role selects the handler definitionally.  In particular,
broadcast and corruption managers and boundary machines are not metadata:
their exact handlers are reachable through the global kernel family.
-/
def toAddressedITM
    (components : SystemComponents.{uCost, uAddress, uPayload, uPort,
      uCapability, uState, uLeakage, uErasure, uOutput}
      M params Tag EnvironmentAddress AdversarialAddress NetworkAddress schema) :
    AddressedITM.{uCost, uAddress, uPayload, uPort, uCapability,
      uState, uLeakage, uErasure, uOutput}
      M schema (SystemAddress Tag params) ClosedWorldAddress.system where
  State sec address :=
    match address with
    | ⟨sid, .party party⟩ => components.parties.State sec ⟨sid, party⟩
    | ⟨sid, .trusted .broadcastManager⟩ =>
        components.broadcast.machine.State sec sid
    | ⟨sid, .trusted .corruptionManager⟩ =>
        components.corruption.machine.State sec sid
    | ⟨sid, .boundary boundary⟩ =>
        components.boundary.machine.State sec ⟨sid, boundary⟩
  Leakage sec address :=
    match address with
    | ⟨sid, .party party⟩ => components.parties.Leakage sec ⟨sid, party⟩
    | ⟨sid, .trusted .broadcastManager⟩ =>
        components.broadcast.machine.Leakage sec sid
    | ⟨sid, .trusted .corruptionManager⟩ =>
        components.corruption.machine.Leakage sec sid
    | ⟨sid, .boundary boundary⟩ =>
        components.boundary.machine.Leakage sec ⟨sid, boundary⟩
  Erasure sec address :=
    match address with
    | ⟨sid, .party party⟩ => components.parties.Erasure sec ⟨sid, party⟩
    | ⟨sid, .trusted .broadcastManager⟩ =>
        components.broadcast.machine.Erasure sec sid
    | ⟨sid, .trusted .corruptionManager⟩ =>
        components.corruption.machine.Erasure sec sid
    | ⟨sid, .boundary boundary⟩ =>
        components.boundary.machine.Erasure sec ⟨sid, boundary⟩
  Output sec address :=
    match address with
    | ⟨sid, .party party⟩ => components.parties.Output sec ⟨sid, party⟩
    | ⟨sid, .trusted .broadcastManager⟩ =>
        components.broadcast.machine.Output sec sid
    | ⟨sid, .trusted .corruptionManager⟩ =>
        components.corruption.machine.Output sec sid
    | ⟨sid, .boundary boundary⟩ =>
        components.boundary.machine.Output sec ⟨sid, boundary⟩
  init sec address :=
    match address with
    | ⟨sid, .party party⟩ => components.parties.init sec ⟨sid, party⟩
    | ⟨sid, .trusted .broadcastManager⟩ => components.broadcast.machine.init sec sid
    | ⟨sid, .trusted .corruptionManager⟩ =>
        components.corruption.machine.init sec sid
    | ⟨sid, .boundary boundary⟩ =>
        components.boundary.machine.init sec ⟨sid, boundary⟩
  activate sec address state input :=
    match address with
    | ⟨sid, .party party⟩ => components.parties.activate sec ⟨sid, party⟩ state input
    | ⟨sid, .trusted .broadcastManager⟩ =>
        components.broadcast.machine.activate sec sid state input
    | ⟨sid, .trusted .corruptionManager⟩ =>
        components.corruption.machine.activate sec sid state input
    | ⟨sid, .boundary boundary⟩ =>
        components.boundary.machine.activate sec ⟨sid, boundary⟩ state input
  applyErasure sec address request state :=
    match address with
    | ⟨sid, .party party⟩ =>
        components.parties.applyErasure sec ⟨sid, party⟩ request state
    | ⟨sid, .trusted .broadcastManager⟩ =>
        components.broadcast.machine.applyErasure sec sid request state
    | ⟨sid, .trusted .corruptionManager⟩ =>
        components.corruption.machine.applyErasure sec sid request state
    | ⟨sid, .boundary boundary⟩ =>
        components.boundary.machine.applyErasure sec ⟨sid, boundary⟩ request state
  leak sec address state :=
    match address with
    | ⟨sid, .party party⟩ => components.parties.leak sec ⟨sid, party⟩ state
    | ⟨sid, .trusted .broadcastManager⟩ =>
        components.broadcast.machine.leak sec sid state
    | ⟨sid, .trusted .corruptionManager⟩ =>
        components.corruption.machine.leak sec sid state
    | ⟨sid, .boundary boundary⟩ =>
        components.boundary.machine.leak sec ⟨sid, boundary⟩ state

/-- The complete layered system dispatcher is the actual real protocol. -/
def toProtocol
    (components : SystemComponents.{uCost, uAddress, uPayload, uPort,
      uCapability, uState, uLeakage, uErasure, uOutput}
      M params Tag EnvironmentAddress AdversarialAddress NetworkAddress schema) :
    Protocol.{uCost, uAddress, uPayload, uPort, uCapability,
      uState, uLeakage, uErasure, uOutput}
      M schema (SystemAddress Tag params) ClosedWorldAddress.system where
  machine := components.toAddressedITM

end SystemComponents

/--
A layered MPC ideal functionality backed by an actual exact ITM.

Input collection, evaluation, output release, leakage, and erasure are all
implemented by `machine.activate` and its state.  There is no disconnected
`eval : ... → PMF ...` field whose semantics could diverge from the UC world.
-/
structure MPCFunctionality
    (M : CostModel.{uCost})
    {Address : Type uAddress}
    (schema : PortSchema.{uAddress, uPayload, uPort, uCapability} Address)
    (LocalAddress : Type uAddress) (embed : LocalAddress → Address) where
  inputCount : Nat
  outputCount : Nat
  machine : AddressedITM.{uCost, uAddress, uPayload, uPort, uCapability,
    uState, uLeakage, uErasure, uOutput} M schema LocalAddress embed

namespace MPCFunctionality

/-- Install the exact MPC machine as a genuine ideal functionality. -/
def toIdealFunctionality
    {M : CostModel.{uCost}}
    {Address LocalAddress : Type uAddress}
    {schema : PortSchema.{uAddress, uPayload, uPort, uCapability} Address}
    {embed : LocalAddress → Address}
    (functionality : MPCFunctionality.{uCost, uAddress, uPayload, uPort,
      uCapability, uState, uLeakage, uErasure, uOutput}
      M schema LocalAddress embed) :
    IdealFunctionality.{uCost, uAddress, uPayload, uPort, uCapability,
      uState, uLeakage, uErasure, uOutput}
      M schema LocalAddress embed where
  machine := functionality.machine

end MPCFunctionality

section ExecutableBridge

variable {M : CostModel.{uCost}} {measure : NatMeasure M}
variable {params : Parameters}
variable {Tag EnvironmentAddress AdversarialAddress NetworkAddress : Type uAddress}
variable [DecidableEq Tag] [DecidableEq EnvironmentAddress]
variable [DecidableEq AdversarialAddress] [DecidableEq NetworkAddress]
variable {schema : PortSchema.{uAddress, uPayload, uPort, uCapability}
  (Corruption.GlobalAddress Tag EnvironmentAddress
    AdversarialAddress NetworkAddress params)}

/--
An executable layered UC experiment before packaging into generic Context
infrastructure.

The real system is definitionally the total dispatcher of `components`; the
ideal system is one `MPCFunctionality` over the same full system address type.
Both configurations and both PPT execution certificates are indexed by the
same `Corruption.layeredPolicy params`, so the threshold restriction is part of
the runner's type rather than an unused side condition.
-/
structure ExecutableLayered where
  components : SystemComponents.{uCost, uAddress, uPayload, uPort,
    uCapability, uState, uLeakage, uErasure, uOutput}
    M params Tag EnvironmentAddress AdversarialAddress NetworkAddress schema
  functionality : MPCFunctionality.{uCost, uAddress, uPayload, uPort,
    uCapability, uState, uLeakage, uErasure, uOutput}
    M schema (SystemAddress Tag params) ClosedWorldAddress.system
  network : Network.{uCost, uAddress, uPayload, uPort, uCapability,
    uState, uLeakage, uErasure, uOutput}
    M schema NetworkAddress ClosedWorldAddress.network
  kernelAlgebra : KernelAlgebra M
    (Corruption.GlobalAddress Tag EnvironmentAddress
      AdversarialAddress NetworkAddress params)
  realInitial : ∀
    (adversary : PPTAdversary.{uCost, uAddress, uPayload, uPort,
      uCapability, uState, uLeakage, uErasure, uOutput}
      M measure schema AdversarialAddress ClosedWorldAddress.adversary)
    (environment : PPTEnvironment.{uCost, uAddress, uPayload, uPort,
      uCapability, uState, uLeakage, uErasure, uOutput}
      M measure schema EnvironmentAddress ClosedWorldAddress.environment)
    (sec : Crypto.SecPar),
      Configuration
        (dispatchFamily environment.toEnvironment.machine
          components.toAddressedITM adversary.toAdversary.machine network.machine)
        (Corruption.layeredPolicy params) sec
  idealInitial : ∀
    (simulator : PPTSimulator.{uCost, uAddress, uPayload, uPort,
      uCapability, uState, uLeakage, uErasure, uOutput}
      M measure schema AdversarialAddress ClosedWorldAddress.adversary)
    (environment : PPTEnvironment.{uCost, uAddress, uPayload, uPort,
      uCapability, uState, uLeakage, uErasure, uOutput}
      M measure schema EnvironmentAddress ClosedWorldAddress.environment)
    (sec : Crypto.SecPar),
      Configuration
        (dispatchFamily environment.toEnvironment.machine functionality.machine
          simulator.toSimulator.machine network.machine)
        (Corruption.layeredPolicy params) sec
  realCertificate : ∀ adversary environment,
    PPTExecutionCertificate
      (family := dispatchFamily environment.toEnvironment.machine
        components.toAddressedITM adversary.toAdversary.machine network.machine)
      (policy := Corruption.layeredPolicy params) measure kernelAlgebra
      (fun sec => network.adapter
        (dispatchFamily environment.toEnvironment.machine
          components.toAddressedITM adversary.toAdversary.machine network.machine)
        sec)
      (realInitial adversary environment)
  idealCertificate : ∀ simulator environment,
    PPTExecutionCertificate
      (family := dispatchFamily environment.toEnvironment.machine
        functionality.machine simulator.toSimulator.machine network.machine)
      (policy := Corruption.layeredPolicy params) measure kernelAlgebra
      (fun sec => network.adapter
        (dispatchFamily environment.toEnvironment.machine functionality.machine
          simulator.toSimulator.machine network.machine) sec)
      (idealInitial simulator environment)

namespace ExecutableLayered

/--
Package the concrete layered dispatchers as the generic executable experiment.

No role or policy field is reconstructed here: all four real component classes,
the full-address ideal functionality, the network, and the shared layered
policy are copied directly into the indexed execution data.
-/
noncomputable def toExecutableExperiment
    (layered : ExecutableLayered.{uCost, uAddress, uPayload, uPort,
      uCapability, uState, uLeakage, uErasure, uOutput}
      (M := M) (measure := measure) (params := params)
      (Tag := Tag) (EnvironmentAddress := EnvironmentAddress)
      (AdversarialAddress := AdversarialAddress)
      (NetworkAddress := NetworkAddress) (schema := schema)) :
    ExecutableExperiment.{uCost, uAddress, uPayload, uPort,
      uCapability, uState, uLeakage, uErasure, uOutput}
      (M := M) (measure := measure) (worldSchema := schema) where
  policy := Corruption.layeredPolicy params
  protocol := layered.components.toProtocol
  functionality := layered.functionality.toIdealFunctionality
  network := layered.network
  realData := fun adversary environment =>
    { kernelAlgebra := layered.kernelAlgebra
      initial := layered.realInitial adversary environment
      certificate := layered.realCertificate adversary environment }
  idealData := fun simulator environment =>
    { kernelAlgebra := layered.kernelAlgebra
      initial := layered.idealInitial simulator environment
      certificate := layered.idealCertificate simulator environment }

@[simp] theorem toExecutableExperiment_policy
    (layered : ExecutableLayered.{uCost, uAddress, uPayload, uPort,
      uCapability, uState, uLeakage, uErasure, uOutput}
      (M := M) (measure := measure) (params := params)
      (Tag := Tag) (EnvironmentAddress := EnvironmentAddress)
      (AdversarialAddress := AdversarialAddress)
      (NetworkAddress := NetworkAddress) (schema := schema)) :
    layered.toExecutableExperiment.policy = Corruption.layeredPolicy params :=
  rfl

@[simp] theorem toExecutableExperiment_protocol
    (layered : ExecutableLayered.{uCost, uAddress, uPayload, uPort,
      uCapability, uState, uLeakage, uErasure, uOutput}
      (M := M) (measure := measure) (params := params)
      (Tag := Tag) (EnvironmentAddress := EnvironmentAddress)
      (AdversarialAddress := AdversarialAddress)
      (NetworkAddress := NetworkAddress) (schema := schema)) :
    layered.toExecutableExperiment.protocol = layered.components.toProtocol :=
  rfl

@[simp] theorem toExecutableExperiment_functionality
    (layered : ExecutableLayered.{uCost, uAddress, uPayload, uPort,
      uCapability, uState, uLeakage, uErasure, uOutput}
      (M := M) (measure := measure) (params := params)
      (Tag := Tag) (EnvironmentAddress := EnvironmentAddress)
      (AdversarialAddress := AdversarialAddress)
      (NetworkAddress := NetworkAddress) (schema := schema)) :
    layered.toExecutableExperiment.functionality =
      layered.functionality.toIdealFunctionality :=
  rfl

end ExecutableLayered

end ExecutableBridge

end Crypto.Infrastructure.UC.Layered

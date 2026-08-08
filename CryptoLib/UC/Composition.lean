import CryptoLib.Protocol.Functionality
import CryptoLib.UC.Kernel

namespace CryptoLib.UC

open CryptoLib.Protocol
open CryptoLib.Core.Infrastructure.Computation.Cost

universe uCost uAddress uPayload uPort uCapability
universe uState uLeakage uErasure uOutput

variable {M : CostModel.{uCost}}
variable {EnvironmentAddress SystemAddress AdversarialAddress NetworkAddress :
  Type uAddress}
variable [DecidableEq EnvironmentAddress] [DecidableEq SystemAddress]
variable [DecidableEq AdversarialAddress] [DecidableEq NetworkAddress]

/-- The common global address type used by both real and ideal executions. -/
abbrev WorldAddress
    (EnvironmentAddress SystemAddress AdversarialAddress NetworkAddress :
      Type uAddress) :=
  ClosedWorldAddress EnvironmentAddress SystemAddress
    AdversarialAddress NetworkAddress

variable {schema : PortSchema.{uAddress, uPayload, uPort, uCapability}
    (WorldAddress EnvironmentAddress SystemAddress
      AdversarialAddress NetworkAddress)}

/--
Dispatch four address-owned ITMs as one global, dependently typed family.

Every handler is selected solely by the constructor of the global address.
Consequently the global `LocalStore` retains the precise state type at each
address without type erasure, casts, or a second interpreter.
-/
def dispatchFamily
    (environment : AddressedITM.{uCost, uAddress, uPayload, uPort, uCapability,
      uState, uLeakage, uErasure, uOutput}
      M schema EnvironmentAddress ClosedWorldAddress.environment)
    (system : AddressedITM.{uCost, uAddress, uPayload, uPort, uCapability,
      uState, uLeakage, uErasure, uOutput}
      M schema SystemAddress ClosedWorldAddress.system)
    (adversarial : AddressedITM.{uCost, uAddress, uPayload, uPort, uCapability,
      uState, uLeakage, uErasure, uOutput}
      M schema AdversarialAddress ClosedWorldAddress.adversary)
    (network : AddressedITM.{uCost, uAddress, uPayload, uPort, uCapability,
      uState, uLeakage, uErasure, uOutput}
      M schema NetworkAddress ClosedWorldAddress.network) :
    ITMFamily.{uCost, uAddress, uPayload, uPort, uCapability,
      uState, uLeakage, uErasure, uOutput}
      M (WorldAddress EnvironmentAddress SystemAddress
        AdversarialAddress NetworkAddress) schema where
  State sec address :=
    match address with
    | .environment localAddress => environment.State sec localAddress
    | .system localAddress => system.State sec localAddress
    | .adversary localAddress => adversarial.State sec localAddress
    | .network localAddress => network.State sec localAddress
  Leakage sec address :=
    match address with
    | .environment localAddress => environment.Leakage sec localAddress
    | .system localAddress => system.Leakage sec localAddress
    | .adversary localAddress => adversarial.Leakage sec localAddress
    | .network localAddress => network.Leakage sec localAddress
  Erasure sec address :=
    match address with
    | .environment localAddress => environment.Erasure sec localAddress
    | .system localAddress => system.Erasure sec localAddress
    | .adversary localAddress => adversarial.Erasure sec localAddress
    | .network localAddress => network.Erasure sec localAddress
  Output sec address :=
    match address with
    | .environment localAddress => environment.Output sec localAddress
    | .system localAddress => system.Output sec localAddress
    | .adversary localAddress => adversarial.Output sec localAddress
    | .network localAddress => network.Output sec localAddress
  init sec address :=
    match address with
    | .environment localAddress => environment.init sec localAddress
    | .system localAddress => system.init sec localAddress
    | .adversary localAddress => adversarial.init sec localAddress
    | .network localAddress => network.init sec localAddress
  activate sec address state input :=
    match address with
    | .environment localAddress =>
        environment.activate sec localAddress state input
    | .system localAddress => system.activate sec localAddress state input
    | .adversary localAddress =>
        adversarial.activate sec localAddress state input
    | .network localAddress => network.activate sec localAddress state input
  applyErasure sec address request state :=
    match address with
    | .environment localAddress =>
        environment.applyErasure sec localAddress request state
    | .system localAddress =>
        system.applyErasure sec localAddress request state
    | .adversary localAddress =>
        adversarial.applyErasure sec localAddress request state
    | .network localAddress =>
        network.applyErasure sec localAddress request state
  leak sec address state :=
    match address with
    | .environment localAddress => environment.leak sec localAddress state
    | .system localAddress => system.leak sec localAddress state
    | .adversary localAddress => adversarial.leak sec localAddress state
    | .network localAddress => network.leak sec localAddress state

namespace Environment

/--
Project a closed-world output to the decision owned by the environment.

Only an output whose source lies in the environment address summand is
observable.  A protocol, functionality, adversarial, or network component
cannot terminate the experiment with a freely chosen Boolean merely by
emitting its own output.
-/
def closedWorldDecision
    (environment : Environment.{uCost, uAddress, uPayload, uPort, uCapability,
      uState, uLeakage, uErasure, uOutput}
      M schema EnvironmentAddress ClosedWorldAddress.environment)
    (system : AddressedITM.{uCost, uAddress, uPayload, uPort, uCapability,
      uState, uLeakage, uErasure, uOutput}
      M schema SystemAddress ClosedWorldAddress.system)
    (adversarial : AddressedITM.{uCost, uAddress, uPayload, uPort, uCapability,
      uState, uLeakage, uErasure, uOutput}
      M schema AdversarialAddress ClosedWorldAddress.adversary)
    (network : AddressedITM.{uCost, uAddress, uPayload, uPort, uCapability,
      uState, uLeakage, uErasure, uOutput}
      M schema NetworkAddress ClosedWorldAddress.network)
    (sec : CryptoLib.Core.SecPar)
    (result : MachineOutput
      (dispatchFamily environment.machine system adversarial network) sec) : Bool :=
  match result with
  | ⟨ClosedWorldAddress.environment address, value⟩ =>
      (Eq.mp (environment.output_isBool sec address) value).down
  | ⟨ClosedWorldAddress.system _, _⟩ => false
  | ⟨ClosedWorldAddress.adversary _, _⟩ => false
  | ⟨ClosedWorldAddress.network _, _⟩ => false

end Environment

/--
A real closed world contains all four concrete components and its unique kernel
configuration.  The initial configuration is indexed by their dispatched
family, so it cannot be reused with different component handlers.
-/
structure RealWorld
    (M : CostModel.{uCost})
    (EnvironmentAddress SystemAddress AdversarialAddress NetworkAddress :
      Type uAddress)
    [DecidableEq EnvironmentAddress] [DecidableEq SystemAddress]
    [DecidableEq AdversarialAddress] [DecidableEq NetworkAddress]
    (schema : PortSchema.{uAddress, uPayload, uPort, uCapability}
      (WorldAddress EnvironmentAddress SystemAddress
        AdversarialAddress NetworkAddress)) where
  environment : Environment.{uCost, uAddress, uPayload, uPort, uCapability,
    uState, uLeakage, uErasure, uOutput}
    M schema EnvironmentAddress ClosedWorldAddress.environment
  protocol : Protocol.{uCost, uAddress, uPayload, uPort, uCapability,
    uState, uLeakage, uErasure, uOutput}
    M schema SystemAddress ClosedWorldAddress.system
  adversary : Adversary.{uCost, uAddress, uPayload, uPort, uCapability,
    uState, uLeakage, uErasure, uOutput}
    M schema AdversarialAddress ClosedWorldAddress.adversary
  network : Network.{uCost, uAddress, uPayload, uPort, uCapability,
    uState, uLeakage, uErasure, uOutput}
    M schema NetworkAddress ClosedWorldAddress.network
  policy : CorruptionPolicy
    (WorldAddress EnvironmentAddress SystemAddress
      AdversarialAddress NetworkAddress)
  kernelCost : KernelCost M
    (WorldAddress EnvironmentAddress SystemAddress
      AdversarialAddress NetworkAddress)
  initial : ∀ sec, Configuration
    (dispatchFamily environment.machine protocol.machine
      adversary.machine network.machine)
    policy sec

/--
An ideal closed world has the same environment, address schema, network, and
corruption-policy types as a real world, but distinct functionality and
simulator components.
-/
structure IdealWorld
    (M : CostModel.{uCost})
    (EnvironmentAddress SystemAddress AdversarialAddress NetworkAddress :
      Type uAddress)
    [DecidableEq EnvironmentAddress] [DecidableEq SystemAddress]
    [DecidableEq AdversarialAddress] [DecidableEq NetworkAddress]
    (schema : PortSchema.{uAddress, uPayload, uPort, uCapability}
      (WorldAddress EnvironmentAddress SystemAddress
        AdversarialAddress NetworkAddress)) where
  environment : Environment.{uCost, uAddress, uPayload, uPort, uCapability,
    uState, uLeakage, uErasure, uOutput}
    M schema EnvironmentAddress ClosedWorldAddress.environment
  functionality : IdealFunctionality.{uCost, uAddress, uPayload, uPort,
    uCapability, uState, uLeakage, uErasure, uOutput}
    M schema SystemAddress ClosedWorldAddress.system
  simulator : Simulator.{uCost, uAddress, uPayload, uPort, uCapability,
    uState, uLeakage, uErasure, uOutput}
    M schema AdversarialAddress ClosedWorldAddress.adversary
  network : Network.{uCost, uAddress, uPayload, uPort, uCapability,
    uState, uLeakage, uErasure, uOutput}
    M schema NetworkAddress ClosedWorldAddress.network
  policy : CorruptionPolicy
    (WorldAddress EnvironmentAddress SystemAddress
      AdversarialAddress NetworkAddress)
  kernelCost : KernelCost M
    (WorldAddress EnvironmentAddress SystemAddress
      AdversarialAddress NetworkAddress)
  initial : ∀ sec, Configuration
    (dispatchFamily environment.machine functionality.machine
      simulator.machine network.machine)
    policy sec

/-- Assemble the environment, protocol, adversary, and network as one real world. -/
def composeReal
    (environment : Environment.{uCost, uAddress, uPayload, uPort, uCapability,
      uState, uLeakage, uErasure, uOutput}
      M schema EnvironmentAddress ClosedWorldAddress.environment)
    (protocol : Protocol.{uCost, uAddress, uPayload, uPort, uCapability,
      uState, uLeakage, uErasure, uOutput}
      M schema SystemAddress ClosedWorldAddress.system)
    (adversary : Adversary.{uCost, uAddress, uPayload, uPort, uCapability,
      uState, uLeakage, uErasure, uOutput}
      M schema AdversarialAddress ClosedWorldAddress.adversary)
    (network : Network.{uCost, uAddress, uPayload, uPort, uCapability,
      uState, uLeakage, uErasure, uOutput}
      M schema NetworkAddress ClosedWorldAddress.network)
    (policy : CorruptionPolicy
      (WorldAddress EnvironmentAddress SystemAddress
        AdversarialAddress NetworkAddress))
    (kernelCost : KernelCost M
      (WorldAddress EnvironmentAddress SystemAddress
        AdversarialAddress NetworkAddress))
    (initial : ∀ sec, Configuration
      (dispatchFamily environment.machine protocol.machine
        adversary.machine network.machine)
      policy sec) :
    RealWorld.{uCost, uAddress, uPayload, uPort, uCapability,
      uState, uLeakage, uErasure, uOutput}
      M EnvironmentAddress SystemAddress AdversarialAddress NetworkAddress schema where
  environment := environment
  protocol := protocol
  adversary := adversary
  network := network
  policy := policy
  kernelCost := kernelCost
  initial := initial

/-- Assemble the same environment with functionality, simulator, and network. -/
def composeIdeal
    (environment : Environment.{uCost, uAddress, uPayload, uPort, uCapability,
      uState, uLeakage, uErasure, uOutput}
      M schema EnvironmentAddress ClosedWorldAddress.environment)
    (functionality : IdealFunctionality.{uCost, uAddress, uPayload, uPort,
      uCapability, uState, uLeakage, uErasure, uOutput}
      M schema SystemAddress ClosedWorldAddress.system)
    (simulator : Simulator.{uCost, uAddress, uPayload, uPort, uCapability,
      uState, uLeakage, uErasure, uOutput}
      M schema AdversarialAddress ClosedWorldAddress.adversary)
    (network : Network.{uCost, uAddress, uPayload, uPort, uCapability,
      uState, uLeakage, uErasure, uOutput}
      M schema NetworkAddress ClosedWorldAddress.network)
    (policy : CorruptionPolicy
      (WorldAddress EnvironmentAddress SystemAddress
        AdversarialAddress NetworkAddress))
    (kernelCost : KernelCost M
      (WorldAddress EnvironmentAddress SystemAddress
        AdversarialAddress NetworkAddress))
    (initial : ∀ sec, Configuration
      (dispatchFamily environment.machine functionality.machine
        simulator.machine network.machine)
      policy sec) :
    IdealWorld.{uCost, uAddress, uPayload, uPort, uCapability,
      uState, uLeakage, uErasure, uOutput}
      M EnvironmentAddress SystemAddress AdversarialAddress NetworkAddress schema where
  environment := environment
  functionality := functionality
  simulator := simulator
  network := network
  policy := policy
  kernelCost := kernelCost
  initial := initial

namespace Network

/-- Specialize a network's typed routing actions to one dispatched family. -/
def adapter
    {LocalAddress : Type uAddress}
    {embed : LocalAddress →
      WorldAddress EnvironmentAddress SystemAddress
        AdversarialAddress NetworkAddress}
    (network : Network.{uCost, uAddress, uPayload, uPort, uCapability,
      uState, uLeakage, uErasure, uOutput}
      M schema LocalAddress embed)
    (family : ITMFamily.{uCost, uAddress, uPayload, uPort, uCapability,
      uState, uLeakage, uErasure, uOutput}
      M (WorldAddress EnvironmentAddress SystemAddress
        AdversarialAddress NetworkAddress) schema)
    (sec : CryptoLib.Core.SecPar) : NetworkAdapter family sec where
  observe := network.observe
  control := network.control
  leakage := fun target value => network.leakage target value

end Network

namespace RealWorld

/-- The sole global ITM family of a real closed world. -/
def family
    (world : RealWorld.{uCost, uAddress, uPayload, uPort, uCapability,
      uState, uLeakage, uErasure, uOutput}
      M EnvironmentAddress SystemAddress AdversarialAddress NetworkAddress schema) :=
  dispatchFamily world.environment.machine world.protocol.machine
    world.adversary.machine world.network.machine

/-- The kernel routing adapter of a real closed world. -/
def networkAdapter
    (world : RealWorld.{uCost, uAddress, uPayload, uPort, uCapability,
      uState, uLeakage, uErasure, uOutput}
      M EnvironmentAddress SystemAddress AdversarialAddress NetworkAddress schema)
    (sec : CryptoLib.Core.SecPar) : NetworkAdapter world.family sec :=
  CryptoLib.UC.Network.adapter world.network world.family sec

/-- The unique Boolean observer induced by the real world's environment. -/
def decision
    (world : RealWorld.{uCost, uAddress, uPayload, uPort, uCapability,
      uState, uLeakage, uErasure, uOutput}
      M EnvironmentAddress SystemAddress AdversarialAddress NetworkAddress schema)
    (sec : CryptoLib.Core.SecPar) : MachineOutput world.family sec → Bool :=
  CryptoLib.UC.Environment.closedWorldDecision world.environment world.protocol.machine
    world.adversary.machine world.network.machine sec

/-- Execute a real world through the unique exact kernel runner. -/
noncomputable def runCosted
    (world : RealWorld.{uCost, uAddress, uPayload, uPort, uCapability,
      uState, uLeakage, uErasure, uOutput}
      M EnvironmentAddress SystemAddress AdversarialAddress NetworkAddress schema)
    (sec : CryptoLib.Core.SecPar) (activationFuel : Nat) :
    RandCosted M (Kernel.ExecutionResult world.family world.policy sec) :=
  Kernel.runCosted world.kernelCost (world.networkAdapter sec)
    activationFuel (world.initial sec)

end RealWorld

namespace IdealWorld

/-- The sole global ITM family of an ideal closed world. -/
def family
    (world : IdealWorld.{uCost, uAddress, uPayload, uPort, uCapability,
      uState, uLeakage, uErasure, uOutput}
      M EnvironmentAddress SystemAddress AdversarialAddress NetworkAddress schema) :=
  dispatchFamily world.environment.machine world.functionality.machine
    world.simulator.machine world.network.machine

/-- The kernel routing adapter of an ideal closed world. -/
def networkAdapter
    (world : IdealWorld.{uCost, uAddress, uPayload, uPort, uCapability,
      uState, uLeakage, uErasure, uOutput}
      M EnvironmentAddress SystemAddress AdversarialAddress NetworkAddress schema)
    (sec : CryptoLib.Core.SecPar) : NetworkAdapter world.family sec :=
  CryptoLib.UC.Network.adapter world.network world.family sec

/-- The unique Boolean observer induced by the ideal world's environment. -/
def decision
    (world : IdealWorld.{uCost, uAddress, uPayload, uPort, uCapability,
      uState, uLeakage, uErasure, uOutput}
      M EnvironmentAddress SystemAddress AdversarialAddress NetworkAddress schema)
    (sec : CryptoLib.Core.SecPar) : MachineOutput world.family sec → Bool :=
  CryptoLib.UC.Environment.closedWorldDecision world.environment world.functionality.machine
    world.simulator.machine world.network.machine sec

/-- Execute an ideal world through the unique exact kernel runner. -/
noncomputable def runCosted
    (world : IdealWorld.{uCost, uAddress, uPayload, uPort, uCapability,
      uState, uLeakage, uErasure, uOutput}
      M EnvironmentAddress SystemAddress AdversarialAddress NetworkAddress schema)
    (sec : CryptoLib.Core.SecPar) (activationFuel : Nat) :
    RandCosted M (Kernel.ExecutionResult world.family world.policy sec) :=
  Kernel.runCosted world.kernelCost (world.networkAdapter sec)
    activationFuel (world.initial sec)

end IdealWorld

end CryptoLib.UC

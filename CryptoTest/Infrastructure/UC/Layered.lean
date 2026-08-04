import Crypto.Infrastructure.UC.Layered
import Mathlib.Tactic

namespace CryptoTest.Infrastructure.UC.Layered

open Crypto.Infrastructure.Computation.Cost
open Crypto.Infrastructure.UC
open Crypto.Infrastructure.UC.Layered

def params : Parameters where
  partiesPerLayer := 1
  maxCorrupt := 1
  layers := 1

abbrev GlobalAddress :=
  Corruption.GlobalAddress Nat Unit Unit Unit params

def schema : PortSchema.{0, 0, 0, 0} GlobalAddress where
  Port := fun _address _direction _payload => Unit
  CanConnect := fun _sourcePort _targetPort => Unit
  CanSendAs := fun _controller _claimed => Unit
  route := fun _sourcePort _targetPort _capability => .direct

def sid : SID Nat := ⟨7, []⟩

def partyId : PartyId params :=
  (⟨0, by decide⟩, ⟨0, by decide⟩)

def partyAddress : PartyAddress Nat params := ⟨sid, partyId⟩

def boundaryAddress : BoundaryAddress Nat := ⟨sid, .input 0⟩

noncomputable def partyStep :
    PartyStep.{0, 0, 0, 0, 0, 0, 0, 0, 0}
      CostModel.nat params Nat schema partyEmbed where
  State := fun _sec _address => Nat
  Leakage := fun _sec _address => Nat
  Erasure := fun _sec _address => Unit
  Output := fun _sec _address => Nat
  init := fun _sec _address =>
    RandCosted.liftCosted (⟨11, 1⟩ : Costed CostModel.nat Nat)
  activate := fun _sec _address state _input =>
    RandCosted.pure CostModel.nat ⟨state, LocalAction.yield⟩
  applyErasure := fun _sec _address _request state => ⟨state, 0⟩
  leak := fun _sec _address state => ⟨state, 0⟩

noncomputable def constantMachine
    {LocalAddress : Type}
    {embed : LocalAddress → GlobalAddress}
    (value cost : Nat) :
    AddressedITM.{0, 0, 0, 0, 0, 0, 0, 0, 0}
      CostModel.nat schema LocalAddress embed where
  State := fun _sec _address => Nat
  Leakage := fun _sec _address => Nat
  Erasure := fun _sec _address => Unit
  Output := fun _sec _address => Nat
  init := fun _sec _address =>
    RandCosted.liftCosted (⟨value, cost⟩ : Costed CostModel.nat Nat)
  activate := fun _sec _address state _input =>
    RandCosted.liftCosted
      (⟨⟨state + value, LocalAction.yield⟩, cost⟩ :
        Costed CostModel.nat
          (ActivationResult Nat (LocalAction schema _ Unit Nat)))
  applyErasure := fun _sec _address _request state => ⟨state, 0⟩
  leak := fun _sec _address state => ⟨state, 0⟩

noncomputable def components :
    SystemComponents.{0, 0, 0, 0, 0, 0, 0, 0, 0}
      CostModel.nat params Nat Unit Unit Unit schema where
  parties := partyStep
  broadcast := ⟨constantMachine 22 2⟩
  corruption := ⟨constantMachine 33 3⟩
  boundary := ⟨constantMachine 44 4⟩

/-! Every layered role reaches its own exact handler through the system dispatcher. -/

example :
    components.toAddressedITM.init 0 ⟨sid, .party partyId⟩ =
      RandCosted.liftCosted (⟨11, 1⟩ : Costed CostModel.nat Nat) :=
  rfl

example :
    components.toAddressedITM.init 0 ⟨sid, .trusted .broadcastManager⟩ =
      RandCosted.liftCosted (⟨22, 2⟩ : Costed CostModel.nat Nat) :=
  rfl

example :
    components.toAddressedITM.init 0 ⟨sid, .trusted .corruptionManager⟩ =
      RandCosted.liftCosted (⟨33, 3⟩ : Costed CostModel.nat Nat) :=
  rfl

example :
    components.toAddressedITM.init 0 ⟨sid, .boundary (.input 0)⟩ =
      RandCosted.liftCosted (⟨44, 4⟩ : Costed CostModel.nat Nat) :=
  rfl

example : components.toProtocol.machine = components.toAddressedITM :=
  rfl

/-! A real FIFO activation reaches the broadcast handler through dispatchFamily. -/

def environmentEmbed (_address : Unit) : GlobalAddress := .environment ()
def adversaryEmbed (_address : Unit) : GlobalAddress := .adversary ()
def networkEmbed (_address : Unit) : GlobalAddress := .network ()

noncomputable def layeredFamily :=
  dispatchFamily
    (constantMachine (embed := environmentEmbed) 0 0)
    components.toAddressedITM
    (constantMachine (embed := adversaryEmbed) 0 0)
    (constantMachine (embed := networkEmbed) 0 0)

def broadcastAddress : GlobalAddress :=
  broadcastManagerEmbed (EnvironmentAddress := Unit)
    (AdversarialAddress := Unit) (NetworkAddress := Unit) sid

def layeredNetwork (sec : Crypto.SecPar) : NetworkAdapter layeredFamily sec where
  observe := fun emission => QueuedActivation.ofEmission emission
  control := fun activation => activation
  leakage := fun target _leakage => QueuedActivation.resume target

noncomputable def layeredConfiguration :
    Configuration layeredFamily (Corruption.layeredPolicy params) 0 where
  state := fun address =>
    match address with
    | .environment _ => show Option Nat from some 7
    | .system ⟨_, .party _⟩ => show Option Nat from some 7
    | .system ⟨_, .trusted .broadcastManager⟩ => show Option Nat from some 7
    | .system ⟨_, .trusted .corruptionManager⟩ => show Option Nat from some 7
    | .system ⟨_, .boundary _⟩ => show Option Nat from some 7
    | .adversary _ => show Option Nat from some 7
    | .network _ => show Option Nat from some 7
  queue := [.activation (QueuedActivation.resume broadcastAddress)]
  corrupted := ∅
  output := none
  trace := []
  corruptionInvariant := by
    constructor
    · change Corruption.Eligible params ∅
      constructor
      · intro address haddress
        simp at haddress
      · intro otherSid layer
        simp [Corruption.countAt, Corruption.partiesAt]
    · intro address haddress
      simp at haddress

noncomputable def observedBroadcastStep : PMF Nat :=
  RandCosted.costDist
    (Kernel.stepOne (KernelAlgebra.zero CostModel.nat GlobalAddress)
      (layeredNetwork 0) layeredConfiguration)

example : observedBroadcastStep = PMF.pure 2 := by
  simp [observedBroadcastStep, layeredConfiguration, layeredFamily,
    layeredNetwork, broadcastAddress, components, constantMachine,
    dispatchFamily, SystemComponents.toAddressedITM,
    broadcastManagerEmbed, QueuedActivation.resume,
    Kernel.stepOne, Kernel.activateHonest,
    Kernel.processAction, Kernel.classify, KernelAlgebra.withCharge,
    KernelAlgebra.charge, KernelAlgebra.zero, Configuration.dequeue,
    Configuration.get, Configuration.set, Configuration.record,
    RandCosted.costDist, RandCosted.liftCosted, RandCosted.pure,
    RandCosted.bind, Costed.bind, Costed.pure, PMF.pure_bind,
    PMF.pure_map, Pure.pure]
  simp [Bind.bind, PMF.pure_map]
  rfl

/-! The canonical embeddings retain the exact session and role. -/

example :
    partyEmbed (EnvironmentAddress := Unit) (AdversarialAddress := Unit)
        (NetworkAddress := Unit) partyAddress =
      ClosedWorldAddress.system ⟨sid, .party partyId⟩ :=
  rfl

example :
    boundaryEmbed (params := params) (EnvironmentAddress := Unit)
        (AdversarialAddress := Unit) (NetworkAddress := Unit) boundaryAddress =
      ClosedWorldAddress.system ⟨sid, .boundary (.input 0)⟩ :=
  rfl

example :
    ¬ (Corruption.layeredPolicy params).mayCorrupt ∅
      (broadcastManagerEmbed (EnvironmentAddress := Unit)
        (AdversarialAddress := Unit) (NetworkAddress := Unit) sid) := by
  change ¬ (_ ∉ (∅ : Finset GlobalAddress) ∧
    Corruption.Eligible params (insert (broadcastManagerEmbed
      (EnvironmentAddress := Unit) (AdversarialAddress := Unit)
      (NetworkAddress := Unit) sid) ∅))
  rintro ⟨_fresh, eligible⟩
  obtain ⟨onlyParties, _threshold⟩ := eligible
  obtain ⟨otherSid, party, equality⟩ := onlyParties
    (broadcastManagerEmbed (EnvironmentAddress := Unit)
      (AdversarialAddress := Unit) (NetworkAddress := Unit) sid) (by simp)
  cases equality

/-! The executable bridge uses the actual layered policy on both sides. -/

section ExecutableBridge

variable
  (layered : ExecutableLayered.{0, 0, 0, 0, 0, 0, 0, 0, 0}
    (M := CostModel.nat) (measure := NatMeasure.nat) (params := params)
    (Tag := Nat) (EnvironmentAddress := Unit)
    (AdversarialAddress := Unit) (NetworkAddress := Unit) (schema := schema))

example :
    layered.toExecutableExperiment.policy = Corruption.layeredPolicy params :=
  rfl

example :
    layered.toExecutableExperiment.protocol.machine =
      layered.components.toAddressedITM :=
  rfl

example :
    layered.toExecutableExperiment.functionality.machine =
      layered.functionality.machine :=
  rfl

noncomputable example
    (adversary : PPTAdversary CostModel.nat NatMeasure.nat schema
      Unit ClosedWorldAddress.adversary)
    (environment : PPTEnvironment CostModel.nat NatMeasure.nat schema
      Unit ClosedWorldAddress.environment) :
    RealExecutionData (Corruption.layeredPolicy params) environment
      layered.components.toProtocol adversary layered.network :=
  layered.toExecutableExperiment.realData adversary environment

noncomputable example
    (simulator : PPTSimulator CostModel.nat NatMeasure.nat schema
      Unit ClosedWorldAddress.adversary)
    (environment : PPTEnvironment CostModel.nat NatMeasure.nat schema
      Unit ClosedWorldAddress.environment) :
    IdealExecutionData (Corruption.layeredPolicy params) environment
      layered.functionality.toIdealFunctionality simulator layered.network :=
  layered.toExecutableExperiment.idealData simulator environment

end ExecutableBridge

end CryptoTest.Infrastructure.UC.Layered

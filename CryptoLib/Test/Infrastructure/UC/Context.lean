import CryptoLib.Core.Infrastructure.UC.Context
import Mathlib.Tactic

namespace CryptoLib.Test.Infrastructure.UC.Context

open CryptoLib.Core.Infrastructure.Asymptotic
open CryptoLib.Core.Infrastructure.Computation.Cost
open CryptoLib.Core.Infrastructure.UC

/-! ## A nontrivial role-preserving address transport -/

abbrev ToyAddress := WorldAddress Unit Bool Unit Unit

def toySchema : PortSchema.{0, 0, 0, 0} ToyAddress where
  Port := fun _address _direction _payload => Unit
  CanConnect := fun _sourcePort _targetPort => Unit
  CanSendAs := fun _controller _claimedSource => Unit
  route := fun _sourcePort _targetPort _capability => .direct

def boolNotRenaming : AddressRenaming Bool Bool where
  toFun := Bool.not
  injective := by
    intro left right equality
    simpa using congrArg Bool.not equality

def toyWorldRenaming : WorldRenaming Unit Bool Unit Unit where
  environment := AddressRenaming.identity Unit
  system := boolNotRenaming
  adversary := AddressRenaming.identity Unit
  network := AddressRenaming.identity Unit

def renameAddress : ToyAddress → ToyAddress := toyWorldRenaming.global

@[simp] theorem renameAddress_environment (address : Unit) :
    renameAddress (.environment address) = .environment address := by
  cases address
  rfl

@[simp] theorem renameAddress_system (address : Bool) :
    renameAddress (.system address) = .system (!address) := rfl

@[simp] theorem renameAddress_adversary (address : Unit) :
    renameAddress (.adversary address) = .adversary address := by
  cases address
  rfl

@[simp] theorem renameAddress_network (address : Unit) :
    renameAddress (.network address) = .network address := by
  cases address
  rfl

@[simp] theorem renameAddress_involutive (address : ToyAddress) :
    renameAddress (renameAddress address) = address := by
  cases address with
  | environment address | adversary address | network address => cases address; rfl
  | system address => cases address <;> rfl

example : renameAddress (.system false) = .system true := rfl

def mapActivationInput {target : ToyAddress} :
    ActivationInput toySchema target →
      ActivationInput toySchema (renameAddress target)
  | .resume => .resume
  | .message incoming => .message {
      Payload := incoming.Payload
      source := ⟨renameAddress incoming.source.address, ()⟩
      targetPort := ()
      capability := ()
      payload := incoming.payload
    }

def mapQueuedActivation (activation : QueuedActivation toySchema) :
    QueuedActivation toySchema :=
  ⟨renameAddress activation.target, mapActivationInput activation.input⟩

def mapEmission {source : ToyAddress} (emission : Emission toySchema source) :
    Emission toySchema (renameAddress source) where
  Payload := emission.Payload
  sourcePort := ()
  target := ⟨renameAddress emission.target.address, ()⟩
  capability := ()
  payload := emission.payload

def toyPortTransport : PortTransport toySchema toyWorldRenaming.global where
  mapActivation := mapQueuedActivation
  activation_target := by intro activation; rfl
  mapEmission := mapEmission
  emission_target := by intro source emission; rfl
  routing_preserved := by intro source emission; rfl
  mapSendAs := fun _authorization => ()

example (activation : QueuedActivation toySchema) :
    (toyPortTransport.mapActivation activation).target =
      renameAddress activation.target :=
  toyPortTransport.activation_target activation

/-! ## Exact configuration and step transport -/

def unitCostModel : CostModel where
  Cost := Unit
  instAddMonoid := inferInstance
  instPartialOrder := inferInstance
  instAddLeftMono := {
    elim := by
      intro left right first _h
      cases left
      cases right
      cases first
      exact le_rfl
  }
  instAddRightMono := {
    elim := by
      intro left right first _h
      cases left
      cases right
      cases first
      exact le_rfl
  }

def unitNatMeasure : NatMeasure unitCostModel := by
  letI := unitCostModel.instAddMonoid
  letI := unitCostModel.instPartialOrder
  exact {
    toNat := {
      toFun := fun _cost => 0
      map_zero' := rfl
      map_add' := by intro _left _right; rfl
    }
    monotone_toNat := by intro _left _right _h; exact Nat.le_refl 0
  }

def addressOutput : ToyAddress → Bool
  | .system address => address
  | .environment _ | .adversary _ | .network _ => false

noncomputable def toyFamily :
    ITMFamily.{0, 0, 0, 0, 0, 0, 0, 0, 0}
      unitCostModel ToyAddress toySchema where
  State := fun _sec _address => Unit
  Leakage := fun _sec _address => Unit
  Erasure := fun _sec _address => Unit
  Output := fun _sec _address => Bool
  init := fun _sec _address => RandCosted.pure unitCostModel ()
  activate := fun _sec address _state _input =>
    RandCosted.pure unitCostModel ⟨(), .output (addressOutput address)⟩
  applyErasure := fun _sec _address _request _state => Costed.pure unitCostModel ()
  leak := fun _sec _address _state => Costed.pure unitCostModel ()

def outerPolicy : CorruptionPolicy ToyAddress :=
  CorruptionPolicy.static {ClosedWorldAddress.system false}

def innerPolicy : CorruptionPolicy ToyAddress :=
  CorruptionPolicy.static {ClosedWorldAddress.system true}

noncomputable def toyNetworkAdapter (_sec : CryptoLib.Core.SecPar) :
    NetworkAdapter toyFamily _sec where
  observe := fun emission => .ofEmission emission
  control := id
  leakage := fun target _leakage => .resume target

section ConfigurationRenaming

variable {sec : CryptoLib.Core.SecPar} {address : ToyAddress}

def mapMachineOutput :
    MachineOutput toyFamily sec → MachineOutput toyFamily sec
  | ⟨source, value⟩ =>
      match source with
      | .system address => ⟨.system (!address), !value⟩
      | .environment address => ⟨.environment address, value⟩
      | .adversary address => ⟨.adversary address, value⟩
      | .network address => ⟨.network address, value⟩

def mapQueuedEvent : QueuedEvent toySchema → QueuedEvent toySchema
  | .activation activation => .activation (mapQueuedActivation activation)
  | .corruptionRequest source target =>
      .corruptionRequest (renameAddress source) (renameAddress target)

def mapLeakage :
    toyFamily.Leakage sec address →
      toyFamily.Leakage sec (renameAddress address) :=
  fun _leakage => ()

def mapErasure :
    toyFamily.Erasure sec address →
      toyFamily.Erasure sec (renameAddress address) :=
  fun _request => ()

/-- The test trace map is the production structural transport, not an
independently chosen event rewrite. -/
noncomputable def mapTraceEvent :
    TraceEvent toyFamily sec → TraceEvent toyFamily sec :=
  KernelSimulation.mapTraceEvent toyWorldRenaming.global toyPortTransport
    (fun _sec _address leakage => mapLeakage leakage)
    (fun _sec _address request => mapErasure request)
    (fun _sec output => mapMachineOutput output) sec

example (sec : CryptoLib.Core.SecPar) :
    mapTraceEvent (sec := sec)
        (.erased (.system false) ()) =
      TraceEvent.erased (.system true) () := rfl

example (sec : CryptoLib.Core.SecPar) :
    mapTraceEvent (sec := sec)
        (.spawned (.system false) (.system true) .resume) =
      TraceEvent.spawned (.system true) (.system false) .resume := rfl

def mapStore (store : LocalStore toyFamily sec) :
    LocalStore toyFamily sec :=
  fun address => store (renameAddress address)

noncomputable def mapConfiguration
    (configuration : Configuration toyFamily outerPolicy sec) :
    Configuration toyFamily innerPolicy sec where
  state := mapStore configuration.state
  queue := configuration.queue.map mapQueuedEvent
  corrupted := configuration.corrupted.image renameAddress
  output := configuration.output.map mapMachineOutput
  trace := configuration.trace.map mapTraceEvent
  corruptionInvariant := by
    have outerAdmissible := configuration.corruptionInvariant.1
    have outerCorrupted : configuration.corrupted = {.system false} :=
      outerAdmissible
    constructor
    · change configuration.corrupted.image renameAddress = {.system true}
      rw [outerCorrupted]
      simp
    · intro address haddress
      have innerCorrupted : configuration.corrupted.image renameAddress =
          {.system true} := by
        rw [outerCorrupted]
        simp
      rw [innerCorrupted] at haddress
      have address_eq : address = .system true := by simpa using haddress
      subst address
      change configuration.state (.system false) = none
      exact configuration.corruptionInvariant.2 (.system false) (by
        rw [outerCorrupted]
        simp)

@[simp] theorem mapConfiguration_queue
    (configuration : Configuration toyFamily outerPolicy sec) :
    (mapConfiguration configuration).queue =
      configuration.queue.map mapQueuedEvent := rfl

@[simp] theorem mapConfiguration_corrupted
    (configuration : Configuration toyFamily outerPolicy sec) :
    (mapConfiguration configuration).corrupted =
      configuration.corrupted.image renameAddress := rfl

@[simp] theorem mapConfiguration_output
    (configuration : Configuration toyFamily outerPolicy sec) :
    (mapConfiguration configuration).output =
      configuration.output.map mapMachineOutput := rfl

@[simp] theorem mapConfiguration_get
    (configuration : Configuration toyFamily outerPolicy sec)
    (address : ToyAddress) :
    (mapConfiguration configuration).get (renameAddress address) =
      (configuration.get address).map (fun state => state) := by
  change configuration.state (renameAddress (renameAddress address)) =
    Option.map (fun state => state) (configuration.state address)
  rw [renameAddress_involutive]
  cases configuration.state address <;> rfl

end ConfigurationRenaming

noncomputable def outerInitial (sec : CryptoLib.Core.SecPar) :
    Configuration toyFamily outerPolicy sec where
  state := LocalStore.set LocalStore.empty (.system true) ()
  queue := [.activation (.resume (.system true))]
  corrupted := {.system false}
  output := none
  trace := []
  corruptionInvariant := by
    constructor
    · rfl
    · intro address haddress
      have address_eq : address = .system false := by simpa using haddress
      subst address
      rfl

noncomputable def innerInitial (sec : CryptoLib.Core.SecPar) :
    Configuration toyFamily innerPolicy sec :=
  mapConfiguration (outerInitial sec)

example (sec : CryptoLib.Core.SecPar) : (outerInitial sec).output = none := rfl

example (sec : CryptoLib.Core.SecPar) :
    (innerInitial sec).queue = [.activation (.resume (.system false))] := rfl

example (sec : CryptoLib.Core.SecPar) :
    (innerInitial sec).get (.system false) = some () := rfl

@[simp] theorem pmf_map_identity {Value : Type} (dist : PMF Value) :
    PMF.map (fun value => value) dist = dist := by
  simpa only using PMF.map_id dist

universe uTestValue

@[simp] theorem zeroKernel_withCharge {Value : Type uTestValue}
    (primitive : KernelPrimitive) (addresses : List ToyAddress)
    (next : RandCosted unitCostModel Value) :
    KernelAlgebra.withCharge
        (KernelAlgebra.zero unitCostModel ToyAddress)
        primitive addresses next = next := by
  unfold KernelAlgebra.withCharge KernelAlgebra.charge KernelAlgebra.zero
  exact RandCosted.pure_bind () (fun _unit => next)

/-- A genuine kernel simulation whose commuting square is consumed at positive
fuel, rather than a final-game equality postulated by the test. -/
noncomputable def toyIdentitySimulation :
    KernelSimulation (AddressRenaming.identity ToyAddress)
      (KernelAlgebra.zero unitCostModel ToyAddress) toyNetworkAdapter
        outerInitial (fun _sec output => output.value)
      (KernelAlgebra.zero unitCostModel ToyAddress) toyNetworkAdapter
        outerInitial (fun _sec output => output.value) :=
  KernelSimulation.identity
    (KernelAlgebra.zero unitCostModel ToyAddress) toyNetworkAdapter outerInitial
      (fun _sec output => output.value)

example (sec : CryptoLib.Core.SecPar) :
    Kernel.decisionDist
        (KernelAlgebra.zero unitCostModel ToyAddress)
        (toyNetworkAdapter sec) (fun output => output.value) 1
        (outerInitial sec) =
      Kernel.decisionDist
        (KernelAlgebra.zero unitCostModel ToyAddress)
        (toyNetworkAdapter sec) (fun output => output.value) 1
        (outerInitial sec) :=
  toyIdentitySimulation.initial_decisionDist_commutes 1 sec

/-!
The initial output is absent and fuel is positive.  Hence these equalities can
only hold if the queued activation is dequeued and dispatched to the selected
system cell.  The outer target is `system true`; the transported inner target
is `system false`.
-/
example (sec : CryptoLib.Core.SecPar) :
    Kernel.decisionDist
        (KernelAlgebra.zero unitCostModel ToyAddress)
        (toyNetworkAdapter sec) (fun output => output.value) 1
        (outerInitial sec) = PMF.pure true := by
  simp [Kernel.decisionDist, Kernel.runCosted, Kernel.stepOne,
    outerInitial, Configuration.dequeue, Configuration.get,
    QueuedActivation.resume, Kernel.activateHonest,
    Kernel.processAction, Configuration.record, Configuration.set,
    Configuration.finish, toyFamily, toyNetworkAdapter,
    Kernel.classify, LocalStore.set, addressOutput,
    PMF.pure_bind, zeroKernel_withCharge]
  simp [RandCosted.bind, RandCosted.pure, RandCosted.liftCosted,
    RandCosted.valueDist, Costed.pure_bind, PMF.pure_bind, PMF.pure_map,
    Pure.pure]
  simp [Bind.bind, PMF.pure_map]
  rfl

example (sec : CryptoLib.Core.SecPar) :
    Kernel.decisionDist
        (KernelAlgebra.zero unitCostModel ToyAddress)
        (toyNetworkAdapter sec) (fun output => !output.value) 1
        (innerInitial sec) = PMF.pure true := by
  simp [Kernel.decisionDist, Kernel.runCosted, Kernel.stepOne,
    innerInitial, mapConfiguration, outerInitial, Configuration.dequeue,
    Configuration.get, QueuedActivation.resume,
    Kernel.activateHonest, Kernel.processAction, Configuration.record,
    Configuration.set, Configuration.finish, toyFamily, toyNetworkAdapter,
    Kernel.classify, LocalStore.set, mapQueuedEvent, mapQueuedActivation,
    mapActivationInput, mapStore, renameAddress,
    toyWorldRenaming, boolNotRenaming, addressOutput,
    PMF.pure_bind, zeroKernel_withCharge]
  simp [RandCosted.bind, RandCosted.pure, RandCosted.liftCosted,
    RandCosted.valueDist, Costed.pure_bind, PMF.pure_bind, PMF.pure_map,
    Pure.pure]
  simp [Bind.bind, PMF.pure_map]
  rfl

/-! ## Structurally assembled certified worlds -/

theorem unitCostBound {Value : Type uTestValue}
    (dist : RandCosted unitCostModel Value) :
    RandCosted.CostBound dist () := by
  intro result _hresult
  cases result.cost
  exact unitCostModel.instPartialOrder.le_refl ()

noncomputable def unitComponentCertificate
    (family : ITMFamily unitCostModel ToyAddress toySchema) :
    ComponentCostCertificate family where
  initBudget := fun _sec _address => ()
  activationBudget := fun _sec _address => ()
  erasureBudget := fun _sec _address => ()
  leakageBudget := fun _sec _address => ()
  init_sound := fun sec address => unitCostBound (family.init sec address)
  activation_sound := fun sec address state input =>
    unitCostBound (family.activate sec address state input)
  erasure_sound := by
    intro sec address request state
    cases (family.applyErasure sec address request state).cost
    exact unitCostModel.instPartialOrder.le_refl ()
  leakage_sound := by
    intro sec address state
    cases (family.leak sec address state).cost
    exact unitCostModel.instPartialOrder.le_refl ()

variable {family : ITMFamily unitCostModel ToyAddress toySchema}

noncomputable def unitStepCertificate
    (network : (sec : CryptoLib.Core.SecPar) → NetworkAdapter family sec) :
    StepCostCertificate
      (KernelAlgebra.zero unitCostModel ToyAddress) network where
  component := unitComponentCertificate family
  kernel := KernelAlgebra.zeroBounds unitCostModel ToyAddress
  atomBudget := fun _sec => ()
  zero_le_atomBudget := by
    intro sec
    exact unitCostModel.instPartialOrder.le_refl ()
  initBudget_le := by
    intro sec address
    exact unitCostModel.instPartialOrder.le_refl ()
  activationBudget_le := by
    intro sec address
    exact unitCostModel.instPartialOrder.le_refl ()
  erasureBudget_le := by
    intro sec address
    exact unitCostModel.instPartialOrder.le_refl ()
  leakageBudget_le := by
    intro sec address
    exact unitCostModel.instPartialOrder.le_refl ()
  kernelBudget_le := by
    intro sec Result operation
    cases operation
    exact unitCostModel.instPartialOrder.le_refl ()

/--
External operational model used by the structural UC fixtures below.

No instance is provided by the test suite.  Consequently the fixtures remain
parametric in an explicit trust-boundary assumption, and the annotation-level
zero-cost algebra cannot manufacture PPT admission on its own.
-/
class ToyExecutionAdmissionModel : Prop where
  closedAdmission :
    ∀ {family : ITMFamily unitCostModel ToyAddress toySchema}
      {policy : CorruptionPolicy ToyAddress}
      (network : (sec : CryptoLib.Core.SecPar) → NetworkAdapter family sec),
      CryptoLib.Core.Infrastructure.Complexity.PPTAdmissible
        unitCostModel unitNatMeasure
        (Input := fun sec => Configuration family policy sec)
        (Output := fun sec _configuration =>
          Kernel.ExecutionResult family policy sec)
        (fun sec configuration =>
          Kernel.runCosted (KernelAlgebra.zero unitCostModel ToyAddress)
            (network sec) 1 configuration)
        (fun _sec => 0)

variable [ToyExecutionAdmissionModel]

noncomputable def deadlockPPTCertificate
    {policy : CorruptionPolicy ToyAddress}
    (network : (sec : CryptoLib.Core.SecPar) → NetworkAdapter family sec)
    (initial : (sec : CryptoLib.Core.SecPar) → Configuration family policy sec)
    (queue_empty : ∀ sec, (initial sec).queue = [])
    (output_none : ∀ sec, (initial sec).output = none) :
    PPTExecutionCertificate unitNatMeasure
      (KernelAlgebra.zero unitCostModel ToyAddress) network initial where
  step := unitStepCertificate network
  activationLimit := fun _sec => 1
  stepRuntime := fun _sec => 0
  budget_le_stepRuntime := by
    intro sec
    rfl
  activationLimit_isPoly := IsPolyBounded.const 1
  stepRuntime_isPoly := IsPolyBounded.zero
  admission := ToyExecutionAdmissionModel.closedAdmission network
  fuel := {
    noTimeout := by
      intro sec result hresult
      have run_eq :
          Kernel.runCosted (KernelAlgebra.zero unitCostModel ToyAddress)
              (network sec) 1 (initial sec) =
            RandCosted.pure unitCostModel
              ({ outcome := Kernel.ExecutionOutcome.deadlock
                 configuration := initial sec } :
                Kernel.ExecutionResult family policy sec) := by
        simp [Kernel.runCosted, Kernel.stepOne, output_none sec,
          Configuration.dequeue, queue_empty sec, zeroKernel_withCharge]
        rfl
      rw [run_eq] at hresult
      simp only [RandCosted.pure, RandCosted.liftCosted,
        PMF.mem_support_pure_iff] at hresult
      subst result
      intro equality
      cases equality
    stable := by
      intro sec extra
      have execution_eq (fuel : Nat) :
          Kernel.runCosted (KernelAlgebra.zero unitCostModel ToyAddress)
              (network sec) (fuel + 1) (initial sec) =
            RandCosted.pure unitCostModel
              ({ outcome := Kernel.ExecutionOutcome.deadlock
                 configuration := initial sec } :
                Kernel.ExecutionResult family policy sec) := by
        simp [Kernel.runCosted, Kernel.stepOne, output_none sec,
          Configuration.dequeue, queue_empty sec, zeroKernel_withCharge]
        rfl
      rw [Nat.add_comm 1 extra, execution_eq extra, execution_eq 0]
  }

/-! ## The observer is owned by the environment -/

noncomputable def boolITM
    {LocalAddress : Type} (embed : LocalAddress → ToyAddress)
    (valueAt : LocalAddress → Bool) :
    AddressedITM unitCostModel toySchema LocalAddress embed where
  State := fun _sec _address => Unit
  Leakage := fun _sec _address => Unit
  Erasure := fun _sec _address => Unit
  Output := fun _sec _address => ULift Bool
  init := fun _sec _address => RandCosted.pure unitCostModel ()
  activate := fun _sec address _state _input =>
    RandCosted.pure unitCostModel ⟨(), .output (ULift.up (valueAt address))⟩
  applyErasure := fun _sec _address _request _state =>
    Costed.pure unitCostModel ()
  leak := fun _sec _address _state => Costed.pure unitCostModel ()

noncomputable def observingEnvironment :
    Environment unitCostModel toySchema Unit ClosedWorldAddress.environment where
  machine := boolITM ClosedWorldAddress.environment (fun _address => true)
  output_isBool := by intro _sec _address; rfl

noncomputable def observingProtocol :
    Protocol unitCostModel toySchema Bool ClosedWorldAddress.system where
  machine := boolITM ClosedWorldAddress.system id

noncomputable def observingAdversary :
    Adversary unitCostModel toySchema Unit ClosedWorldAddress.adversary where
  machine := boolITM ClosedWorldAddress.adversary (fun _address => false)

noncomputable def observingNetwork :
    Network unitCostModel toySchema Unit ClosedWorldAddress.network where
  machine := boolITM ClosedWorldAddress.network (fun _address => false)
  observe := fun emission => .ofEmission emission
  control := id
  leakage := fun target _leakage => .resume target

noncomputable abbrev ObservingFamily :=
  dispatchFamily observingEnvironment.machine observingProtocol.machine
    observingAdversary.machine observingNetwork.machine

noncomputable def observingInitial (sec : CryptoLib.Core.SecPar) :
    Configuration ObservingFamily CorruptionPolicy.incorruptible sec where
  state := LocalStore.set LocalStore.empty (.environment ()) ()
  queue := [.activation (.resume (.environment ()))]
  corrupted := ∅
  output := none
  trace := []
  corruptionInvariant := by
    constructor
    · rfl
    · intro address haddress
      simp at haddress

noncomputable def observingWorld :
    RealWorld unitCostModel Unit Bool Unit Unit toySchema :=
  composeReal observingEnvironment observingProtocol observingAdversary
    observingNetwork CorruptionPolicy.incorruptible
      (KernelAlgebra.zero unitCostModel ToyAddress) observingInitial

noncomputable def environmentOwnedOutput (sec : CryptoLib.Core.SecPar) :
    MachineOutput observingWorld.family sec :=
  ⟨.environment (), ULift.up true⟩

noncomputable def systemOwnedOutput (sec : CryptoLib.Core.SecPar) :
    MachineOutput observingWorld.family sec :=
  ⟨.system false, ULift.up true⟩

example (sec : CryptoLib.Core.SecPar) :
    observingWorld.decision sec (environmentOwnedOutput sec) = true := rfl

example (sec : CryptoLib.Core.SecPar) :
    observingWorld.decision sec (systemOwnedOutput sec) = false := rfl

/-- Positive fuel starts from no output, dispatches the queued environment
activation, and applies the environment's nonconstant Boolean observer. -/
example (sec : CryptoLib.Core.SecPar) :
    observingWorld.execution (fun _sec => 1) sec = PMF.pure true := by
  simp [RealWorld.execution, RealWorld.runCosted, observingWorld, composeReal,
    Kernel.runCosted, Kernel.stepOne, observingInitial,
    Configuration.dequeue, Configuration.get, QueuedActivation.resume,
    Kernel.activateHonest, Kernel.processAction, Configuration.record,
    Configuration.set, Configuration.finish, dispatchFamily,
    observingEnvironment, observingProtocol, observingAdversary,
    observingNetwork, boolITM, Network.adapter, RealWorld.networkAdapter,
    RealWorld.family, RealWorld.decision,
    Kernel.classify, LocalStore.set, PMF.pure_bind, zeroKernel_withCharge]
  simp [RandCosted.bind, RandCosted.pure, RandCosted.liftCosted,
    RandCosted.valueDist, Costed.pure_bind, PMF.pure_bind, PMF.pure_map,
    Pure.pure]
  simp [Bind.bind, PMF.pure_map]
  rfl

/-! ## Concrete structural context and universal composition -/

noncomputable def observingFunctionality :
    IdealFunctionality unitCostModel toySchema Bool
      ClosedWorldAddress.system where
  machine := observingProtocol.machine

noncomputable def simulatorOfAdversary
    (adversary : PPTAdversary unitCostModel unitNatMeasure toySchema Unit
      ClosedWorldAddress.adversary) :
    PPTSimulator unitCostModel unitNatMeasure toySchema Unit
      ClosedWorldAddress.adversary where
  toSimulator := { machine := adversary.toAdversary.machine }
  certificate := adversary.certificate

noncomputable def realDeadlockInitial
    (adversary : PPTAdversary unitCostModel unitNatMeasure toySchema Unit
      ClosedWorldAddress.adversary)
    (environment : PPTEnvironment unitCostModel unitNatMeasure toySchema Unit
      ClosedWorldAddress.environment)
    (sec : CryptoLib.Core.SecPar) :
    Configuration
      (dispatchFamily environment.toEnvironment.machine
        observingProtocol.machine adversary.toAdversary.machine
        observingNetwork.machine)
      CorruptionPolicy.incorruptible sec where
  state := LocalStore.empty
  queue := []
  corrupted := ∅
  output := none
  trace := []
  corruptionInvariant := by
    constructor
    · rfl
    · intro address haddress
      simp at haddress

noncomputable def idealDeadlockInitial
    (simulator : PPTSimulator unitCostModel unitNatMeasure toySchema Unit
      ClosedWorldAddress.adversary)
    (environment : PPTEnvironment unitCostModel unitNatMeasure toySchema Unit
      ClosedWorldAddress.environment)
    (sec : CryptoLib.Core.SecPar) :
    Configuration
      (dispatchFamily environment.toEnvironment.machine
        observingFunctionality.machine simulator.toSimulator.machine
        observingNetwork.machine)
      CorruptionPolicy.incorruptible sec where
  state := LocalStore.empty
  queue := []
  corrupted := ∅
  output := none
  trace := []
  corruptionInvariant := by
    constructor
    · rfl
    · intro address haddress
      simp at haddress

noncomputable def realDeadlockData
    (adversary : PPTAdversary unitCostModel unitNatMeasure toySchema Unit
      ClosedWorldAddress.adversary)
    (environment : PPTEnvironment unitCostModel unitNatMeasure toySchema Unit
      ClosedWorldAddress.environment) :
    RealExecutionData CorruptionPolicy.incorruptible environment
      observingProtocol adversary observingNetwork where
  kernelAlgebra := KernelAlgebra.zero unitCostModel ToyAddress
  initial := realDeadlockInitial adversary environment
  certificate := deadlockPPTCertificate
    (fun sec => observingNetwork.adapter
      (dispatchFamily environment.toEnvironment.machine
        observingProtocol.machine adversary.toAdversary.machine
        observingNetwork.machine) sec)
    (realDeadlockInitial adversary environment) (fun _sec => rfl)
      (fun _sec => rfl)

noncomputable def idealDeadlockData
    (simulator : PPTSimulator unitCostModel unitNatMeasure toySchema Unit
      ClosedWorldAddress.adversary)
    (environment : PPTEnvironment unitCostModel unitNatMeasure toySchema Unit
      ClosedWorldAddress.environment) :
    IdealExecutionData CorruptionPolicy.incorruptible environment
      observingFunctionality simulator observingNetwork where
  kernelAlgebra := KernelAlgebra.zero unitCostModel ToyAddress
  initial := idealDeadlockInitial simulator environment
  certificate := deadlockPPTCertificate
    (fun sec => observingNetwork.adapter
      (dispatchFamily environment.toEnvironment.machine
        observingFunctionality.machine simulator.toSimulator.machine
        observingNetwork.machine) sec)
    (idealDeadlockInitial simulator environment) (fun _sec => rfl)
      (fun _sec => rfl)

noncomputable def structuralExperiment :
    ExecutableExperiment (M := unitCostModel) (measure := unitNatMeasure)
      (worldSchema := toySchema) where
  policy := CorruptionPolicy.incorruptible
  protocol := observingProtocol
  functionality := observingFunctionality
  network := observingNetwork
  realData := realDeadlockData
  idealData := idealDeadlockData

theorem structuralPerfect :
    Experiment.PerfectUCEmulates structuralExperiment.toExperiment := by
  intro adversary
  refine ⟨simulatorOfAdversary adversary, ?_⟩
  intro environment sec
  rfl

abbrev ToyPPTAdversary :=
  PPTAdversary unitCostModel unitNatMeasure toySchema Unit
    ClosedWorldAddress.adversary

abbrev ToyPPTSimulator :=
  PPTSimulator unitCostModel unitNatMeasure toySchema Unit
    ClosedWorldAddress.adversary

abbrev ToyPPTEnvironment :=
  PPTEnvironment unitCostModel unitNatMeasure toySchema Unit
    ClosedWorldAddress.environment

example (adversary : ToyPPTAdversary) (environment : ToyPPTEnvironment) :
    (structuralExperiment.realData adversary environment).certified.world.policy =
      structuralExperiment.policy :=
  (structuralExperiment.realData adversary environment).bound.policy_eq

example (simulator : ToyPPTSimulator) (environment : ToyPPTEnvironment) :
    (structuralExperiment.idealData simulator environment).certified.world.policy =
      structuralExperiment.policy :=
  (structuralExperiment.idealData simulator environment).bound.policy_eq

example (adversary : ToyPPTAdversary) (simulator : ToyPPTSimulator)
    (environment : ToyPPTEnvironment) :
    (structuralExperiment.toExperiment.certifiedPair adversary simulator
          environment).real.world.policy =
      (structuralExperiment.toExperiment.certifiedPair adversary simulator
          environment).ideal.world.policy :=
  (structuralExperiment.toExperiment.certifiedPair adversary simulator
    environment).policy_eq

noncomputable def structuralBuilder : ContextBuilder structuralExperiment :=
  ContextBuilder.identity structuralExperiment

example :
    structuralBuilder.hole.fill structuralExperiment.protocol.machine =
      structuralExperiment.protocol.machine := rfl

example : structuralBuilder.build = structuralExperiment :=
  ContextBuilder.build_identity structuralExperiment

example : structuralBuilder.build.policy =
    structuralBuilder.plugPolicy structuralExperiment.policy := rfl

noncomputable def structuralSecondBuilder :
    ContextBuilder structuralBuilder.build :=
  ContextBuilder.identity structuralBuilder.build

noncomputable def structuralComposedBuilder :
    ContextBuilder structuralExperiment :=
  structuralBuilder.comp structuralSecondBuilder

example : structuralComposedBuilder.build = structuralSecondBuilder.build :=
  ContextBuilder.build_comp structuralBuilder structuralSecondBuilder

noncomputable def structuralContext : Context structuralExperiment :=
  Context.identity structuralExperiment

noncomputable def structuralSecondContext : Context structuralContext.outer :=
  Context.identity structuralContext.outer

noncomputable def structuralThirdContext :
    Context structuralSecondContext.outer :=
  Context.identity structuralSecondContext.outer

example : structuralContext.plug = structuralExperiment.toExperiment :=
  Context.plug_identity structuralExperiment

example :
    (structuralContext.compose structuralSecondContext).plug =
      structuralSecondContext.plug :=
  Context.plug_compose structuralContext structuralSecondContext

example :
    ((structuralContext.compose structuralSecondContext).compose
        structuralThirdContext).plug =
      (structuralContext.compose
        (structuralSecondContext.compose structuralThirdContext)).plug :=
  Context.plug_assoc structuralContext structuralSecondContext
    structuralThirdContext

example :
    ((structuralContext.compose structuralSecondContext).compose
        structuralThirdContext).addressRenaming =
      (structuralContext.compose
        (structuralSecondContext.compose structuralThirdContext)).addressRenaming :=
  Context.compose_addressRenaming_assoc structuralContext structuralSecondContext
    structuralThirdContext

example (adversary : ToyPPTAdversary) (simulator : ToyPPTSimulator)
    (environment : ToyPPTEnvironment) :
    Experiment.realExecution structuralContext.plug adversary
        (structuralContext.plugSimulator simulator) environment =
      Experiment.realExecution structuralExperiment.toExperiment
        (structuralContext.contextAdversary adversary) simulator
          (structuralContext.contextEnvironment environment) :=
  structuralContext.real_operational adversary simulator environment

example (adversary : ToyPPTAdversary) (simulator : ToyPPTSimulator)
    (environment : ToyPPTEnvironment) :
    Experiment.idealExecution structuralContext.plug adversary
        (structuralContext.plugSimulator simulator) environment =
      Experiment.idealExecution structuralExperiment.toExperiment
        (structuralContext.contextAdversary adversary) simulator
          (structuralContext.contextEnvironment environment) :=
  structuralContext.ideal_operational adversary simulator environment

theorem structuralUC : Experiment.UCEmulates structuralContext.plug :=
  Context.uc_compose structuralContext structuralPerfect.ucEmulates

end CryptoLib.Test.Infrastructure.UC.Context

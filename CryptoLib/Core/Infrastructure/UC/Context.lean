import CryptoLib.Core.Infrastructure.UC.Security

namespace CryptoLib.Core.Infrastructure.UC

open CryptoLib.Core.Infrastructure.Computation.Cost

universe uCost uAddress uPayload uPort uCapability
universe uState uLeakage uErasure uOutput

/-- An injective renaming of machine addresses. -/
structure AddressRenaming (Source Target : Type uAddress) where
  toFun : Source → Target
  injective : Function.Injective toFun

namespace AddressRenaming

variable {Source Target : Type uAddress}
variable {First Middle Last : Type uAddress}

instance :
    CoeFun (AddressRenaming Source Target) (fun _ => Source → Target) where
  coe := fun addressMap => addressMap.toFun

def identity (Address : Type uAddress) : AddressRenaming Address Address where
  toFun := id
  injective := Function.injective_id

def comp (first : AddressRenaming First Middle)
    (second : AddressRenaming Middle Last) : AddressRenaming First Last where
  toFun := second.toFun ∘ first.toFun
  injective := second.injective.comp first.injective

@[ext] theorem ext {left right : AddressRenaming Source Target}
    (functions : left.toFun = right.toFun) : left = right := by
  cases left
  cases right
  simp_all

@[simp] theorem identity_apply {Address : Type uAddress} (address : Address) :
    identity Address address = address := rfl

@[simp] theorem comp_apply (first : AddressRenaming First Middle)
    (second : AddressRenaming Middle Last) (address : First) :
    first.comp second address = second (first address) := rfl

theorem comp_identity (addressMap : AddressRenaming Source Target) :
    addressMap.comp (identity Target) = addressMap := by
  ext address
  rfl

theorem identity_comp (addressMap : AddressRenaming Source Target) :
    (identity Source).comp addressMap = addressMap := by
  ext address
  rfl

theorem comp_assoc {First Second Third Fourth : Type uAddress}
    (first : AddressRenaming First Second)
    (second : AddressRenaming Second Third)
    (third : AddressRenaming Third Fourth) :
    (first.comp second).comp third = first.comp (second.comp third) := by
  ext address
  rfl

end AddressRenaming

/--
A role-preserving renaming of a closed UC address space.

Each owner is renamed only inside its own local address type.  The induced
global map therefore cannot alias environment, system, adversary, or network
cells, and its injectivity follows from the four local injectivity proofs.
-/
structure WorldRenaming
    (EnvironmentAddress SystemAddress AdversarialAddress NetworkAddress :
      Type uAddress) where
  environment : AddressRenaming EnvironmentAddress EnvironmentAddress
  system : AddressRenaming SystemAddress SystemAddress
  adversary : AddressRenaming AdversarialAddress AdversarialAddress
  network : AddressRenaming NetworkAddress NetworkAddress

namespace WorldRenaming

variable {EnvironmentAddress SystemAddress AdversarialAddress NetworkAddress :
  Type uAddress}

def toFun
    (addressRenaming : WorldRenaming EnvironmentAddress SystemAddress
      AdversarialAddress NetworkAddress) :
    WorldAddress EnvironmentAddress SystemAddress AdversarialAddress
        NetworkAddress →
      WorldAddress EnvironmentAddress SystemAddress AdversarialAddress
        NetworkAddress
  | .environment address => .environment (addressRenaming.environment address)
  | .system address => .system (addressRenaming.system address)
  | .adversary address => .adversary (addressRenaming.adversary address)
  | .network address => .network (addressRenaming.network address)

theorem toFun_injective
    (addressRenaming : WorldRenaming EnvironmentAddress SystemAddress
      AdversarialAddress NetworkAddress) :
    Function.Injective addressRenaming.toFun := by
  intro left right equality
  cases left with
  | environment leftAddress =>
      cases right with
      | environment rightAddress =>
          apply congrArg ClosedWorldAddress.environment
          apply addressRenaming.environment.injective
          exact ClosedWorldAddress.environment.inj equality
      | system _ | adversary _ | network _ => cases equality
  | system leftAddress =>
      cases right with
      | environment _ | adversary _ | network _ => cases equality
      | system rightAddress =>
          apply congrArg ClosedWorldAddress.system
          apply addressRenaming.system.injective
          exact ClosedWorldAddress.system.inj equality
  | adversary leftAddress =>
      cases right with
      | environment _ | system _ | network _ => cases equality
      | adversary rightAddress =>
          apply congrArg ClosedWorldAddress.adversary
          apply addressRenaming.adversary.injective
          exact ClosedWorldAddress.adversary.inj equality
  | network leftAddress =>
      cases right with
      | environment _ | system _ | adversary _ => cases equality
      | network rightAddress =>
          apply congrArg ClosedWorldAddress.network
          apply addressRenaming.network.injective
          exact ClosedWorldAddress.network.inj equality

def global
    (addressRenaming : WorldRenaming EnvironmentAddress SystemAddress
      AdversarialAddress NetworkAddress) :
    AddressRenaming
      (WorldAddress EnvironmentAddress SystemAddress AdversarialAddress
        NetworkAddress)
      (WorldAddress EnvironmentAddress SystemAddress AdversarialAddress
        NetworkAddress) where
  toFun := addressRenaming.toFun
  injective := addressRenaming.toFun_injective

def identity
    (EnvironmentAddress SystemAddress AdversarialAddress NetworkAddress :
      Type uAddress) :
    WorldRenaming EnvironmentAddress SystemAddress AdversarialAddress
      NetworkAddress where
  environment := AddressRenaming.identity _
  system := AddressRenaming.identity _
  adversary := AddressRenaming.identity _
  network := AddressRenaming.identity _

theorem identity_global
    (EnvironmentAddress SystemAddress AdversarialAddress NetworkAddress :
      Type uAddress) :
    (identity EnvironmentAddress SystemAddress AdversarialAddress
      NetworkAddress).global =
      AddressRenaming.identity
        (WorldAddress EnvironmentAddress SystemAddress AdversarialAddress
          NetworkAddress) := by
  ext address
  cases address <;> rfl

def comp
    (outerToMiddle middleToInner :
      WorldRenaming EnvironmentAddress SystemAddress AdversarialAddress
        NetworkAddress) :
    WorldRenaming EnvironmentAddress SystemAddress AdversarialAddress
      NetworkAddress where
  environment := outerToMiddle.environment.comp middleToInner.environment
  system := outerToMiddle.system.comp middleToInner.system
  adversary := outerToMiddle.adversary.comp middleToInner.adversary
  network := outerToMiddle.network.comp middleToInner.network

@[ext] theorem ext
    {left right : WorldRenaming EnvironmentAddress SystemAddress
      AdversarialAddress NetworkAddress}
    (environment : left.environment = right.environment)
    (system : left.system = right.system)
    (adversary : left.adversary = right.adversary)
    (network : left.network = right.network) : left = right := by
  cases left
  cases right
  simp_all

theorem comp_assoc
    (first second third :
      WorldRenaming EnvironmentAddress SystemAddress AdversarialAddress
        NetworkAddress) :
    (first.comp second).comp third = first.comp (second.comp third) := by
  apply WorldRenaming.ext <;> apply AddressRenaming.comp_assoc

@[simp] theorem global_apply_environment
    (addressRenaming : WorldRenaming EnvironmentAddress SystemAddress
      AdversarialAddress NetworkAddress) (address : EnvironmentAddress) :
    addressRenaming.global (.environment address) =
      .environment (addressRenaming.environment address) := rfl

@[simp] theorem global_apply_system
    (addressRenaming : WorldRenaming EnvironmentAddress SystemAddress
      AdversarialAddress NetworkAddress) (address : SystemAddress) :
    addressRenaming.global (.system address) =
      .system (addressRenaming.system address) := rfl

@[simp] theorem global_apply_adversary
    (addressRenaming : WorldRenaming EnvironmentAddress SystemAddress
      AdversarialAddress NetworkAddress) (address : AdversarialAddress) :
    addressRenaming.global (.adversary address) =
      .adversary (addressRenaming.adversary address) := rfl

@[simp] theorem global_apply_network
    (addressRenaming : WorldRenaming EnvironmentAddress SystemAddress
      AdversarialAddress NetworkAddress) (address : NetworkAddress) :
    addressRenaming.global (.network address) =
      .network (addressRenaming.network address) := rfl

theorem global_comp
    (outerToMiddle middleToInner :
      WorldRenaming EnvironmentAddress SystemAddress AdversarialAddress
        NetworkAddress) :
    (outerToMiddle.comp middleToInner).global =
      outerToMiddle.global.comp middleToInner.global := by
  ext address
  cases address <;> rfl

end WorldRenaming

/--
Typed transport for the result-indexed port schema along an address renaming.

The transport explicitly maps both incoming activations and outgoing
emissions.  Its laws state that endpoints follow the address map and that
routing authority is preserved, so a context cannot silently change a direct
connection into an adversarial one while claiming to be a renaming.
-/
structure PortTransport
    {Address : Type uAddress}
    (schema : PortSchema.{uAddress, uPayload, uPort, uCapability} Address)
    (addressMap : AddressRenaming Address Address) where
  mapActivation : QueuedActivation schema → QueuedActivation schema
  activation_target : ∀ activation,
    (mapActivation activation).target = addressMap activation.target
  mapEmission : ∀ {source : Address},
    Emission schema source → Emission schema (addressMap source)
  emission_target : ∀ {source : Address} (emission : Emission schema source),
    (mapEmission emission).target.address = addressMap emission.target.address
  routing_preserved : ∀ {source : Address} (emission : Emission schema source),
    (mapEmission emission).routingPolicy = emission.routingPolicy
  mapSendAs : ∀ {controller claimedSource : Address},
    schema.CanSendAs controller claimedSource →
      schema.CanSendAs (addressMap controller) (addressMap claimedSource)

namespace PortTransport

variable {Address : Type uAddress}

def identity
    (schema : PortSchema.{uAddress, uPayload, uPort, uCapability} Address) :
    PortTransport schema (AddressRenaming.identity Address) where
  mapActivation := id
  activation_target := by intro activation; rfl
  mapEmission := fun emission => emission
  emission_target := by intro source emission; rfl
  routing_preserved := by intro source emission; rfl
  mapSendAs := fun authorization => authorization

variable {schema : PortSchema.{uAddress, uPayload, uPort, uCapability} Address}

def comp
    {outerToMiddle middleToInner : AddressRenaming Address Address}
    (outer : PortTransport schema outerToMiddle)
    (inner : PortTransport schema middleToInner) :
    PortTransport schema (outerToMiddle.comp middleToInner) where
  mapActivation := inner.mapActivation ∘ outer.mapActivation
  activation_target := by
    intro activation
    rw [Function.comp_apply, inner.activation_target, outer.activation_target]
    rfl
  mapEmission := fun emission => inner.mapEmission (outer.mapEmission emission)
  emission_target := by
    intro source emission
    rw [inner.emission_target, outer.emission_target]
    rfl
  routing_preserved := by
    intro source emission
    calc
      (inner.mapEmission (outer.mapEmission emission)).routingPolicy =
          (outer.mapEmission emission).routingPolicy :=
        inner.routing_preserved (outer.mapEmission emission)
      _ = emission.routingPolicy := outer.routing_preserved emission
  mapSendAs := fun authorization =>
    inner.mapSendAs (outer.mapSendAs authorization)

end PortTransport

variable {M : CostModel.{uCost}} {measure : NatMeasure M}
variable {Address : Type uAddress} [DecidableEq Address]
variable {schema : PortSchema.{uAddress, uPayload, uPort, uCapability} Address}
variable
  {outerFamily innerFamily : ITMFamily.{uCost, uAddress, uPayload, uPort,
    uCapability, uState, uLeakage, uErasure, uOutput} M Address schema}
variable {outerPolicy innerPolicy : CorruptionPolicy Address}

namespace KernelSimulation

def mapQueuedEvent
    (addressMap : AddressRenaming Address Address)
    (ports : PortTransport schema addressMap) :
    QueuedEvent schema → QueuedEvent schema
  | .activation activation => .activation (ports.mapActivation activation)
  | .corruptionRequest source target =>
      .corruptionRequest (addressMap source) (addressMap target)

/--
Transport an audit event without changing its event kind.

Every payload is mapped by the same structural transports used by the kernel
simulation itself.  In particular, contexts cannot postulate an unrelated
trace map that turns (for example) an erasure into an output.  For a spawn we
transport the target-indexed input as a queued activation and then unpack it;
this avoids any equality cast along `activation_target`.
-/
def mapTraceEvent
    (addressMap : AddressRenaming Address Address)
    (ports : PortTransport schema addressMap)
    (mapLeakage : ∀ sec address,
      outerFamily.Leakage sec address →
        innerFamily.Leakage sec (addressMap address))
    (mapErasure : ∀ sec address,
      outerFamily.Erasure sec address →
        innerFamily.Erasure sec (addressMap address))
    (mapOutput : ∀ sec,
      MachineOutput outerFamily sec → MachineOutput innerFamily sec) :
    ∀ sec, TraceEvent outerFamily sec → TraceEvent innerFamily sec
  | _sec, .activated activation =>
      .activated (ports.mapActivation activation)
  | _sec, .yielded source =>
      .yielded (addressMap source)
  | _sec, .emitted emission =>
      .emitted (ports.mapEmission emission)
  | sec, .erased source request =>
      .erased (addressMap source) (mapErasure sec source request)
  | _sec, .spawned source target initial =>
      let mapped := ports.mapActivation (.ofInput target initial)
      .spawned (addressMap source) mapped.target mapped.input
  | _sec, .sendAsAuthorized controller claimedSource =>
      .sendAsAuthorized (addressMap controller) (addressMap claimedSource)
  | _sec, .sendAsRejected controller claimedSource =>
      .sendAsRejected (addressMap controller) (addressMap claimedSource)
  | _sec, .corruptionRequested source target =>
      .corruptionRequested (addressMap source) (addressMap target)
  | sec, .corrupted target leakage =>
      .corrupted (addressMap target) (mapLeakage sec target leakage)
  | sec, .output result =>
      .output (mapOutput sec result)

end KernelSimulation

/--
A one-step simulation between two concrete typed kernel executions.

No whole-run or final-game equality is stored.  The central premise is the
commuting `Kernel.stepOne` square after cost erasure.  Queue, corruption set,
output, and initial-configuration laws expose how the configuration map uses
the address and port transports.
-/
structure KernelSimulation
    (addressMap : AddressRenaming Address Address)
    (outerAlgebra : KernelAlgebra M Address)
    (outerNetwork : (sec : CryptoLib.Core.SecPar) → NetworkAdapter outerFamily sec)
    (outerInitial : (sec : CryptoLib.Core.SecPar) →
      Configuration outerFamily outerPolicy sec)
    (outerDecide : ∀ sec, MachineOutput outerFamily sec → Bool)
    (innerAlgebra : KernelAlgebra M Address)
    (innerNetwork : (sec : CryptoLib.Core.SecPar) → NetworkAdapter innerFamily sec)
    (innerInitial : (sec : CryptoLib.Core.SecPar) →
      Configuration innerFamily innerPolicy sec)
    (innerDecide : ∀ sec, MachineOutput innerFamily sec → Bool) where
  ports : PortTransport schema addressMap
  mapState : ∀ sec address,
    outerFamily.State sec address → innerFamily.State sec (addressMap address)
  mapLeakage : ∀ sec address,
    outerFamily.Leakage sec address → innerFamily.Leakage sec (addressMap address)
  mapErasure : ∀ sec address,
    outerFamily.Erasure sec address → innerFamily.Erasure sec (addressMap address)
  mapOutput : ∀ sec, MachineOutput outerFamily sec → MachineOutput innerFamily sec
  output_source_commutes : ∀ sec output,
    (mapOutput sec output).source = addressMap output.source
  mapConfiguration : ∀ sec,
    Configuration outerFamily outerPolicy sec →
      Configuration innerFamily innerPolicy sec
  queue_commutes : ∀ sec configuration,
    (mapConfiguration sec configuration).queue =
      configuration.queue.map
        (KernelSimulation.mapQueuedEvent addressMap ports)
  corrupted_commutes : ∀ sec configuration,
    (mapConfiguration sec configuration).corrupted =
      configuration.corrupted.image addressMap
  state_commutes : ∀ sec configuration address,
    (mapConfiguration sec configuration).get (addressMap address) =
      (configuration.get address).map (mapState sec address)
  output_commutes : ∀ sec configuration,
    (mapConfiguration sec configuration).output =
      configuration.output.map (mapOutput sec)
  trace_commutes : ∀ sec configuration,
    (mapConfiguration sec configuration).trace =
      configuration.trace.map
        (KernelSimulation.mapTraceEvent addressMap ports mapLeakage mapErasure
          mapOutput sec)
  initial_commutes : ∀ sec,
    mapConfiguration sec (outerInitial sec) = innerInitial sec
  decide_commutes : ∀ sec output,
    innerDecide sec (mapOutput sec output) = outerDecide sec output
  policy_commutes : ∀ sec configuration address,
    innerPolicy.mayCorrupt
        (mapConfiguration sec configuration).corrupted (addressMap address) ↔
      outerPolicy.mayCorrupt configuration.corrupted address
  network_observe_commutes : ∀ sec {source : Address}
      (emission : Emission schema source),
    ports.mapActivation ((outerNetwork sec).observe emission) =
      (innerNetwork sec).observe (ports.mapEmission emission)
  network_control_commutes : ∀ sec activation,
    ports.mapActivation ((outerNetwork sec).control activation) =
      (innerNetwork sec).control (ports.mapActivation activation)
  network_leakage_commutes : ∀ sec address leakage,
    ports.mapActivation ((outerNetwork sec).leakage address leakage) =
      (innerNetwork sec).leakage (addressMap address)
        (mapLeakage sec address leakage)
  step_commutes : ∀ sec configuration,
    PMF.map
        (fun step =>
          match step with
          | .progressed updated =>
              KernelStepResult.progressed (mapConfiguration sec updated)
          | .halted updated =>
              KernelStepResult.halted (mapConfiguration sec updated)
          | .deadlock updated =>
              KernelStepResult.deadlock (mapConfiguration sec updated))
        (RandCosted.valueDist
          (Kernel.stepOne outerAlgebra (outerNetwork sec) configuration)) =
      RandCosted.valueDist
        (Kernel.stepOne innerAlgebra (innerNetwork sec)
          (mapConfiguration sec configuration))

namespace KernelSimulation

variable
  {addressMap : AddressRenaming Address Address}
  {outerAlgebra innerAlgebra : KernelAlgebra M Address}
  {outerNetwork : (sec : CryptoLib.Core.SecPar) → NetworkAdapter outerFamily sec}
  {innerNetwork : (sec : CryptoLib.Core.SecPar) → NetworkAdapter innerFamily sec}
  {outerInitial : (sec : CryptoLib.Core.SecPar) →
    Configuration outerFamily outerPolicy sec}
  {innerInitial : (sec : CryptoLib.Core.SecPar) →
    Configuration innerFamily innerPolicy sec}
  {outerDecide : ∀ sec, MachineOutput outerFamily sec → Bool}
  {innerDecide : ∀ sec, MachineOutput innerFamily sec → Bool}

def mapStepResult
    (simulation : KernelSimulation addressMap outerAlgebra outerNetwork
      outerInitial outerDecide innerAlgebra innerNetwork innerInitial innerDecide)
    (sec : CryptoLib.Core.SecPar) :
    KernelStepResult outerFamily outerPolicy sec →
      KernelStepResult innerFamily innerPolicy sec
  | .progressed updated => .progressed (simulation.mapConfiguration sec updated)
  | .halted updated => .halted (simulation.mapConfiguration sec updated)
  | .deadlock updated => .deadlock (simulation.mapConfiguration sec updated)

def mapOutcome
    (simulation : KernelSimulation addressMap outerAlgebra outerNetwork
      outerInitial outerDecide innerAlgebra innerNetwork innerInitial innerDecide)
    (sec : CryptoLib.Core.SecPar) :
    Kernel.ExecutionOutcome outerFamily sec →
      Kernel.ExecutionOutcome innerFamily sec
  | .output output => .output (simulation.mapOutput sec output)
  | .timeout => .timeout
  | .deadlock => .deadlock

def mapExecutionResult
    (simulation : KernelSimulation addressMap outerAlgebra outerNetwork
      outerInitial outerDecide innerAlgebra innerNetwork innerInitial innerDecide)
    (sec : CryptoLib.Core.SecPar) :
    Kernel.ExecutionResult outerFamily outerPolicy sec →
      Kernel.ExecutionResult innerFamily innerPolicy sec
  | ⟨outcome, configuration⟩ =>
      ⟨simulation.mapOutcome sec outcome,
        simulation.mapConfiguration sec configuration⟩

theorem map_atFuelZero
    (simulation : KernelSimulation addressMap outerAlgebra outerNetwork
      outerInitial outerDecide innerAlgebra innerNetwork innerInitial innerDecide)
    (sec : CryptoLib.Core.SecPar)
    (configuration : Configuration outerFamily outerPolicy sec) :
    simulation.mapExecutionResult sec (Kernel.atFuelZero configuration) =
      Kernel.atFuelZero (simulation.mapConfiguration sec configuration) := by
  cases houtput : configuration.output with
  | none =>
      have mappedOutput :
          (simulation.mapConfiguration sec configuration).output = none := by
        rw [simulation.output_commutes, houtput]
        rfl
      simp [Kernel.atFuelZero, houtput, mappedOutput, mapExecutionResult, mapOutcome]
  | some output =>
      have mappedOutput :
          (simulation.mapConfiguration sec configuration).output =
            some (simulation.mapOutput sec output) := by
        rw [simulation.output_commutes, houtput]
        rfl
      simp [Kernel.atFuelZero, houtput, mappedOutput, mapExecutionResult, mapOutcome]

/--
The one-step commuting square extends by induction to every finite fuel.
-/
theorem runCosted_commutes
    (simulation : KernelSimulation addressMap outerAlgebra outerNetwork
      outerInitial outerDecide innerAlgebra innerNetwork innerInitial innerDecide) :
    ∀ (fuel : Nat) (sec : CryptoLib.Core.SecPar)
      (configuration : Configuration outerFamily outerPolicy sec),
      PMF.map (simulation.mapExecutionResult sec)
          (RandCosted.valueDist
            (Kernel.runCosted outerAlgebra (outerNetwork sec) fuel configuration)) =
        RandCosted.valueDist
          (Kernel.runCosted innerAlgebra (innerNetwork sec) fuel
            (simulation.mapConfiguration sec configuration)) := by
  intro fuel
  induction fuel with
  | zero =>
      intro sec configuration
      simp only [Kernel.runCosted]
      change
        PMF.map (simulation.mapExecutionResult sec)
            (RandCosted.valueDist
              (RandCosted.pure M (Kernel.atFuelZero configuration))) =
          RandCosted.valueDist
            (RandCosted.pure M
              (Kernel.atFuelZero
                (simulation.mapConfiguration sec configuration)))
      rw [RandCosted.valueDist_pure, RandCosted.valueDist_pure,
        PMF.pure_map]
      exact congrArg PMF.pure (simulation.map_atFuelZero sec configuration)
  | succ fuel inductionHypothesis =>
      intro sec configuration
      cases houtput : configuration.output with
      | some output =>
          have mappedOutput :
              (simulation.mapConfiguration sec configuration).output =
                some (simulation.mapOutput sec output) := by
            rw [simulation.output_commutes, houtput]
            rfl
          simp only [Kernel.runCosted, houtput, mappedOutput]
          change
            PMF.map (simulation.mapExecutionResult sec)
                (RandCosted.valueDist
                  (RandCosted.pure M
                    ({ outcome := Kernel.ExecutionOutcome.output output
                       configuration := configuration } :
                      Kernel.ExecutionResult outerFamily outerPolicy sec))) =
              RandCosted.valueDist
                (RandCosted.pure M
                  ({ outcome := Kernel.ExecutionOutcome.output
                        (simulation.mapOutput sec output)
                     configuration := simulation.mapConfiguration sec configuration } :
                    Kernel.ExecutionResult innerFamily innerPolicy sec))
          rw [RandCosted.valueDist_pure, RandCosted.valueDist_pure,
            PMF.pure_map]
          rfl
      | none =>
          have mappedOutput :
              (simulation.mapConfiguration sec configuration).output = none := by
            rw [simulation.output_commutes, houtput]
            rfl
          simp only [Kernel.runCosted, houtput, mappedOutput]
          change
            PMF.map (simulation.mapExecutionResult sec)
                (RandCosted.valueDist
                  (RandCosted.bind
                    (Kernel.stepOne outerAlgebra (outerNetwork sec) configuration)
                    (fun step =>
                      match step with
                      | .progressed updated =>
                          Kernel.runCosted outerAlgebra (outerNetwork sec)
                            fuel updated
                      | .halted updated =>
                          match updated.output with
                          | some result => RandCosted.pure M
                              ({ outcome := Kernel.ExecutionOutcome.output result
                                 configuration := updated } :
                                Kernel.ExecutionResult outerFamily outerPolicy sec)
                          | none => RandCosted.pure M
                              ({ outcome := Kernel.ExecutionOutcome.deadlock
                                 configuration := updated } :
                                Kernel.ExecutionResult outerFamily outerPolicy sec)
                      | .deadlock updated => RandCosted.pure M
                          ({ outcome := Kernel.ExecutionOutcome.deadlock
                             configuration := updated } :
                            Kernel.ExecutionResult outerFamily outerPolicy sec)))) =
              RandCosted.valueDist
                (RandCosted.bind
                  (Kernel.stepOne innerAlgebra (innerNetwork sec)
                    (simulation.mapConfiguration sec configuration))
                  (fun step =>
                    match step with
                    | .progressed updated =>
                        Kernel.runCosted innerAlgebra (innerNetwork sec)
                          fuel updated
                    | .halted updated =>
                        match updated.output with
                        | some result => RandCosted.pure M
                            ({ outcome := Kernel.ExecutionOutcome.output result
                               configuration := updated } :
                              Kernel.ExecutionResult innerFamily innerPolicy sec)
                        | none => RandCosted.pure M
                            ({ outcome := Kernel.ExecutionOutcome.deadlock
                               configuration := updated } :
                              Kernel.ExecutionResult innerFamily innerPolicy sec)
                    | .deadlock updated => RandCosted.pure M
                        ({ outcome := Kernel.ExecutionOutcome.deadlock
                           configuration := updated } :
                          Kernel.ExecutionResult innerFamily innerPolicy sec)))
          rw [RandCosted.valueDist_bind, RandCosted.valueDist_bind,
            PMF.map_bind]
          let outerStep := RandCosted.valueDist
            (Kernel.stepOne outerAlgebra (outerNetwork sec) configuration)
          let innerStep := RandCosted.valueDist
            (Kernel.stepOne innerAlgebra (innerNetwork sec)
              (simulation.mapConfiguration sec configuration))
          let outerContinuation := fun step :
              KernelStepResult outerFamily outerPolicy sec =>
            RandCosted.valueDist <|
              match step with
              | .progressed updated =>
                  (Kernel.runCosted outerAlgebra (outerNetwork sec) fuel updated)
              | .halted updated =>
                  match updated.output with
                  | some result => RandCosted.pure M
                      ({ outcome := Kernel.ExecutionOutcome.output result
                         configuration := updated } :
                        Kernel.ExecutionResult outerFamily outerPolicy sec)
                  | none => RandCosted.pure M
                      ({ outcome := Kernel.ExecutionOutcome.deadlock
                         configuration := updated } :
                        Kernel.ExecutionResult outerFamily outerPolicy sec)
              | .deadlock updated => RandCosted.pure M
                  ({ outcome := Kernel.ExecutionOutcome.deadlock
                     configuration := updated } :
                    Kernel.ExecutionResult outerFamily outerPolicy sec)
          let innerContinuation := fun step :
              KernelStepResult innerFamily innerPolicy sec =>
            RandCosted.valueDist <|
              match step with
              | .progressed updated =>
                  (Kernel.runCosted innerAlgebra (innerNetwork sec) fuel updated)
              | .halted updated =>
                  match updated.output with
                  | some result => RandCosted.pure M
                      ({ outcome := Kernel.ExecutionOutcome.output result
                         configuration := updated } :
                        Kernel.ExecutionResult innerFamily innerPolicy sec)
                  | none => RandCosted.pure M
                      ({ outcome := Kernel.ExecutionOutcome.deadlock
                         configuration := updated } :
                        Kernel.ExecutionResult innerFamily innerPolicy sec)
              | .deadlock updated => RandCosted.pure M
                  ({ outcome := Kernel.ExecutionOutcome.deadlock
                     configuration := updated } :
                    Kernel.ExecutionResult innerFamily innerPolicy sec)
          have continuationCommutes : ∀ step,
              PMF.map (simulation.mapExecutionResult sec)
                  (outerContinuation step) =
                innerContinuation (simulation.mapStepResult sec step) := by
            intro step
            cases step with
            | progressed updated =>
                exact inductionHypothesis sec updated
            | deadlock updated =>
                dsimp [outerContinuation, innerContinuation, mapStepResult]
                rw [RandCosted.valueDist_pure, RandCosted.valueDist_pure,
                  PMF.pure_map]
                rfl
            | halted updated =>
                cases hresult : updated.output with
                | none =>
                    have mappedResult :
                        (simulation.mapConfiguration sec updated).output = none := by
                      rw [simulation.output_commutes, hresult]
                      rfl
                    simp [outerContinuation, innerContinuation, mapStepResult,
                      hresult, mappedResult, PMF.pure_map,
                      mapExecutionResult, mapOutcome]
                | some result =>
                    have mappedResult :
                        (simulation.mapConfiguration sec updated).output =
                          some (simulation.mapOutput sec result) := by
                      rw [simulation.output_commutes, hresult]
                      rfl
                    simp [outerContinuation, innerContinuation, mapStepResult,
                      hresult, mappedResult, PMF.pure_map,
                      mapExecutionResult, mapOutcome]
          have bindEquality :
              PMF.bind outerStep
                  (fun step => PMF.map (simulation.mapExecutionResult sec)
                    (outerContinuation step)) =
                PMF.bind innerStep innerContinuation := by
            rw [show (fun step => PMF.map (simulation.mapExecutionResult sec)
                  (outerContinuation step)) =
                (fun step => innerContinuation (simulation.mapStepResult sec step))
              from funext continuationCommutes]
            change
              PMF.bind outerStep
                  (innerContinuation ∘ simulation.mapStepResult sec) =
                PMF.bind innerStep innerContinuation
            rw [← PMF.bind_map]
            have stepEquality :
                PMF.map (simulation.mapStepResult sec) outerStep = innerStep := by
              exact simulation.step_commutes sec configuration
            rw [stepEquality]
          simpa only [outerStep, innerStep, outerContinuation,
            innerContinuation] using bindEquality

/-- The finite-run simulation preserves the Boolean decision distribution. -/
theorem decisionDist_commutes
    (simulation : KernelSimulation addressMap outerAlgebra outerNetwork
      outerInitial outerDecide innerAlgebra innerNetwork innerInitial innerDecide)
    (fuel : Nat) (sec : CryptoLib.Core.SecPar)
    (configuration : Configuration outerFamily outerPolicy sec) :
    Kernel.decisionDist outerAlgebra (outerNetwork sec) (outerDecide sec)
        fuel configuration =
      Kernel.decisionDist innerAlgebra (innerNetwork sec) (innerDecide sec)
        fuel (simulation.mapConfiguration sec configuration) := by
  change
    PMF.map
        (fun result : Kernel.ExecutionResult outerFamily outerPolicy sec =>
          result.outcome.toBool (outerDecide sec))
        (RandCosted.valueDist
          (Kernel.runCosted outerAlgebra (outerNetwork sec) fuel configuration)) =
      PMF.map
        (fun result : Kernel.ExecutionResult innerFamily innerPolicy sec =>
          result.outcome.toBool (innerDecide sec))
        (RandCosted.valueDist
          (Kernel.runCosted innerAlgebra (innerNetwork sec) fuel
            (simulation.mapConfiguration sec configuration)))
  let outerDist := RandCosted.valueDist
    (Kernel.runCosted outerAlgebra (outerNetwork sec) fuel configuration)
  let innerDist := RandCosted.valueDist
    (Kernel.runCosted innerAlgebra (innerNetwork sec) fuel
      (simulation.mapConfiguration sec configuration))
  let outerObservation :=
    fun result : Kernel.ExecutionResult outerFamily outerPolicy sec =>
      result.outcome.toBool (outerDecide sec)
  let innerObservation :=
    fun result : Kernel.ExecutionResult innerFamily innerPolicy sec =>
      result.outcome.toBool (innerDecide sec)
  have observationCommutes :
      outerObservation = innerObservation ∘ simulation.mapExecutionResult sec := by
    funext result
    cases result with
    | mk outcome finalConfiguration =>
        cases outcome with
        | output output =>
            change outerDecide sec output =
              innerDecide sec (simulation.mapOutput sec output)
            exact (simulation.decide_commutes sec output).symm
        | timeout | deadlock => rfl
  change PMF.map outerObservation outerDist = PMF.map innerObservation innerDist
  calc
    PMF.map outerObservation outerDist =
        PMF.map (innerObservation ∘ simulation.mapExecutionResult sec)
          outerDist := by rw [observationCommutes]
    _ = PMF.map innerObservation
          (PMF.map (simulation.mapExecutionResult sec) outerDist) := by
      exact (PMF.map_comp _ _ _).symm
    _ = PMF.map innerObservation innerDist := by
      rw [simulation.runCosted_commutes fuel sec configuration]

/-- The actual initial configurations therefore have identical finite games. -/
theorem initial_decisionDist_commutes
    (simulation : KernelSimulation addressMap outerAlgebra outerNetwork
      outerInitial outerDecide innerAlgebra innerNetwork innerInitial innerDecide)
    (fuel : Nat) (sec : CryptoLib.Core.SecPar) :
    Kernel.decisionDist outerAlgebra (outerNetwork sec) (outerDecide sec)
        fuel (outerInitial sec) =
      Kernel.decisionDist innerAlgebra (innerNetwork sec) (innerDecide sec)
        fuel (innerInitial sec) := by
  rw [← simulation.initial_commutes sec]
  exact simulation.decisionDist_commutes fuel sec (outerInitial sec)

/-- Identity simulation of one concrete typed kernel execution. -/
noncomputable def identity
    {family : ITMFamily.{uCost, uAddress, uPayload, uPort, uCapability,
      uState, uLeakage, uErasure, uOutput} M Address schema}
    {policy : CorruptionPolicy Address}
    (algebra : KernelAlgebra M Address)
    (network : (sec : CryptoLib.Core.SecPar) → NetworkAdapter family sec)
    (initial : (sec : CryptoLib.Core.SecPar) → Configuration family policy sec)
    (decide : ∀ sec, MachineOutput family sec → Bool) :
    KernelSimulation (AddressRenaming.identity Address)
      algebra network initial decide algebra network initial decide where
  ports := PortTransport.identity schema
  mapState := fun _sec _address state => state
  mapLeakage := fun _sec _address leakage => leakage
  mapErasure := fun _sec _address request => request
  mapOutput := fun _sec output => output
  output_source_commutes := by intro sec output; rfl
  mapConfiguration := fun _sec configuration => configuration
  queue_commutes := by
    intro sec configuration
    have eventIdentity :
        KernelSimulation.mapQueuedEvent (AddressRenaming.identity Address)
            (PortTransport.identity schema) = id := by
      funext event
      cases event <;> rfl
    rw [eventIdentity, List.map_id]
  corrupted_commutes := by
    intro sec configuration
    simp [AddressRenaming.identity]
  state_commutes := by
    intro sec configuration address
    simp [AddressRenaming.identity]
  output_commutes := by
    intro sec configuration
    simp
  trace_commutes := by
    intro sec configuration
    induction configuration.trace with
    | nil => rfl
    | cons event trace inductionHypothesis =>
        simp only [List.map_cons]
        congr
        · cases event <;> rfl
  initial_commutes := by
    intro sec
    rfl
  decide_commutes := by
    intro sec output
    rfl
  policy_commutes := by
    intro sec configuration address
    rfl
  network_observe_commutes := by
    intro sec source emission
    rfl
  network_control_commutes := by
    intro sec activation
    rfl
  network_leakage_commutes := by
    intro sec address leakage
    rfl
  step_commutes := by
    intro sec configuration
    have stepIdentity :
        (fun step : KernelStepResult family policy sec =>
          match step with
          | .progressed updated => KernelStepResult.progressed updated
          | .halted updated => KernelStepResult.halted updated
          | .deadlock updated => KernelStepResult.deadlock updated) = id := by
      funext step
      cases step <;> rfl
    rw [stepIdentity, PMF.map_id]

/-- Sequential composition of two one-step kernel simulations. -/
noncomputable def comp
    {middleFamily : ITMFamily.{uCost, uAddress, uPayload, uPort, uCapability,
      uState, uLeakage, uErasure, uOutput} M Address schema}
    {middlePolicy : CorruptionPolicy Address}
    {outerToMiddle middleToInner : AddressRenaming Address Address}
    {middleAlgebra : KernelAlgebra M Address}
    {middleNetwork : (sec : CryptoLib.Core.SecPar) → NetworkAdapter middleFamily sec}
    {middleInitial : (sec : CryptoLib.Core.SecPar) →
      Configuration middleFamily middlePolicy sec}
    {middleDecide : ∀ sec, MachineOutput middleFamily sec → Bool}
    (outer : KernelSimulation outerToMiddle outerAlgebra outerNetwork
      outerInitial outerDecide middleAlgebra middleNetwork middleInitial
      middleDecide)
    (inner : KernelSimulation middleToInner middleAlgebra middleNetwork
      middleInitial middleDecide innerAlgebra innerNetwork innerInitial
      innerDecide) :
    KernelSimulation (outerToMiddle.comp middleToInner)
      outerAlgebra outerNetwork outerInitial outerDecide
      innerAlgebra innerNetwork innerInitial innerDecide where
  ports := outer.ports.comp inner.ports
  mapState := fun sec address state =>
    inner.mapState sec (outerToMiddle address)
      (outer.mapState sec address state)
  mapLeakage := fun sec address leakage =>
    inner.mapLeakage sec (outerToMiddle address)
      (outer.mapLeakage sec address leakage)
  mapErasure := fun sec address request =>
    inner.mapErasure sec (outerToMiddle address)
      (outer.mapErasure sec address request)
  mapOutput := fun sec output => inner.mapOutput sec (outer.mapOutput sec output)
  output_source_commutes := by
    intro sec output
    rw [inner.output_source_commutes, outer.output_source_commutes]
    rfl
  mapConfiguration := fun sec configuration =>
    inner.mapConfiguration sec (outer.mapConfiguration sec configuration)
  queue_commutes := by
    intro sec configuration
    rw [inner.queue_commutes, outer.queue_commutes, List.map_map]
    apply congrArg (List.map · configuration.queue)
    funext event
    cases event <;> rfl
  corrupted_commutes := by
    intro sec configuration
    rw [inner.corrupted_commutes, outer.corrupted_commutes]
    simp only [Finset.image_image]
    rfl
  state_commutes := by
    intro sec configuration address
    change
      (inner.mapConfiguration sec
          (outer.mapConfiguration sec configuration)).get
          (middleToInner (outerToMiddle address)) = _
    rw [inner.state_commutes sec (outer.mapConfiguration sec configuration)
      (outerToMiddle address), outer.state_commutes]
    simp only [Option.map_map]
    rfl
  output_commutes := by
    intro sec configuration
    rw [inner.output_commutes, outer.output_commutes]
    simp only [Option.map_map]
    rfl
  trace_commutes := by
    intro sec configuration
    rw [inner.trace_commutes, outer.trace_commutes, List.map_map]
    apply congrArg (List.map · configuration.trace)
    funext event
    cases event <;> rfl
  initial_commutes := by
    intro sec
    rw [outer.initial_commutes, inner.initial_commutes]
  decide_commutes := by
    intro sec output
    rw [inner.decide_commutes, outer.decide_commutes]
  policy_commutes := by
    intro sec configuration address
    exact (inner.policy_commutes sec (outer.mapConfiguration sec configuration)
      (outerToMiddle address)).trans (outer.policy_commutes sec configuration address)
  network_observe_commutes := by
    intro sec source emission
    change
      inner.ports.mapActivation
          (outer.ports.mapActivation ((outerNetwork sec).observe emission)) =
        (innerNetwork sec).observe
          (inner.ports.mapEmission (outer.ports.mapEmission emission))
    rw [outer.network_observe_commutes]
    exact inner.network_observe_commutes sec (outer.ports.mapEmission emission)
  network_control_commutes := by
    intro sec activation
    change
      inner.ports.mapActivation
          (outer.ports.mapActivation ((outerNetwork sec).control activation)) =
        (innerNetwork sec).control
          (inner.ports.mapActivation (outer.ports.mapActivation activation))
    rw [outer.network_control_commutes]
    exact inner.network_control_commutes sec (outer.ports.mapActivation activation)
  network_leakage_commutes := by
    intro sec address leakage
    change
      inner.ports.mapActivation
          (outer.ports.mapActivation
            ((outerNetwork sec).leakage address leakage)) =
        (innerNetwork sec).leakage (middleToInner (outerToMiddle address))
          (inner.mapLeakage sec (outerToMiddle address)
            (outer.mapLeakage sec address leakage))
    rw [outer.network_leakage_commutes]
    exact inner.network_leakage_commutes sec (outerToMiddle address)
      (outer.mapLeakage sec address leakage)
  step_commutes := by
    intro sec configuration
    let outerDist := RandCosted.valueDist
      (Kernel.stepOne outerAlgebra (outerNetwork sec) configuration)
    let middleDist := RandCosted.valueDist
      (Kernel.stepOne middleAlgebra (middleNetwork sec)
        (outer.mapConfiguration sec configuration))
    let innerDist := RandCosted.valueDist
      (Kernel.stepOne innerAlgebra (innerNetwork sec)
        (inner.mapConfiguration sec
          (outer.mapConfiguration sec configuration)))
    let outerStep := outer.mapStepResult sec
    let innerStep := inner.mapStepResult sec
    change PMF.map
      (fun step =>
        match step with
        | .progressed updated => KernelStepResult.progressed
            (inner.mapConfiguration sec (outer.mapConfiguration sec updated))
        | .halted updated => KernelStepResult.halted
            (inner.mapConfiguration sec (outer.mapConfiguration sec updated))
        | .deadlock updated => KernelStepResult.deadlock
            (inner.mapConfiguration sec (outer.mapConfiguration sec updated)))
      outerDist = innerDist
    have stepComposition :
        (fun step : KernelStepResult outerFamily outerPolicy sec =>
          match step with
          | .progressed updated => KernelStepResult.progressed
              (inner.mapConfiguration sec (outer.mapConfiguration sec updated))
          | .halted updated => KernelStepResult.halted
              (inner.mapConfiguration sec (outer.mapConfiguration sec updated))
          | .deadlock updated => KernelStepResult.deadlock
              (inner.mapConfiguration sec (outer.mapConfiguration sec updated))) =
          innerStep ∘ outerStep := by
      funext step
      cases step <;> rfl
    rw [stepComposition]
    calc
      PMF.map (innerStep ∘ outerStep) outerDist =
          PMF.map innerStep (PMF.map outerStep outerDist) := by
        exact (PMF.map_comp outerStep outerDist innerStep).symm
      _ = PMF.map innerStep middleDist := by
        rw [show PMF.map outerStep outerDist = middleDist from
          outer.step_commutes sec configuration]
      _ = innerDist := inner.step_commutes sec
        (outer.mapConfiguration sec configuration)

end KernelSimulation

section ClosedWorldBuilder

variable {EnvironmentAddress SystemAddress AdversarialAddress NetworkAddress :
  Type uAddress}
variable [DecidableEq EnvironmentAddress] [DecidableEq SystemAddress]
variable [DecidableEq AdversarialAddress] [DecidableEq NetworkAddress]
variable {worldSchema : PortSchema.{uAddress, uPayload, uPort, uCapability}
  (WorldAddress EnvironmentAddress SystemAddress
    AdversarialAddress NetworkAddress)}

/--
All data needed to build one certified real world with `composeReal`.

The structure stores no preassembled `BoundRealExecution`; its world and role
equalities below are derived definitionally from these inputs.
-/
structure RealExecutionData
    (policy : CorruptionPolicy
      (WorldAddress EnvironmentAddress SystemAddress
        AdversarialAddress NetworkAddress))
    (environment : PPTEnvironment.{uCost, uAddress, uPayload, uPort,
      uCapability, uState, uLeakage, uErasure, uOutput}
      M measure worldSchema EnvironmentAddress ClosedWorldAddress.environment)
    (protocol : Protocol.{uCost, uAddress, uPayload, uPort, uCapability,
      uState, uLeakage, uErasure, uOutput}
      M worldSchema SystemAddress ClosedWorldAddress.system)
    (adversary : PPTAdversary.{uCost, uAddress, uPayload, uPort,
      uCapability, uState, uLeakage, uErasure, uOutput}
      M measure worldSchema AdversarialAddress ClosedWorldAddress.adversary)
    (network : Network.{uCost, uAddress, uPayload, uPort, uCapability,
      uState, uLeakage, uErasure, uOutput}
      M worldSchema NetworkAddress ClosedWorldAddress.network) where
  kernelAlgebra : KernelAlgebra M
    (WorldAddress EnvironmentAddress SystemAddress
      AdversarialAddress NetworkAddress)
  initial : ∀ sec, Configuration
    (dispatchFamily environment.toEnvironment.machine protocol.machine
      adversary.toAdversary.machine network.machine) policy sec
  certificate : PPTExecutionCertificate
    (family := dispatchFamily environment.toEnvironment.machine protocol.machine
      adversary.toAdversary.machine network.machine)
    (policy := policy) measure kernelAlgebra
    (fun sec => network.adapter
      (dispatchFamily environment.toEnvironment.machine protocol.machine
        adversary.toAdversary.machine network.machine) sec)
    initial

namespace RealExecutionData

variable
  {policy : CorruptionPolicy
    (WorldAddress EnvironmentAddress SystemAddress
      AdversarialAddress NetworkAddress)}
  {environment : PPTEnvironment.{uCost, uAddress, uPayload, uPort,
    uCapability, uState, uLeakage, uErasure, uOutput}
    M measure worldSchema EnvironmentAddress ClosedWorldAddress.environment}
  {protocol : Protocol.{uCost, uAddress, uPayload, uPort, uCapability,
    uState, uLeakage, uErasure, uOutput}
    M worldSchema SystemAddress ClosedWorldAddress.system}
  {adversary : PPTAdversary.{uCost, uAddress, uPayload, uPort,
    uCapability, uState, uLeakage, uErasure, uOutput}
    M measure worldSchema AdversarialAddress ClosedWorldAddress.adversary}
  {network : Network.{uCost, uAddress, uPayload, uPort, uCapability,
    uState, uLeakage, uErasure, uOutput}
    M worldSchema NetworkAddress ClosedWorldAddress.network}

noncomputable def world
    (data : RealExecutionData policy environment protocol adversary network) :
    RealWorld.{uCost, uAddress, uPayload, uPort, uCapability,
      uState, uLeakage, uErasure, uOutput}
      M EnvironmentAddress SystemAddress AdversarialAddress NetworkAddress
        worldSchema :=
  composeReal environment.toEnvironment protocol adversary.toAdversary network
    policy data.kernelAlgebra data.initial

noncomputable def certified
    (data : RealExecutionData policy environment protocol adversary network) :
    CertifiedRealWorld.{uCost, uAddress, uPayload, uPort, uCapability,
      uState, uLeakage, uErasure, uOutput}
      measure EnvironmentAddress SystemAddress AdversarialAddress NetworkAddress
        worldSchema where
  world := data.world
  certificate := data.certificate

noncomputable def bound
    (data : RealExecutionData policy environment protocol adversary network) :
    BoundRealExecution policy environment protocol adversary network where
  certified := data.certified
  environment_eq := rfl
  policy_eq := rfl
  protocol_eq := rfl
  adversary_eq := rfl
  network_eq := rfl

end RealExecutionData

/-- Structural data from which one certified ideal world is assembled. -/
structure IdealExecutionData
    (policy : CorruptionPolicy
      (WorldAddress EnvironmentAddress SystemAddress
        AdversarialAddress NetworkAddress))
    (environment : PPTEnvironment.{uCost, uAddress, uPayload, uPort,
      uCapability, uState, uLeakage, uErasure, uOutput}
      M measure worldSchema EnvironmentAddress ClosedWorldAddress.environment)
    (functionality : IdealFunctionality.{uCost, uAddress, uPayload, uPort,
      uCapability, uState, uLeakage, uErasure, uOutput}
      M worldSchema SystemAddress ClosedWorldAddress.system)
    (simulator : PPTSimulator.{uCost, uAddress, uPayload, uPort,
      uCapability, uState, uLeakage, uErasure, uOutput}
      M measure worldSchema AdversarialAddress ClosedWorldAddress.adversary)
    (network : Network.{uCost, uAddress, uPayload, uPort, uCapability,
      uState, uLeakage, uErasure, uOutput}
      M worldSchema NetworkAddress ClosedWorldAddress.network) where
  kernelAlgebra : KernelAlgebra M
    (WorldAddress EnvironmentAddress SystemAddress
      AdversarialAddress NetworkAddress)
  initial : ∀ sec, Configuration
    (dispatchFamily environment.toEnvironment.machine functionality.machine
      simulator.toSimulator.machine network.machine) policy sec
  certificate : PPTExecutionCertificate
    (family := dispatchFamily environment.toEnvironment.machine
      functionality.machine simulator.toSimulator.machine network.machine)
    (policy := policy) measure kernelAlgebra
    (fun sec => network.adapter
      (dispatchFamily environment.toEnvironment.machine functionality.machine
        simulator.toSimulator.machine network.machine) sec)
    initial

namespace IdealExecutionData

variable
  {policy : CorruptionPolicy
    (WorldAddress EnvironmentAddress SystemAddress
      AdversarialAddress NetworkAddress)}
  {environment : PPTEnvironment.{uCost, uAddress, uPayload, uPort,
    uCapability, uState, uLeakage, uErasure, uOutput}
    M measure worldSchema EnvironmentAddress ClosedWorldAddress.environment}
  {functionality : IdealFunctionality.{uCost, uAddress, uPayload, uPort,
    uCapability, uState, uLeakage, uErasure, uOutput}
    M worldSchema SystemAddress ClosedWorldAddress.system}
  {simulator : PPTSimulator.{uCost, uAddress, uPayload, uPort,
    uCapability, uState, uLeakage, uErasure, uOutput}
    M measure worldSchema AdversarialAddress ClosedWorldAddress.adversary}
  {network : Network.{uCost, uAddress, uPayload, uPort, uCapability,
    uState, uLeakage, uErasure, uOutput}
    M worldSchema NetworkAddress ClosedWorldAddress.network}

noncomputable def world
    (data : IdealExecutionData policy environment functionality simulator network) :
    IdealWorld.{uCost, uAddress, uPayload, uPort, uCapability,
      uState, uLeakage, uErasure, uOutput}
      M EnvironmentAddress SystemAddress AdversarialAddress NetworkAddress
        worldSchema :=
  composeIdeal environment.toEnvironment functionality simulator.toSimulator
    network policy data.kernelAlgebra data.initial

noncomputable def certified
    (data : IdealExecutionData policy environment functionality simulator network) :
    CertifiedIdealWorld.{uCost, uAddress, uPayload, uPort, uCapability,
      uState, uLeakage, uErasure, uOutput}
      measure EnvironmentAddress SystemAddress AdversarialAddress NetworkAddress
        worldSchema where
  world := data.world
  certificate := data.certificate

noncomputable def bound
    (data : IdealExecutionData policy environment functionality simulator network) :
    BoundIdealExecution policy environment functionality simulator network where
  certified := data.certified
  environment_eq := rfl
  policy_eq := rfl
  functionality_eq := rfl
  simulator_eq := rfl
  network_eq := rfl

end IdealExecutionData

/--
A structurally executable UC experiment.

Only exact world inputs and certificates are stored.  `toExperiment` below
constructs every real and ideal world through `composeReal` and `composeIdeal`.
-/
structure ExecutableExperiment where
  /-- The one corruption policy shared by both assembled executions. -/
  policy : CorruptionPolicy
    (WorldAddress EnvironmentAddress SystemAddress
      AdversarialAddress NetworkAddress)
  protocol : Protocol.{uCost, uAddress, uPayload, uPort, uCapability,
    uState, uLeakage, uErasure, uOutput}
    M worldSchema SystemAddress ClosedWorldAddress.system
  functionality : IdealFunctionality.{uCost, uAddress, uPayload, uPort,
    uCapability, uState, uLeakage, uErasure, uOutput}
    M worldSchema SystemAddress ClosedWorldAddress.system
  network : Network.{uCost, uAddress, uPayload, uPort, uCapability,
    uState, uLeakage, uErasure, uOutput}
    M worldSchema NetworkAddress ClosedWorldAddress.network
  realData : ∀
    (adversary : PPTAdversary.{uCost, uAddress, uPayload, uPort,
      uCapability, uState, uLeakage, uErasure, uOutput}
      M measure worldSchema AdversarialAddress ClosedWorldAddress.adversary)
    (environment : PPTEnvironment.{uCost, uAddress, uPayload, uPort,
      uCapability, uState, uLeakage, uErasure, uOutput}
      M measure worldSchema EnvironmentAddress ClosedWorldAddress.environment),
      RealExecutionData policy environment protocol adversary network
  idealData : ∀
    (simulator : PPTSimulator.{uCost, uAddress, uPayload, uPort,
      uCapability, uState, uLeakage, uErasure, uOutput}
      M measure worldSchema AdversarialAddress ClosedWorldAddress.adversary)
    (environment : PPTEnvironment.{uCost, uAddress, uPayload, uPort,
      uCapability, uState, uLeakage, uErasure, uOutput}
      M measure worldSchema EnvironmentAddress ClosedWorldAddress.environment),
      IdealExecutionData policy environment functionality simulator network

namespace ExecutableExperiment

noncomputable def toExperiment
    (executable : ExecutableExperiment.{uCost, uAddress, uPayload, uPort,
      uCapability, uState, uLeakage, uErasure, uOutput}
      (M := M) (measure := measure) (worldSchema := worldSchema)) :
    Experiment.{uCost, uAddress, uPayload, uPort, uCapability,
      uState, uLeakage, uErasure, uOutput}
      M measure EnvironmentAddress SystemAddress AdversarialAddress
        NetworkAddress worldSchema where
  policy := executable.policy
  protocol := executable.protocol
  functionality := executable.functionality
  network := executable.network
  real := fun adversary environment =>
    (executable.realData adversary environment).bound
  ideal := fun simulator environment =>
    (executable.idealData simulator environment).bound

end ExecutableExperiment

/--
The typed system hole of a context.

One structural transformation is used for both worlds.  The distinct
`Protocol` and `IdealFunctionality` wrappers below are derived from this same
`fill`; a context therefore cannot apply unrelated transformations on its real
and ideal sides or supply a preassembled outer experiment.
-/
structure SystemHole where
  fill :
    AddressedITM.{uCost, uAddress, uPayload, uPort, uCapability,
      uState, uLeakage, uErasure, uOutput}
      M worldSchema SystemAddress ClosedWorldAddress.system →
    AddressedITM.{uCost, uAddress, uPayload, uPort, uCapability,
      uState, uLeakage, uErasure, uOutput}
      M worldSchema SystemAddress ClosedWorldAddress.system

namespace SystemHole

def plugProtocol
    (hole : SystemHole.{uCost, uAddress, uPayload, uPort, uCapability,
      uState, uLeakage, uErasure, uOutput}
      (M := M) (worldSchema := worldSchema))
    (protocol : Protocol.{uCost, uAddress, uPayload, uPort, uCapability,
      uState, uLeakage, uErasure, uOutput}
      M worldSchema SystemAddress ClosedWorldAddress.system) :
    Protocol.{uCost, uAddress, uPayload, uPort, uCapability,
      uState, uLeakage, uErasure, uOutput}
      M worldSchema SystemAddress ClosedWorldAddress.system where
  machine := hole.fill protocol.machine

def plugFunctionality
    (hole : SystemHole.{uCost, uAddress, uPayload, uPort, uCapability,
      uState, uLeakage, uErasure, uOutput}
      (M := M) (worldSchema := worldSchema))
    (functionality : IdealFunctionality.{uCost, uAddress, uPayload, uPort,
      uCapability, uState, uLeakage, uErasure, uOutput}
      M worldSchema SystemAddress ClosedWorldAddress.system) :
    IdealFunctionality.{uCost, uAddress, uPayload, uPort, uCapability,
      uState, uLeakage, uErasure, uOutput}
      M worldSchema SystemAddress ClosedWorldAddress.system where
  machine := hole.fill functionality.machine

def identity : SystemHole.{uCost, uAddress, uPayload, uPort, uCapability,
    uState, uLeakage, uErasure, uOutput}
    (M := M) (worldSchema := worldSchema) where
  fill := id

def comp
    (inner outer : SystemHole.{uCost, uAddress, uPayload, uPort, uCapability,
      uState, uLeakage, uErasure, uOutput}
      (M := M) (worldSchema := worldSchema)) :
    SystemHole.{uCost, uAddress, uPayload, uPort, uCapability,
      uState, uLeakage, uErasure, uOutput}
      (M := M) (worldSchema := worldSchema) where
  fill := outer.fill ∘ inner.fill

end SystemHole

/--
Structural inputs for plugging one executable experiment into a typed system
hole.  The only complete worlds stored here are `RealExecutionData` and
`IdealExecutionData` indexed by the components obtained by actually applying
the hole and network transformations to `inner`.
-/
structure ContextBuilder
    (inner : ExecutableExperiment.{uCost, uAddress, uPayload, uPort,
      uCapability, uState, uLeakage, uErasure, uOutput}
      (M := M) (measure := measure) (worldSchema := worldSchema)) where
  hole : SystemHole.{uCost, uAddress, uPayload, uPort, uCapability,
    uState, uLeakage, uErasure, uOutput}
    (M := M) (worldSchema := worldSchema)
  /-- One policy transformation, shared by the real and ideal fillings. -/
  plugPolicy :
    CorruptionPolicy
        (WorldAddress EnvironmentAddress SystemAddress
          AdversarialAddress NetworkAddress) →
      CorruptionPolicy
        (WorldAddress EnvironmentAddress SystemAddress
          AdversarialAddress NetworkAddress)
  plugNetwork :
    Network.{uCost, uAddress, uPayload, uPort, uCapability,
      uState, uLeakage, uErasure, uOutput}
      M worldSchema NetworkAddress ClosedWorldAddress.network →
    Network.{uCost, uAddress, uPayload, uPort, uCapability,
      uState, uLeakage, uErasure, uOutput}
      M worldSchema NetworkAddress ClosedWorldAddress.network
  realData : ∀
    (adversary : PPTAdversary.{uCost, uAddress, uPayload, uPort,
      uCapability, uState, uLeakage, uErasure, uOutput}
      M measure worldSchema AdversarialAddress ClosedWorldAddress.adversary)
    (environment : PPTEnvironment.{uCost, uAddress, uPayload, uPort,
      uCapability, uState, uLeakage, uErasure, uOutput}
      M measure worldSchema EnvironmentAddress ClosedWorldAddress.environment),
      RealExecutionData (plugPolicy inner.policy) environment
        (hole.plugProtocol inner.protocol) adversary (plugNetwork inner.network)
  idealData : ∀
    (simulator : PPTSimulator.{uCost, uAddress, uPayload, uPort,
      uCapability, uState, uLeakage, uErasure, uOutput}
      M measure worldSchema AdversarialAddress ClosedWorldAddress.adversary)
    (environment : PPTEnvironment.{uCost, uAddress, uPayload, uPort,
      uCapability, uState, uLeakage, uErasure, uOutput}
      M measure worldSchema EnvironmentAddress ClosedWorldAddress.environment),
      IdealExecutionData (plugPolicy inner.policy) environment
        (hole.plugFunctionality inner.functionality) simulator
        (plugNetwork inner.network)

namespace ContextBuilder

variable
  {inner : ExecutableExperiment.{uCost, uAddress, uPayload, uPort,
    uCapability, uState, uLeakage, uErasure, uOutput}
    (M := M) (measure := measure) (worldSchema := worldSchema)}

noncomputable def build
    (builder : ContextBuilder inner) :
    ExecutableExperiment.{uCost, uAddress, uPayload, uPort, uCapability,
      uState, uLeakage, uErasure, uOutput}
      (M := M) (measure := measure) (worldSchema := worldSchema) where
  policy := builder.plugPolicy inner.policy
  protocol := builder.hole.plugProtocol inner.protocol
  functionality := builder.hole.plugFunctionality inner.functionality
  network := builder.plugNetwork inner.network
  realData := builder.realData
  idealData := builder.idealData

noncomputable def identity
    (inner : ExecutableExperiment.{uCost, uAddress, uPayload, uPort,
      uCapability, uState, uLeakage, uErasure, uOutput}
      (M := M) (measure := measure) (worldSchema := worldSchema)) :
    ContextBuilder inner where
  hole := SystemHole.identity
  plugPolicy := id
  plugNetwork := id
  realData := inner.realData
  idealData := inner.idealData

noncomputable def comp
    (innerBuilder : ContextBuilder inner)
    (outerBuilder : ContextBuilder innerBuilder.build) :
    ContextBuilder inner where
  hole := innerBuilder.hole.comp outerBuilder.hole
  plugPolicy := outerBuilder.plugPolicy ∘ innerBuilder.plugPolicy
  plugNetwork := outerBuilder.plugNetwork ∘ innerBuilder.plugNetwork
  realData := outerBuilder.realData
  idealData := outerBuilder.idealData

@[simp] theorem build_identity
    (inner : ExecutableExperiment.{uCost, uAddress, uPayload, uPort,
      uCapability, uState, uLeakage, uErasure, uOutput}
      (M := M) (measure := measure) (worldSchema := worldSchema)) :
    (identity inner).build = inner := rfl

@[simp] theorem build_comp
    (innerBuilder : ContextBuilder inner)
    (outerBuilder : ContextBuilder innerBuilder.build) :
    (innerBuilder.comp outerBuilder).build = outerBuilder.build := rfl

end ContextBuilder

/-- A step simulation between two concrete PPT-certified real executions. -/
structure RealExecutionSimulation
    (addressMap : AddressRenaming
      (WorldAddress EnvironmentAddress SystemAddress AdversarialAddress
        NetworkAddress)
      (WorldAddress EnvironmentAddress SystemAddress AdversarialAddress
        NetworkAddress))
    (outer inner : CertifiedRealWorld.{uCost, uAddress, uPayload, uPort,
      uCapability, uState, uLeakage, uErasure, uOutput}
      measure EnvironmentAddress SystemAddress AdversarialAddress NetworkAddress
        worldSchema) where
  kernel : KernelSimulation
    (outerFamily := outer.world.family) (innerFamily := inner.world.family)
    (outerPolicy := outer.world.policy) (innerPolicy := inner.world.policy)
    addressMap outer.world.kernelAlgebra outer.world.networkAdapter
      outer.world.initial outer.world.decision inner.world.kernelAlgebra
      inner.world.networkAdapter inner.world.initial inner.world.decision

namespace RealExecutionSimulation

/-- Composition of certified real-world simulations preserves the actual
kernel-level configuration map and step square. -/
noncomputable def comp
    {outerToMiddle middleToInner : AddressRenaming
      (WorldAddress EnvironmentAddress SystemAddress AdversarialAddress
        NetworkAddress)
      (WorldAddress EnvironmentAddress SystemAddress AdversarialAddress
        NetworkAddress)}
    {outer middle inner : CertifiedRealWorld.{uCost, uAddress, uPayload, uPort,
      uCapability, uState, uLeakage, uErasure, uOutput}
      measure EnvironmentAddress SystemAddress AdversarialAddress NetworkAddress
        worldSchema}
    (outerMiddle : RealExecutionSimulation outerToMiddle outer middle)
    (middleInner : RealExecutionSimulation middleToInner middle inner) :
    RealExecutionSimulation (outerToMiddle.comp middleToInner) outer inner where
  kernel := outerMiddle.kernel.comp middleInner.kernel

variable
  {addressMap : AddressRenaming
    (WorldAddress EnvironmentAddress SystemAddress AdversarialAddress
      NetworkAddress)
    (WorldAddress EnvironmentAddress SystemAddress AdversarialAddress
      NetworkAddress)}
  {outer inner : CertifiedRealWorld.{uCost, uAddress, uPayload, uPort,
    uCapability, uState, uLeakage, uErasure, uOutput}
    measure EnvironmentAddress SystemAddress AdversarialAddress NetworkAddress
      worldSchema}

def comparisonFuel
    (_simulation : RealExecutionSimulation addressMap outer inner)
    (sec : CryptoLib.Core.SecPar) : Nat :=
  max (outer.certificate.activationLimit sec)
    (inner.certificate.activationLimit sec)

/-- Step simulation plus both fuel-stability certificates imply game equality. -/
theorem execution_eq
    (simulation : RealExecutionSimulation addressMap outer inner) :
    outer.execution = inner.execution := by
  let fuel := simulation.comparisonFuel
  calc
    outer.execution = outer.world.execution fuel := by
      symm
      exact outer.execution_eq_of_activationLimit_le fuel
        (fun _sec => Nat.le_max_left _ _)
    _ = inner.world.execution fuel := by
      funext sec
      simpa only [RealWorld.execution, RealWorld.runCosted,
        Kernel.decisionDist] using
        simulation.kernel.initial_decisionDist_commutes (fuel sec) sec
    _ = inner.execution :=
      inner.execution_eq_of_activationLimit_le fuel
        (fun _sec => Nat.le_max_right _ _)

end RealExecutionSimulation

/-- A step simulation between two concrete PPT-certified ideal executions. -/
structure IdealExecutionSimulation
    (addressMap : AddressRenaming
      (WorldAddress EnvironmentAddress SystemAddress AdversarialAddress
        NetworkAddress)
      (WorldAddress EnvironmentAddress SystemAddress AdversarialAddress
        NetworkAddress))
    (outer inner : CertifiedIdealWorld.{uCost, uAddress, uPayload, uPort,
      uCapability, uState, uLeakage, uErasure, uOutput}
      measure EnvironmentAddress SystemAddress AdversarialAddress NetworkAddress
        worldSchema) where
  kernel : KernelSimulation
    (outerFamily := outer.world.family) (innerFamily := inner.world.family)
    (outerPolicy := outer.world.policy) (innerPolicy := inner.world.policy)
    addressMap outer.world.kernelAlgebra outer.world.networkAdapter
      outer.world.initial outer.world.decision inner.world.kernelAlgebra
      inner.world.networkAdapter inner.world.initial inner.world.decision

namespace IdealExecutionSimulation

/-- Composition of certified ideal-world simulations preserves the actual
kernel-level configuration map and step square. -/
noncomputable def comp
    {outerToMiddle middleToInner : AddressRenaming
      (WorldAddress EnvironmentAddress SystemAddress AdversarialAddress
        NetworkAddress)
      (WorldAddress EnvironmentAddress SystemAddress AdversarialAddress
        NetworkAddress)}
    {outer middle inner : CertifiedIdealWorld.{uCost, uAddress, uPayload, uPort,
      uCapability, uState, uLeakage, uErasure, uOutput}
      measure EnvironmentAddress SystemAddress AdversarialAddress NetworkAddress
        worldSchema}
    (outerMiddle : IdealExecutionSimulation outerToMiddle outer middle)
    (middleInner : IdealExecutionSimulation middleToInner middle inner) :
    IdealExecutionSimulation (outerToMiddle.comp middleToInner) outer inner where
  kernel := outerMiddle.kernel.comp middleInner.kernel

variable
  {addressMap : AddressRenaming
    (WorldAddress EnvironmentAddress SystemAddress AdversarialAddress
      NetworkAddress)
    (WorldAddress EnvironmentAddress SystemAddress AdversarialAddress
      NetworkAddress)}
  {outer inner : CertifiedIdealWorld.{uCost, uAddress, uPayload, uPort,
    uCapability, uState, uLeakage, uErasure, uOutput}
    measure EnvironmentAddress SystemAddress AdversarialAddress NetworkAddress
      worldSchema}

def comparisonFuel
    (_simulation : IdealExecutionSimulation addressMap outer inner)
    (sec : CryptoLib.Core.SecPar) : Nat :=
  max (outer.certificate.activationLimit sec)
    (inner.certificate.activationLimit sec)

theorem execution_eq
    (simulation : IdealExecutionSimulation addressMap outer inner) :
    outer.execution = inner.execution := by
  let fuel := simulation.comparisonFuel
  calc
    outer.execution = outer.world.execution fuel := by
      symm
      exact outer.execution_eq_of_activationLimit_le fuel
        (fun _sec => Nat.le_max_left _ _)
    _ = inner.world.execution fuel := by
      funext sec
      simpa only [IdealWorld.execution, IdealWorld.runCosted,
        Kernel.decisionDist] using
        simulation.kernel.initial_decisionDist_commutes (fuel sec) sec
    _ = inner.execution :=
      inner.execution_eq_of_activationLimit_le fuel
        (fun _sec => Nat.le_max_right _ _)

end IdealExecutionSimulation

/--
An executable typed context around a structurally built experiment.

The address renaming is role preserving.  Real and ideal obligations are
one-step kernel simulations between the actual certified worlds generated by
the outer and inner `ExecutableExperiment` values.
-/
structure Context
    (inner : ExecutableExperiment.{uCost, uAddress, uPayload, uPort,
      uCapability, uState, uLeakage, uErasure, uOutput}
      (M := M) (measure := measure) (worldSchema := worldSchema)) where
  builder : ContextBuilder inner
  addressRenaming : WorldRenaming EnvironmentAddress SystemAddress
    AdversarialAddress NetworkAddress
  contextAdversary :
    PPTAdversary.{uCost, uAddress, uPayload, uPort, uCapability,
      uState, uLeakage, uErasure, uOutput}
      M measure worldSchema AdversarialAddress ClosedWorldAddress.adversary →
    PPTAdversary.{uCost, uAddress, uPayload, uPort, uCapability,
      uState, uLeakage, uErasure, uOutput}
      M measure worldSchema AdversarialAddress ClosedWorldAddress.adversary
  contextEnvironment :
    PPTEnvironment.{uCost, uAddress, uPayload, uPort, uCapability,
      uState, uLeakage, uErasure, uOutput}
      M measure worldSchema EnvironmentAddress ClosedWorldAddress.environment →
    PPTEnvironment.{uCost, uAddress, uPayload, uPort, uCapability,
      uState, uLeakage, uErasure, uOutput}
      M measure worldSchema EnvironmentAddress ClosedWorldAddress.environment
  plugSimulator :
    PPTSimulator.{uCost, uAddress, uPayload, uPort, uCapability,
      uState, uLeakage, uErasure, uOutput}
      M measure worldSchema AdversarialAddress ClosedWorldAddress.adversary →
    PPTSimulator.{uCost, uAddress, uPayload, uPort, uCapability,
      uState, uLeakage, uErasure, uOutput}
      M measure worldSchema AdversarialAddress ClosedWorldAddress.adversary
  realSimulation : ∀ adversary environment,
    RealExecutionSimulation addressRenaming.global
      (builder.build.realData adversary environment).certified
      (inner.realData (contextAdversary adversary)
        (contextEnvironment environment)).certified
  idealSimulation : ∀ simulator environment,
    IdealExecutionSimulation addressRenaming.global
      (builder.build.idealData (plugSimulator simulator) environment).certified
      (inner.idealData simulator (contextEnvironment environment)).certified

namespace Context

variable
  {inner : ExecutableExperiment.{uCost, uAddress, uPayload, uPort,
    uCapability, uState, uLeakage, uErasure, uOutput}
    (M := M) (measure := measure) (worldSchema := worldSchema)}

/-- The outer executable experiment is definitionally built by filling the
context's typed system hole with `inner`'s protocol and functionality. -/
noncomputable def outer
    (context : Context inner) :
    ExecutableExperiment.{uCost, uAddress, uPayload, uPort, uCapability,
      uState, uLeakage, uErasure, uOutput}
      (M := M) (measure := measure) (worldSchema := worldSchema) :=
  context.builder.build

noncomputable def plug
    (context : Context inner) :=
  context.outer.toExperiment

noncomputable def innerExperiment
    (inner : ExecutableExperiment.{uCost, uAddress, uPayload, uPort,
      uCapability, uState, uLeakage, uErasure, uOutput}
      (M := M) (measure := measure) (worldSchema := worldSchema)) :=
  inner.toExperiment

/-- Identity is available only for structurally executable experiments. -/
noncomputable def identity
    (inner : ExecutableExperiment.{uCost, uAddress, uPayload, uPort,
      uCapability, uState, uLeakage, uErasure, uOutput}
      (M := M) (measure := measure) (worldSchema := worldSchema)) : Context inner where
  builder := ContextBuilder.identity inner
  addressRenaming := WorldRenaming.identity EnvironmentAddress SystemAddress
    AdversarialAddress NetworkAddress
  contextAdversary := id
  contextEnvironment := id
  plugSimulator := id
  realSimulation := by
    intro adversary environment
    let certified := (inner.realData adversary environment).certified
    change RealExecutionSimulation
      (WorldRenaming.identity EnvironmentAddress SystemAddress
        AdversarialAddress NetworkAddress).global certified certified
    simpa only [WorldRenaming.identity_global] using (show
      RealExecutionSimulation
        (AddressRenaming.identity
          (WorldAddress EnvironmentAddress SystemAddress AdversarialAddress
            NetworkAddress)) certified certified from {
      kernel := KernelSimulation.identity certified.world.kernelAlgebra
        certified.world.networkAdapter certified.world.initial
          certified.world.decision
    })
  idealSimulation := by
    intro simulator environment
    let certified := (inner.idealData simulator environment).certified
    change IdealExecutionSimulation
      (WorldRenaming.identity EnvironmentAddress SystemAddress
        AdversarialAddress NetworkAddress).global certified certified
    simpa only [WorldRenaming.identity_global] using (show
      IdealExecutionSimulation
        (AddressRenaming.identity
          (WorldAddress EnvironmentAddress SystemAddress AdversarialAddress
            NetworkAddress)) certified certified from {
      kernel := KernelSimulation.identity certified.world.kernelAlgebra
        certified.world.networkAdapter certified.world.initial
          certified.world.decision
    })

@[simp] theorem plug_identity
    (inner : ExecutableExperiment.{uCost, uAddress, uPayload, uPort,
      uCapability, uState, uLeakage, uErasure, uOutput}
      (M := M) (measure := measure) (worldSchema := worldSchema)) :
    (identity inner).plug = inner.toExperiment := rfl

/--
Sequentially plug two executable contexts.  The composite simulations are
formed from the two configuration-level `Kernel.stepOne` squares; no
whole-experiment equality is accepted as input.
-/
noncomputable def compose
    (innerContext : Context inner)
    (outerContext : Context innerContext.outer) : Context inner where
  builder := innerContext.builder.comp outerContext.builder
  addressRenaming :=
    outerContext.addressRenaming.comp innerContext.addressRenaming
  contextAdversary :=
    innerContext.contextAdversary ∘ outerContext.contextAdversary
  contextEnvironment :=
    innerContext.contextEnvironment ∘ outerContext.contextEnvironment
  plugSimulator :=
    outerContext.plugSimulator ∘ innerContext.plugSimulator
  realSimulation := by
    intro adversary environment
    have outerToMiddle := outerContext.realSimulation adversary environment
    have middleToInner := innerContext.realSimulation
      (outerContext.contextAdversary adversary)
      (outerContext.contextEnvironment environment)
    simpa only [WorldRenaming.global_comp] using
      outerToMiddle.comp middleToInner
  idealSimulation := by
    intro simulator environment
    have outerToMiddle := outerContext.idealSimulation
      (innerContext.plugSimulator simulator) environment
    have middleToInner := innerContext.idealSimulation simulator
      (outerContext.contextEnvironment environment)
    simpa only [WorldRenaming.global_comp] using
      outerToMiddle.comp middleToInner

@[simp] theorem plug_compose
    (innerContext : Context inner)
    (outerContext : Context innerContext.outer) :
    (innerContext.compose outerContext).plug = outerContext.plug := rfl

/-- Plugging is associative at the actual structurally assembled outer world. -/
@[simp] theorem plug_assoc
    (first : Context inner)
    (second : Context first.outer)
    (third : Context second.outer) :
    ((first.compose second).compose third).plug =
      (first.compose (second.compose third)).plug := rfl

/-- Both associations induce the same role-preserving address transport. -/
theorem compose_addressRenaming_assoc
    (first : Context inner)
    (second : Context first.outer)
    (third : Context second.outer) :
    ((first.compose second).compose third).addressRenaming =
      (first.compose (second.compose third)).addressRenaming := by
  exact WorldRenaming.comp_assoc third.addressRenaming
    second.addressRenaming first.addressRenaming

/-- A shared-fuel real game equals its own concrete certified execution. -/
private theorem realExecution_eq_own
    (experiment : Experiment.{uCost, uAddress, uPayload, uPort, uCapability,
      uState, uLeakage, uErasure, uOutput}
      M measure EnvironmentAddress SystemAddress AdversarialAddress
        NetworkAddress worldSchema)
    (adversary : PPTAdversary.{uCost, uAddress, uPayload, uPort,
      uCapability, uState, uLeakage, uErasure, uOutput}
      M measure worldSchema AdversarialAddress ClosedWorldAddress.adversary)
    (simulator : PPTSimulator.{uCost, uAddress, uPayload, uPort,
      uCapability, uState, uLeakage, uErasure, uOutput}
      M measure worldSchema AdversarialAddress ClosedWorldAddress.adversary)
    (environment : PPTEnvironment.{uCost, uAddress, uPayload, uPort,
      uCapability, uState, uLeakage, uErasure, uOutput}
      M measure worldSchema EnvironmentAddress ClosedWorldAddress.environment) :
    Experiment.realExecution experiment adversary simulator environment =
      (experiment.real adversary environment).certified.execution := by
  let certified := (experiment.real adversary environment).certified
  let pair := experiment.certifiedPair adversary simulator environment
  simpa only [Experiment.realExecution, pair, certified,
    CertifiedWorldPair.realExecution, Experiment.certifiedPair] using
    certified.execution_eq_of_activationLimit_le pair.commonFuel
      (fun _sec => Nat.le_max_left _ _)

/-- A shared-fuel ideal game equals its own concrete certified execution. -/
private theorem idealExecution_eq_own
    (experiment : Experiment.{uCost, uAddress, uPayload, uPort, uCapability,
      uState, uLeakage, uErasure, uOutput}
      M measure EnvironmentAddress SystemAddress AdversarialAddress
        NetworkAddress worldSchema)
    (adversary : PPTAdversary.{uCost, uAddress, uPayload, uPort,
      uCapability, uState, uLeakage, uErasure, uOutput}
      M measure worldSchema AdversarialAddress ClosedWorldAddress.adversary)
    (simulator : PPTSimulator.{uCost, uAddress, uPayload, uPort,
      uCapability, uState, uLeakage, uErasure, uOutput}
      M measure worldSchema AdversarialAddress ClosedWorldAddress.adversary)
    (environment : PPTEnvironment.{uCost, uAddress, uPayload, uPort,
      uCapability, uState, uLeakage, uErasure, uOutput}
      M measure worldSchema EnvironmentAddress ClosedWorldAddress.environment) :
    Experiment.idealExecution experiment adversary simulator environment =
      (experiment.ideal simulator environment).certified.execution := by
  let certified := (experiment.ideal simulator environment).certified
  let pair := experiment.certifiedPair adversary simulator environment
  simpa only [Experiment.idealExecution, pair, certified,
    CertifiedWorldPair.idealExecution, Experiment.certifiedPair] using
    certified.execution_eq_of_activationLimit_le pair.commonFuel
      (fun _sec => Nat.le_max_right _ _)

/-- Real operational equality derived from the concrete step simulation. -/
theorem real_operational
    (context : Context inner) (adversary) (simulator) (environment) :
    Experiment.realExecution context.plug adversary
        (context.plugSimulator simulator) environment =
      Experiment.realExecution inner.toExperiment
        (context.contextAdversary adversary) simulator
          (context.contextEnvironment environment) := by
  calc
    Experiment.realExecution context.plug adversary
        (context.plugSimulator simulator) environment =
        (context.outer.realData adversary environment).certified.execution := by
      simpa only [plug, ExecutableExperiment.toExperiment,
        RealExecutionData.bound] using
        realExecution_eq_own context.plug adversary
          (context.plugSimulator simulator) environment
    _ = (inner.realData (context.contextAdversary adversary)
          (context.contextEnvironment environment)).certified.execution :=
      (context.realSimulation adversary environment).execution_eq
    _ = Experiment.realExecution inner.toExperiment
          (context.contextAdversary adversary) simulator
            (context.contextEnvironment environment) := by
      symm
      simpa only [ExecutableExperiment.toExperiment,
        RealExecutionData.bound] using
        realExecution_eq_own inner.toExperiment
          (context.contextAdversary adversary) simulator
            (context.contextEnvironment environment)

/-- Ideal operational equality derived from the concrete step simulation. -/
theorem ideal_operational
    (context : Context inner) (adversary) (simulator) (environment) :
    Experiment.idealExecution context.plug adversary
        (context.plugSimulator simulator) environment =
      Experiment.idealExecution inner.toExperiment
        (context.contextAdversary adversary) simulator
          (context.contextEnvironment environment) := by
  calc
    Experiment.idealExecution context.plug adversary
        (context.plugSimulator simulator) environment =
        (context.outer.idealData (context.plugSimulator simulator)
          environment).certified.execution := by
      simpa only [plug, ExecutableExperiment.toExperiment,
        IdealExecutionData.bound] using
        idealExecution_eq_own context.plug adversary
          (context.plugSimulator simulator) environment
    _ = (inner.idealData simulator
          (context.contextEnvironment environment)).certified.execution :=
      (context.idealSimulation simulator environment).execution_eq
    _ = Experiment.idealExecution inner.toExperiment
          (context.contextAdversary adversary) simulator
            (context.contextEnvironment environment) := by
      symm
      simpa only [ExecutableExperiment.toExperiment,
        IdealExecutionData.bound] using
        idealExecution_eq_own inner.toExperiment
          (context.contextAdversary adversary) simulator
            (context.contextEnvironment environment)

/-- Universal composition from executable one-step simulations. -/
theorem uc_compose
    (context : Context inner)
    (secure : Experiment.UCEmulates inner.toExperiment) :
    Experiment.UCEmulates context.plug := by
  intro adversary
  obtain ⟨simulator, simulatorSecure⟩ :=
    secure (context.contextAdversary adversary)
  refine ⟨context.plugSimulator simulator, ?_⟩
  intro environment
  rw [context.real_operational adversary simulator environment,
    context.ideal_operational adversary simulator environment]
  exact simulatorSecure (context.contextEnvironment environment)

end Context

end ClosedWorldBuilder

end CryptoLib.Core.Infrastructure.UC

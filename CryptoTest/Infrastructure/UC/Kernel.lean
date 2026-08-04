import Crypto.Infrastructure.UC.Kernel
import Mathlib.Tactic

namespace CryptoTest.Infrastructure.UC.Kernel

open Crypto.Infrastructure.Computation.Algebra
open Crypto.Infrastructure.Computation.Cost
open Crypto.Infrastructure.UC

/-! ## Hierarchical session isolation -/

def rootSession (root : Nat) : SID Nat :=
  ⟨root, []⟩

example : (rootSession 3).Ancestor ((rootSession 3).child 7) :=
  SID.ancestor_child _ _

example : ¬ (rootSession 3).Ancestor ((rootSession 4).child 7) := by
  simp [SID.Ancestor, rootSession, SID.child]

example : ((rootSession 3).child 7).root = (rootSession 3).root :=
  rfl

/-! ## Typed endpoints and proof-carrying routing -/

/-- Only controller `true` may statically claim address `false`. -/
inductive ToySendAs : Bool → Bool → Type where
  | trueClaimsFalse : ToySendAs true false

def toySchema : PortSchema.{0, 0, 0, 0} Bool where
  Port := fun _address _direction _payload => Unit
  CanConnect := fun _sourcePort _targetPort => Unit
  CanSendAs := ToySendAs
  route := fun _sourcePort _targetPort _capability => .direct

def directEmission : Emission toySchema false where
  Payload := Unit
  sourcePort := ()
  target := ⟨true, ()⟩
  capability := ()
  payload := ()

example : directEmission.routingPolicy = .direct :=
  rfl

example : directEmission.routingPolicy.observable = false :=
  rfl

example :
    RoutingPolicy.adversarialAuthenticated.deliveryAuthority =
      DeliveryAuthority.adversary :=
  rfl

example : RoutingPolicy.adversarialForgeable.forgeable = true :=
  rfl

example : RoutingPolicy.adversarialBroadcast.broadcastable = true :=
  rfl

/-- Send-as is an explicit address-indexed capability carried by the action. -/
example : LocalAction toySchema true Unit Bool :=
  LocalAction.emitAs false .trueClaimsFalse directEmission

/-- An address-scoped capability cannot be reused for another claimed source. -/
example (authorization : toySchema.CanSendAs false true) : False := by
  cases authorization

example : (QueuedActivation.ofEmission directEmission).target = true :=
  rfl

/-! ## A small exactly costed ITM family -/

noncomputable abbrev toyFamily :
    ITMFamily.{0, 0, 0, 0, 0, 0, 0, 0, 0}
      CostModel.nat Bool toySchema where
  State := fun _sec _address => Nat
  Leakage := fun _sec _address => Nat
  Erasure := fun _sec _address => Unit
  Output := fun _sec _address => Bool
  init := fun _sec _address =>
    RandCosted.liftCosted (⟨0, 3⟩ : Costed CostModel.nat Nat)
  activate := fun _sec address state _input =>
    if _h : address = false then
      RandCosted.pure CostModel.nat
        ⟨state + 1, LocalAction.requestCorruption true⟩
    else
      RandCosted.pure CostModel.nat
        ⟨state + 1, LocalAction.yield⟩
  applyErasure := fun _sec _address _request state =>
    ⟨state, 0⟩
  leak := fun _sec _address state =>
    ⟨state, 0⟩

def toyPolicy : CorruptionPolicy Bool :=
  CorruptionPolicy.dynamic (fun _corrupted => True) (fun _corrupted => inferInstance)

def toyNetwork (sec : Crypto.SecPar) : NetworkAdapter (toyFamily) sec where
  observe := fun emission => QueuedActivation.ofEmission emission
  control := fun activation => activation
  leakage := fun target _leakage => QueuedActivation.resume target

def initialConfiguration : Configuration toyFamily toyPolicy 0 where
  state := fun _address => some 7
  queue := [.activation (QueuedActivation.resume false)]
  corrupted := ∅
  output := none
  trace := []
  corruptionInvariant := by
    constructor
    · trivial
    · intro address haddress
      simp at haddress

/-! ## FIFO scheduling and one-action activation -/

def secondActivation : QueuedActivation toySchema :=
  QueuedActivation.resume true

example :
    (initialConfiguration.enqueue secondActivation).queue =
      [.activation (QueuedActivation.resume false), .activation secondActivation] :=
  rfl

example :
    ∃ remaining,
      Configuration.dequeue (initialConfiguration.enqueue secondActivation) =
        some (.activation (QueuedActivation.resume false), remaining) ∧
      remaining.queue = [.activation secondActivation] := by
  exact Configuration.dequeue_enqueue_of_queue_eq_cons
    initialConfiguration (.activation (QueuedActivation.resume false)) []
      secondActivation rfl

/-- The activation interface returns one `LocalAction`, never a hidden action list. -/
example :
    RandCosted.valueDist
      (toyFamily.activate 0 false 7 ActivationInput.resume) =
      PMF.pure
        (⟨8, LocalAction.requestCorruption true⟩ :
          ActivationResult Nat (LocalAction toySchema false Unit Bool)) := by
  simp [toyFamily]

/-! ## Exact kernel charging and fuel semantics -/

example :
    KernelAlgebra.charge (KernelAlgebra.zero CostModel.nat Bool)
        .dequeue [] =
      RandCosted.pure CostModel.nat () :=
  rfl

example :
    RandCosted.CostBound
      (KernelAlgebra.charge (KernelAlgebra.zero CostModel.nat Bool)
        .dequeue []) 0 := by
  exact RandCosted.CostBound.pure ()

noncomputable def chargedKernelAlgebra :
    KernelAlgebra CostModel.nat Bool where
  exec operation :=
    match operation with
    | .perform _primitive _addresses =>
        RandCosted.liftCosted (⟨(), 2⟩ : Costed CostModel.nat Unit)

example :
    KernelAlgebra.charge chargedKernelAlgebra .route [false, true] =
      RandCosted.liftCosted
        (⟨(), 2⟩ : Costed CostModel.nat Unit) :=
  rfl

example :
    RandCosted.CostBound
      (KernelAlgebra.charge chargedKernelAlgebra .route [false, true]) 2 := by
  intro result hresult
  rw [show
    KernelAlgebra.charge chargedKernelAlgebra .route [false, true] =
      PMF.pure (⟨(), 2⟩ : Costed CostModel.nat Unit) by rfl] at hresult
  rw [PMF.mem_support_pure_iff] at hresult
  subst result
  exact Nat.le_refl 2

def deniedPolicy : CorruptionPolicy Bool :=
  CorruptionPolicy.incorruptible

def deniedCorruptionConfiguration : Configuration toyFamily deniedPolicy 0 where
  state := fun _address => some 7
  queue := []
  corrupted := ∅
  output := none
  trace := []
  corruptionInvariant := by
    constructor
    · rfl
    · intro address haddress
      simp at haddress

def expectedDeniedCorruption : Configuration toyFamily deniedPolicy 0 where
  state := fun _address => some 7
  queue := []
  corrupted := ∅
  output := none
  trace := [TraceEvent.corruptionRequested false true]
  corruptionInvariant := by
    constructor
    · rfl
    · intro address haddress
      simp at haddress

/-- Even a denied request pays exactly one explicit state-read charge. -/
theorem deniedCorruption_chargesReadState :
    Kernel.processCorruption chargedKernelAlgebra (toyNetwork 0)
        deniedCorruptionConfiguration false true =
      RandCosted.liftCosted
        (⟨expectedDeniedCorruption, 2⟩ :
          Costed CostModel.nat (Configuration toyFamily deniedPolicy 0)) := by
  simp [Kernel.processCorruption,
    KernelAlgebra.withCharge, KernelAlgebra.charge, chargedKernelAlgebra,
    Pure.pure, PMF.pure_bind, PMF.pure_map,
    RandCosted.liftCosted, RandCosted.pure,
    Costed.bind, Costed.pure,
    deniedPolicy, CorruptionPolicy.incorruptible,
    deniedCorruptionConfiguration, expectedDeniedCorruption,
    Configuration.record]

example :
    Kernel.runCosted (KernelAlgebra.zero CostModel.nat Bool)
        (toyNetwork 0) 0 initialConfiguration =
      RandCosted.pure CostModel.nat
        (Kernel.atFuelZero initialConfiguration) :=
  rfl

example :
    (Kernel.atFuelZero initialConfiguration).outcome =
      Kernel.ExecutionOutcome.timeout :=
  rfl

example :
    (Kernel.atFuelZero initialConfiguration).outcome.toBool
        (fun _result => true) = false :=
  rfl

/-! ## Dynamic send-as authorization -/

def forgedAction : LocalAction toySchema true Unit Bool :=
  LocalAction.emitAs false .trueClaimsFalse directEmission

def beforeSendAsConfiguration : Configuration toyFamily toyPolicy 0 where
  state := fun _address => some 7
  queue := []
  corrupted := ∅
  output := none
  trace := []
  corruptionInvariant := by
    constructor
    · trivial
    · intro address haddress
      simp at haddress

def rejectedSendAsConfiguration : Configuration toyFamily toyPolicy 0 where
  state := fun _address => some 7
  queue := []
  corrupted := ∅
  output := none
  trace := [TraceEvent.sendAsRejected true false]
  corruptionInvariant := by
    constructor
    · trivial
    · intro address haddress
      simp at haddress

/-- A static capability alone cannot authorize impersonation before corruption. -/
theorem sendAsBeforeCorruption_rejected :
    Kernel.processAction (KernelAlgebra.zero CostModel.nat Bool)
        (toyNetwork 0) beforeSendAsConfiguration true (by simp [beforeSendAsConfiguration])
        7 forgedAction =
      RandCosted.pure CostModel.nat rejectedSendAsConfiguration := by
  simp [Kernel.processAction, Kernel.routeEmissionAs,
    KernelAlgebra.withCharge, KernelAlgebra.charge, KernelAlgebra.zero,
    Pure.pure, PMF.pure_bind, PMF.pure_map,
    RandCosted.liftCosted, RandCosted.pure, Costed.bind, Costed.pure,
    forgedAction, beforeSendAsConfiguration, rejectedSendAsConfiguration,
    Configuration.record]

def afterCorruptionConfiguration : Configuration toyFamily toyPolicy 0 where
  state := LocalStore.remove (fun _address => some 7) false
  queue := []
  corrupted := {false}
  output := none
  trace := []
  corruptionInvariant := by
    constructor
    · trivial
    · intro address haddress
      have : address = false := by simpa using haddress
      subst address
      simp [LocalStore.remove]

def authorizedSendAsConfiguration : Configuration toyFamily toyPolicy 0 where
  state := LocalStore.remove (fun _address => some 7) false
  queue := [.activation (QueuedActivation.ofEmission directEmission)]
  corrupted := {false}
  output := none
  trace :=
    [TraceEvent.sendAsAuthorized true false, TraceEvent.emitted directEmission]
  corruptionInvariant := by
    constructor
    · trivial
    · intro address haddress
      have : address = false := by simpa using haddress
      subst address
      simp [LocalStore.remove]

/-- After corruption, the same address-indexed capability authorizes that address only. -/
theorem sendAsAfterCorruption_authorized :
    Kernel.processAction (KernelAlgebra.zero CostModel.nat Bool)
        (toyNetwork 0) afterCorruptionConfiguration true
        (by simp [afterCorruptionConfiguration]) 7 forgedAction =
      RandCosted.pure CostModel.nat authorizedSendAsConfiguration := by
  simp [Kernel.processAction, Kernel.routeEmissionAs, Kernel.routeEmissionCore,
    Kernel.enqueueDirect,
    KernelAlgebra.withCharge, KernelAlgebra.charge, KernelAlgebra.zero,
    Pure.pure, PMF.pure_bind, PMF.pure_map,
    RandCosted.liftCosted, RandCosted.pure, Costed.bind, Costed.pure,
    forgedAction, directEmission, toySchema,
    afterCorruptionConfiguration, authorizedSendAsConfiguration,
    Emission.routingPolicy, RoutingPolicy.deliveryAuthority,
    Configuration.record, Configuration.enqueue,
    Configuration.enqueueEvent, QueuedActivation.ofEmission]
  congr 1

/-! ## Dynamic corruption is an explicit kernel event -/

def expectedRequestConfiguration : Configuration toyFamily toyPolicy 0 where
  state :=
    LocalStore.set
      ((fun _address => some 7) : LocalStore toyFamily 0) false 8
  queue := [.corruptionRequest false true]
  corrupted := ∅
  output := none
  trace := [TraceEvent.activated (QueuedActivation.resume false)]
  corruptionInvariant := by
    constructor
    · trivial
    · intro address haddress
      simp at haddress

def expectedCorruptedConfiguration : Configuration toyFamily toyPolicy 0 where
  state :=
    LocalStore.remove
      (LocalStore.set
        ((fun _address => some 7) : LocalStore toyFamily 0) false 8) true
  queue := [.activation (QueuedActivation.resume true)]
  corrupted := {true}
  output := none
  trace :=
    [TraceEvent.activated (QueuedActivation.resume false),
      TraceEvent.corruptionRequested false true,
      TraceEvent.corrupted true 7]
  corruptionInvariant := by
    constructor
    · trivial
    · intro address haddress
      have : address = true := by
        simpa using haddress
      subst address
      simp [LocalStore.remove]

theorem toyRequestStep_exact :
    Kernel.stepOne (KernelAlgebra.zero CostModel.nat Bool)
        (toyNetwork 0) initialConfiguration =
      RandCosted.pure CostModel.nat
        (KernelStepResult.progressed expectedRequestConfiguration) := by
  simp [Kernel.stepOne, Kernel.activateHonest, Kernel.processAction,
    KernelAlgebra.withCharge, KernelAlgebra.charge, KernelAlgebra.zero,
    Bind.bind, Pure.pure, PMF.pure_bind, PMF.pure_map,
    RandCosted.liftCosted, RandCosted.pure,
    Costed.bind, Costed.pure,
    toyFamily, toyPolicy, toyNetwork, initialConfiguration,
    expectedRequestConfiguration,
    QueuedActivation.resume, QueuedActivation.ofInput,
    CorruptionPolicy.dynamic,
    Configuration.dequeue, Configuration.get,
    Configuration.set, Configuration.record,
    Configuration.enqueueCorruption, Configuration.enqueueEvent,
    Configuration.enqueue, Kernel.classify]
  congr 1

theorem toyCorruptionStep_exact :
    Kernel.stepOne (KernelAlgebra.zero CostModel.nat Bool)
        (toyNetwork 0) expectedRequestConfiguration =
      RandCosted.pure CostModel.nat
        (KernelStepResult.progressed expectedCorruptedConfiguration) := by
  simp [Kernel.stepOne, Kernel.processCorruption, Kernel.corruptFromState,
    KernelAlgebra.withCharge, KernelAlgebra.charge, KernelAlgebra.zero,
    Bind.bind, Pure.pure, PMF.pure_bind, PMF.pure_map,
    RandCosted.liftCosted, RandCosted.pure,
    Costed.bind, Costed.pure,
    toyFamily, toyPolicy, toyNetwork, expectedRequestConfiguration,
    expectedCorruptedConfiguration, QueuedActivation.resume,
    CorruptionPolicy.dynamic, Configuration.dequeue, Configuration.get,
    LocalStore.set,
    Configuration.record, Configuration.markCorrupted,
    Configuration.enqueue, Configuration.enqueueEvent, Kernel.classify]
  congr 1

theorem toyCorruptionStep_cost_eq_zero (result : Costed CostModel.nat
    (KernelStepResult toyFamily toyPolicy 0))
    (hresult : result ∈
      (Kernel.stepOne (KernelAlgebra.zero CostModel.nat Bool)
        (toyNetwork 0) expectedRequestConfiguration).support) :
    result.cost = 0 := by
  rw [toyCorruptionStep_exact, PMF.mem_support_pure_iff] at hresult
  subst result
  rfl

example :
    RandCosted.CostBound
      (Kernel.stepOne (KernelAlgebra.zero CostModel.nat Bool)
        (toyNetwork 0) expectedRequestConfiguration) 0 := by
  intro result hresult
  exact Nat.le_of_eq (toyCorruptionStep_cost_eq_zero result hresult)

theorem toyStep_dynamicCorruption
    (result : Costed CostModel.nat
      (KernelStepResult toyFamily toyPolicy 0))
    (hresult : result ∈
      (Kernel.stepOne (KernelAlgebra.zero CostModel.nat Bool)
        (toyNetwork 0) expectedRequestConfiguration).support) :
    ∃ configuration,
      result.val = KernelStepResult.progressed configuration ∧
      configuration.get true = none ∧
      true ∈ configuration.corrupted ∧
      configuration.queue = [.activation (QueuedActivation.resume true)] ∧
      configuration.trace.getLast? =
        some (TraceEvent.corrupted (family := toyFamily) (sec := 0) true 7) := by
  rw [toyCorruptionStep_exact, PMF.mem_support_pure_iff] at hresult
  subst result
  refine ⟨expectedCorruptedConfiguration, rfl, ?_, ?_, rfl, ?_⟩
  · rfl
  · simp [expectedCorruptedConfiguration]
  · rfl

/-! ## Corrupting a dormant address -/

def dormantRequestConfiguration : Configuration toyFamily toyPolicy 0 where
  state := LocalStore.remove (fun _address => some 7) true
  queue := [.corruptionRequest false true]
  corrupted := ∅
  output := none
  trace := []
  corruptionInvariant := by
    constructor
    · trivial
    · intro address haddress
      simp at haddress

def expectedDormantCorruption : Configuration toyFamily toyPolicy 0 where
  state :=
    LocalStore.remove (LocalStore.remove (fun _address => some 7) true) true
  queue := [.activation (QueuedActivation.resume true)]
  corrupted := {true}
  output := none
  trace :=
    [TraceEvent.corruptionRequested false true, TraceEvent.corrupted true 0]
  corruptionInvariant := by
    constructor
    · trivial
    · intro address haddress
      have : address = true := by simpa using haddress
      subst address
      simp [LocalStore.remove]

/--
Store absence triggers exact initialization (cost `3`) before leakage and the
same corruption commit; it does not silently discard a permitted request.
-/
theorem dormantCorruptionStep_exact :
    Kernel.stepOne (KernelAlgebra.zero CostModel.nat Bool)
        (toyNetwork 0) dormantRequestConfiguration =
      RandCosted.liftCosted
        (⟨KernelStepResult.progressed expectedDormantCorruption, 3⟩ :
          Costed CostModel.nat (KernelStepResult toyFamily toyPolicy 0)) := by
  simp [Kernel.stepOne, Kernel.processCorruption, Kernel.corruptFromState,
    KernelAlgebra.withCharge, KernelAlgebra.charge, KernelAlgebra.zero,
    Bind.bind, Pure.pure, PMF.pure_bind, PMF.pure_map,
    RandCosted.liftCosted, RandCosted.pure,
    Costed.bind, Costed.pure,
    toyFamily, toyPolicy, toyNetwork, dormantRequestConfiguration,
    expectedDormantCorruption, QueuedActivation.resume,
    CorruptionPolicy.dynamic, Configuration.dequeue, Configuration.get,
    LocalStore.remove, Configuration.record, Configuration.markCorrupted,
    Configuration.enqueue, Configuration.enqueueEvent, Kernel.classify]
  congr 1

/--
With a cost-`2` kernel handler, the dormant path exposes its complete order:
dequeue, read, initialize, component init (`3`), corrupt, and enqueue.
-/
theorem dormantCorruptionStep_charged_exact :
    Kernel.stepOne chargedKernelAlgebra (toyNetwork 0)
        dormantRequestConfiguration =
      RandCosted.liftCosted
        (⟨KernelStepResult.progressed expectedDormantCorruption, 13⟩ :
          Costed CostModel.nat (KernelStepResult toyFamily toyPolicy 0)) := by
  simp [Kernel.stepOne, Kernel.processCorruption, Kernel.corruptFromState,
    KernelAlgebra.withCharge, KernelAlgebra.charge, chargedKernelAlgebra,
    Bind.bind, Pure.pure, PMF.pure_bind, PMF.pure_map,
    RandCosted.liftCosted, RandCosted.pure,
    Costed.bind, Costed.pure,
    toyFamily, toyPolicy, toyNetwork, dormantRequestConfiguration,
    expectedDormantCorruption, QueuedActivation.resume,
    CorruptionPolicy.dynamic, Configuration.dequeue, Configuration.get,
    LocalStore.remove, Configuration.record, Configuration.markCorrupted,
    Configuration.enqueue, Configuration.enqueueEvent, Kernel.classify]
  congr 1

theorem dormant_mem_corrupted : true ∈ expectedDormantCorruption.corrupted := by
  simp [expectedDormantCorruption]

example : expectedDormantCorruption.get true = none :=
  expectedDormantCorruption.get_eq_none_of_mem_corrupted true dormant_mem_corrupted

end CryptoTest.Infrastructure.UC.Kernel

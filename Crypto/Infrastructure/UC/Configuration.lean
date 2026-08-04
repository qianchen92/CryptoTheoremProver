import Crypto.Infrastructure.UC.Corruption
import Crypto.Infrastructure.UC.ITM

namespace Crypto.Infrastructure.UC

open Crypto.Infrastructure.Computation.Cost

universe uCost uAddress uPayload uPort uCapability
universe uState uLeakage uErasure uOutput

variable {M : CostModel.{uCost}}
variable {Address : Type uAddress}
variable {schema : PortSchema.{uAddress, uPayload, uPort, uCapability} Address}

/--
A heterogeneous local-state store represented without type erasure.

The address index determines the type stored at that address.  A missing value
means that the instance has not been initialized or that its honest state has
been removed after corruption.
-/
abbrev LocalStore
    (family : ITMFamily.{uCost, uAddress, uPayload, uPort, uCapability,
      uState, uLeakage, uErasure, uOutput} M Address schema)
    (sec : Crypto.SecPar) :=
  (address : Address) → Option (family.State sec address)

namespace LocalStore

variable
    {family : ITMFamily.{uCost, uAddress, uPayload, uPort, uCapability,
      uState, uLeakage, uErasure, uOutput} M Address schema}
    {sec : Crypto.SecPar}

/-- The store in which no machine instance has local state. -/
def empty : LocalStore family sec :=
  fun _address => none

/-- Read the state at one address. -/
def get (store : LocalStore family sec) (address : Address) :
    Option (family.State sec address) :=
  store address

/-- Replace the state at exactly one address. -/
def set [DecidableEq Address]
    (store : LocalStore family sec) (address : Address)
    (state : family.State sec address) : LocalStore family sec :=
  fun other =>
    if h : other = address then
      h.symm ▸ some state
    else
      store other

/-- Remove any honest state stored at exactly one address. -/
def remove [DecidableEq Address]
    (store : LocalStore family sec) (address : Address) : LocalStore family sec :=
  fun other => if other = address then none else store other

@[simp] theorem get_empty (address : Address) :
    get (empty : LocalStore family sec) address = none :=
  rfl

@[simp] theorem get_set_same [DecidableEq Address]
    (store : LocalStore family sec) (address : Address)
    (state : family.State sec address) :
    get (set store address state) address = some state := by
  simp [get, set]

@[simp] theorem get_set_of_ne [DecidableEq Address]
    (store : LocalStore family sec) {address other : Address}
    (state : family.State sec address) (hne : other ≠ address) :
    get (set store address state) other = get store other := by
  simp [get, set, hne]

@[simp] theorem get_remove_same [DecidableEq Address]
    (store : LocalStore family sec) (address : Address) :
    get (remove store address) address = none := by
  simp [get, remove]

@[simp] theorem get_remove_of_ne [DecidableEq Address]
    (store : LocalStore family sec) {address other : Address}
    (hne : other ≠ address) :
    get (remove store address) other = get store other := by
  simp [get, remove, hne]

end LocalStore

/-- One queued activation, retaining the input type determined by its target. -/
structure QueuedActivation
    (schema : PortSchema.{uAddress, uPayload, uPort, uCapability} Address) where
  target : Address
  input : ActivationInput schema target

namespace QueuedActivation

/-- Queue an already target-indexed activation input. -/
def ofInput (target : Address) (input : ActivationInput schema target) :
    QueuedActivation schema :=
  ⟨target, input⟩

/-- Queue a resume activation for one machine instance. -/
def resume (target : Address) : QueuedActivation schema :=
  ⟨target, .resume⟩

/-- Deliver one typed emission to its statically indexed target. -/
def ofEmission {source : Address} (emission : Emission schema source) :
    QueuedActivation schema where
  target := emission.target.address
  input := .message {
    Payload := emission.Payload
    source := ⟨source, emission.sourcePort⟩
    targetPort := emission.target.port
    capability := emission.capability
    payload := emission.payload
  }

end QueuedActivation

/--
One event in the global FIFO.

Corruption requests are queued separately from ITM activations.  Processing a
request therefore consumes its own kernel step and cannot hide leakage/state
removal inside the activation that asked for corruption.
-/
inductive QueuedEvent
    (schema : PortSchema.{uAddress, uPayload, uPort, uCapability} Address) where
  | activation (activation : QueuedActivation schema)
  | corruptionRequest (source target : Address)

/-- A machine output whose type is determined by the producing address. -/
structure MachineOutput
    (family : ITMFamily.{uCost, uAddress, uPayload, uPort, uCapability,
      uState, uLeakage, uErasure, uOutput} M Address schema)
    (sec : Crypto.SecPar) where
  source : Address
  value : family.Output sec source

/-- Typed audit events produced by the single-activation kernel. -/
inductive TraceEvent
    (family : ITMFamily.{uCost, uAddress, uPayload, uPort, uCapability,
      uState, uLeakage, uErasure, uOutput} M Address schema)
    (sec : Crypto.SecPar) where
  | activated (activation : QueuedActivation schema)
  | yielded (source : Address)
  | emitted {source : Address} (emission : Emission schema source)
  | erased (source : Address) (request : family.Erasure sec source)
  | spawned (source target : Address) (initial : ActivationInput schema target)
  | sendAsAuthorized (controller claimedSource : Address)
  | sendAsRejected (controller claimedSource : Address)
  | corruptionRequested (source target : Address)
  | corrupted (target : Address) (leakage : family.Leakage sec target)
  | output (result : MachineOutput family sec)

/--
The policy and state-removal invariant maintained by a UC configuration.

No honest local state remains at a corrupted address.  Consequently later
leakage can only be produced by the explicit corruption transition that first
removes that state.
-/
def CorruptionInvariant [DecidableEq Address]
    (family : ITMFamily.{uCost, uAddress, uPayload, uPort, uCapability,
      uState, uLeakage, uErasure, uOutput} M Address schema)
    (policy : CorruptionPolicy Address) (sec : Crypto.SecPar)
    (state : LocalStore family sec) (corrupted : Finset Address) : Prop :=
  policy.Admissible corrupted ∧
    ∀ address, address ∈ corrupted → state address = none

/--
A finite-prefix UC configuration with an explicit FIFO activation queue.

The dependent function `state` is the sole global store.  The optional output
marks a halted configuration; the kernel, rather than this data structure,
decides how fuel exhaustion is mapped to the external Boolean result.
-/
structure Configuration [DecidableEq Address]
    (family : ITMFamily.{uCost, uAddress, uPayload, uPort, uCapability,
      uState, uLeakage, uErasure, uOutput} M Address schema)
    (policy : CorruptionPolicy Address) (sec : Crypto.SecPar) where
  state : LocalStore family sec
  queue : List (QueuedEvent schema)
  corrupted : Finset Address
  output : Option (MachineOutput family sec)
  trace : List (TraceEvent family sec)
  corruptionInvariant :
    CorruptionInvariant family policy sec state corrupted

namespace Configuration

variable [DecidableEq Address]
variable
    {family : ITMFamily.{uCost, uAddress, uPayload, uPort, uCapability,
      uState, uLeakage, uErasure, uOutput} M Address schema}
    {policy : CorruptionPolicy Address}
    {sec : Crypto.SecPar}

/-- Read one address from a configuration's heterogeneous store. -/
def get (configuration : Configuration family policy sec) (address : Address) :
    Option (family.State sec address) :=
  configuration.state address

/-- Store a state at an address known not to be corrupted. -/
def set
    (configuration : Configuration family policy sec) (address : Address)
    (state : family.State sec address)
    (honest : address ∉ configuration.corrupted) :
    Configuration family policy sec where
  state := configuration.state.set address state
  queue := configuration.queue
  corrupted := configuration.corrupted
  output := configuration.output
  trace := configuration.trace
  corruptionInvariant := by
    refine ⟨configuration.corruptionInvariant.1, ?_⟩
    intro other hcorrupted
    by_cases h : other = address
    · subst other
      exact (honest hcorrupted).elim
    · simpa [LocalStore.set, h] using
        configuration.corruptionInvariant.2 other hcorrupted

/-- Remove the state at one address while preserving corruption validity. -/
def remove
    (configuration : Configuration family policy sec) (address : Address) :
    Configuration family policy sec where
  state := configuration.state.remove address
  queue := configuration.queue
  corrupted := configuration.corrupted
  output := configuration.output
  trace := configuration.trace
  corruptionInvariant := by
    refine ⟨configuration.corruptionInvariant.1, ?_⟩
    intro other hcorrupted
    by_cases h : other = address
    · subst other
      simp [LocalStore.remove]
    · simpa [LocalStore.remove, h] using
        configuration.corruptionInvariant.2 other hcorrupted

/-- Append one kernel event to the tail of the FIFO queue. -/
def enqueueEvent
    (configuration : Configuration family policy sec)
    (event : QueuedEvent schema) : Configuration family policy sec :=
  { configuration with queue := configuration.queue ++ [event] }

/-- Append one activation to the tail of the FIFO queue. -/
def enqueue
    (configuration : Configuration family policy sec)
    (activation : QueuedActivation schema) : Configuration family policy sec :=
  configuration.enqueueEvent (.activation activation)

/-- Append one dynamic-corruption request to the same global FIFO. -/
def enqueueCorruption
    (configuration : Configuration family policy sec)
    (source target : Address) : Configuration family policy sec :=
  configuration.enqueueEvent (.corruptionRequest source target)

/-- Append several activations without changing their order. -/
def enqueueMany
    (configuration : Configuration family policy sec)
    (activations : List (QueuedActivation schema)) :
    Configuration family policy sec :=
  { configuration with
      queue := configuration.queue ++ activations.map QueuedEvent.activation }

/-- Remove the head activation, if one exists, and leave the remaining FIFO state. -/
def dequeue
    (configuration : Configuration family policy sec) :
    Option (QueuedEvent schema × Configuration family policy sec) :=
  match configuration.queue with
  | [] => none
  | activation :: remaining =>
      some (activation, { configuration with queue := remaining })

/-- Append one typed audit event. -/
def record
    (configuration : Configuration family policy sec)
    (event : TraceEvent family sec) : Configuration family policy sec :=
  { configuration with trace := configuration.trace ++ [event] }

/-- Record and expose the typed output that halts this configuration. -/
def finish
    (configuration : Configuration family policy sec)
    (result : MachineOutput family sec) : Configuration family policy sec :=
  { configuration with
      output := some result
      trace := configuration.trace ++ [.output result] }

/--
Commit one permitted dynamic corruption after its leakage has been computed.

The honest state is removed, the policy invariant advances, and the typed
leakage is retained in the audit trace.
-/
def markCorrupted
    (configuration : Configuration family policy sec) (target : Address)
    (leakage : family.Leakage sec target)
    (permitted : policy.mayCorrupt configuration.corrupted target) :
    Configuration family policy sec where
  state := configuration.state.remove target
  queue := configuration.queue
  corrupted := insert target configuration.corrupted
  output := configuration.output
  trace := configuration.trace ++ [.corrupted target leakage]
  corruptionInvariant := by
    refine ⟨policy.preserves configuration.corruptionInvariant.1 permitted, ?_⟩
    intro address hcorrupted
    rcases Finset.mem_insert.mp hcorrupted with h | h
    · subst address
      simp [LocalStore.remove]
    · by_cases hne : address = target
      · subst address
        simp [LocalStore.remove]
      · simpa [LocalStore.remove, hne] using
          configuration.corruptionInvariant.2 address h

/-- The corrupted-address set of every configuration satisfies its policy. -/
theorem corrupted_admissible
    (configuration : Configuration family policy sec) :
    policy.Admissible configuration.corrupted :=
  configuration.corruptionInvariant.1

/-- A corrupted address never retains honest local state. -/
@[simp] theorem get_eq_none_of_mem_corrupted
    (configuration : Configuration family policy sec) (address : Address)
    (hcorrupted : address ∈ configuration.corrupted) :
    configuration.get address = none :=
  configuration.corruptionInvariant.2 address hcorrupted

@[simp] theorem get_markCorrupted_same
    (configuration : Configuration family policy sec) (target : Address)
    (leakage : family.Leakage sec target)
    (permitted : policy.mayCorrupt configuration.corrupted target) :
    (configuration.markCorrupted target leakage permitted).get target = none := by
  change
    LocalStore.get (LocalStore.remove configuration.state target) target = none
  exact LocalStore.get_remove_same configuration.state target

@[simp] theorem mem_corrupted_markCorrupted
    (configuration : Configuration family policy sec) (target : Address)
    (leakage : family.Leakage sec target)
    (permitted : policy.mayCorrupt configuration.corrupted target) :
    target ∈ (configuration.markCorrupted target leakage permitted).corrupted := by
  simp [markCorrupted]

@[simp] theorem get_set_same
    (configuration : Configuration family policy sec) (address : Address)
    (state : family.State sec address)
    (honest : address ∉ configuration.corrupted) :
    get (configuration.set address state honest) address = some state := by
  change
    LocalStore.get (LocalStore.set configuration.state address state) address =
      some state
  exact LocalStore.get_set_same configuration.state address state

@[simp] theorem get_set_of_ne
    (configuration : Configuration family policy sec) {address other : Address}
    (state : family.State sec address)
    (honest : address ∉ configuration.corrupted) (hne : other ≠ address) :
    get (configuration.set address state honest) other = configuration.get other := by
  change
    LocalStore.get (LocalStore.set configuration.state address state) other =
      LocalStore.get configuration.state other
  exact LocalStore.get_set_of_ne configuration.state state hne

@[simp] theorem get_remove_same
    (configuration : Configuration family policy sec) (address : Address) :
    get (configuration.remove address) address = none := by
  change
    LocalStore.get (LocalStore.remove configuration.state address) address = none
  exact LocalStore.get_remove_same configuration.state address

@[simp] theorem get_remove_of_ne
    (configuration : Configuration family policy sec) {address other : Address}
    (hne : other ≠ address) :
    get (configuration.remove address) other = configuration.get other := by
  change
    LocalStore.get (LocalStore.remove configuration.state address) other =
      LocalStore.get configuration.state other
  exact LocalStore.get_remove_of_ne configuration.state hne

@[simp] theorem queue_enqueue
    (configuration : Configuration family policy sec)
    (activation : QueuedActivation schema) :
    (configuration.enqueue activation).queue =
      configuration.queue ++ [.activation activation] :=
  rfl

@[simp] theorem queue_enqueueCorruption
    (configuration : Configuration family policy sec)
    (source target : Address) :
    (configuration.enqueueCorruption source target).queue =
      configuration.queue ++ [.corruptionRequest source target] :=
  rfl

@[simp] theorem queue_enqueueMany
    (configuration : Configuration family policy sec)
    (activations : List (QueuedActivation schema)) :
    (configuration.enqueueMany activations).queue =
      configuration.queue ++ activations.map QueuedEvent.activation :=
  rfl

/-- Successive enqueue operations preserve their left-to-right order. -/
theorem queue_enqueue_pair
    (configuration : Configuration family policy sec)
    (first second : QueuedActivation schema) :
    (configuration.enqueue first |>.enqueue second).queue =
      configuration.queue ++ [.activation first, .activation second] := by
  simp [enqueue, enqueueEvent, List.append_assoc]

/-- Enqueuing into an empty queue makes that activation the next one dequeued. -/
theorem dequeue_enqueue_of_queue_eq_nil
    (configuration : Configuration family policy sec)
    (activation : QueuedActivation schema)
    (hqueue : configuration.queue = []) :
    dequeue (configuration.enqueue activation) =
      some (.activation activation, configuration) := by
  cases configuration
  simp_all [enqueue, enqueueEvent, dequeue]

/-- Appending work never overtakes the existing head of a nonempty queue. -/
theorem dequeue_enqueue_of_queue_eq_cons
    (configuration : Configuration family policy sec)
    (head : QueuedEvent schema) (tail : List (QueuedEvent schema))
    (activation : QueuedActivation schema)
    (hqueue : configuration.queue = head :: tail) :
    ∃ remaining,
      dequeue (configuration.enqueue activation) = some (head, remaining) ∧
        remaining.queue = tail ++ [.activation activation] := by
  cases configuration
  simp_all [enqueue, enqueueEvent, dequeue]

@[simp] theorem trace_record
    (configuration : Configuration family policy sec)
    (event : TraceEvent family sec) :
    (configuration.record event).trace = configuration.trace ++ [event] :=
  rfl

@[simp] theorem output_finish
    (configuration : Configuration family policy sec)
    (result : MachineOutput family sec) :
    (configuration.finish result).output = some result :=
  rfl

end Configuration

end Crypto.Infrastructure.UC

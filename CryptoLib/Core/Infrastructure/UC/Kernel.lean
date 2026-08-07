import CryptoLib.Core.Infrastructure.Computation.Algebra.Bounds
import CryptoLib.Core.Infrastructure.Computation.Algebra.Laws
import CryptoLib.Core.Infrastructure.Computation.Cost.PathBound
import CryptoLib.Core.Infrastructure.UC.Configuration

namespace CryptoLib.Core.Infrastructure.UC

open CryptoLib.Core.Infrastructure.Computation.Algebra
open CryptoLib.Core.Infrastructure.Computation.Cost

universe uCost uAddress uPayload uPort uCapability
universe uState uLeakage uErasure uOutput

/-- Structural operations performed by the global activation kernel. -/
inductive KernelPrimitive where
  | dequeue
  | initialize
  | readState
  | writeState
  | route
  | enqueue
  | erase
  | corrupt
  | finish
  deriving DecidableEq, Repr

/-- A typed kernel operation.  Every operation returns `Unit`. -/
inductive KernelOperation (Address : Type uAddress) : Type → Type (max uAddress 1) where
  | perform (primitive : KernelPrimitive) (addresses : List Address) :
      KernelOperation Address Unit

namespace KernelOperation

/-- The result-indexed signature of kernel bookkeeping operations. -/
def signature (Address : Type uAddress) : Signature.{0, max uAddress 1} where
  Op := KernelOperation Address

end KernelOperation

/-- The exact handler used to charge kernel bookkeeping. -/
abbrev KernelAlgebra (M : CostModel.{uCost}) (Address : Type uAddress) :=
  CostedAlgebra M (KernelOperation.signature Address)

namespace KernelAlgebra

variable (M : CostModel.{uCost}) (Address : Type uAddress)

/-- A named model in which abstract kernel bookkeeping is free. -/
noncomputable def zero :
    KernelAlgebra M Address where
  exec operation :=
    match operation with
    | .perform _primitive _addresses => RandCosted.pure M ()

/-- Erasing the zero-cost kernel handler gives a point mass at `Unit`. -/
noncomputable def zeroLaws :
    AlgebraLaws (zero M Address) where
  semantics operation :=
    match operation with
    | .perform _primitive _addresses => PMF.pure ()
  exec_spec operation := by
    cases operation
    exact RandCosted.valueDist_pure M ()

/-- Every operation of the free kernel handler has exact zero budget. -/
noncomputable def zeroBounds :
    OperationBounds (zero M Address) where
  budget _operation := M.instAddMonoid.zero
  cost_le operation := by
    cases operation
    exact RandCosted.CostBound.pure ()

/-- Execute and charge one structural kernel operation. -/
noncomputable def charge
    {M : CostModel.{uCost}} {Address : Type uAddress}
    (algebra : KernelAlgebra M Address)
    (primitive : KernelPrimitive) (addresses : List Address) :
    RandCosted M Unit :=
  algebra.exec (.perform primitive addresses)

/-- Sequence a charged kernel operation before a possibly higher-universe result. -/
noncomputable def withCharge
    {M : CostModel.{uCost}} {Address : Type uAddress} {Value : Type uOutput}
    (algebra : KernelAlgebra M Address)
    (primitive : KernelPrimitive) (addresses : List Address)
    (next : RandCosted M Value) : RandCosted M Value :=
  RandCosted.bind (charge algebra primitive addresses) (fun _unit => next)

end KernelAlgebra

variable {M : CostModel.{uCost}}
variable {Address : Type uAddress} [DecidableEq Address]
variable {schema : PortSchema.{uAddress, uPayload, uPort, uCapability} Address}
variable
  {family : ITMFamily.{uCost, uAddress, uPayload, uPort, uCapability,
    uState, uLeakage, uErasure, uOutput} M Address schema}
variable {policy : CorruptionPolicy Address}
variable {sec : CryptoLib.Core.SecPar}

/--
Typed wiring used when the kernel hands network control to the adversary.

These functions construct ordinary queued activations, so observation,
corrupted-party control, and leakage all remain explicit in the same FIFO.
-/
structure NetworkAdapter
    (family : ITMFamily.{uCost, uAddress, uPayload, uPort, uCapability,
      uState, uLeakage, uErasure, uOutput} M Address schema)
    (sec : CryptoLib.Core.SecPar) where
  observe : ∀ {source : Address},
    Emission schema source → QueuedActivation schema
  control : QueuedActivation schema → QueuedActivation schema
  leakage : (target : Address) →
    family.Leakage sec target → QueuedActivation schema

/-- One result of the single-activation kernel. -/
inductive KernelStepResult
    (family : ITMFamily.{uCost, uAddress, uPayload, uPort, uCapability,
      uState, uLeakage, uErasure, uOutput} M Address schema)
    (policy : CorruptionPolicy Address) (sec : CryptoLib.Core.SecPar) where
  | progressed (configuration : Configuration family policy sec)
  | halted (configuration : Configuration family policy sec)
  | deadlock (configuration : Configuration family policy sec)

namespace Kernel

/-- Classify a configuration after one action has been processed. -/
def classify
    (configuration : Configuration family policy sec) :
    KernelStepResult family policy sec :=
  if configuration.output.isSome then
    .halted configuration
  else
    .progressed configuration

/-- Enqueue a direct delivery, redirecting corrupted targets to the adversary. -/
noncomputable def enqueueDirect
    (algebra : KernelAlgebra M Address)
    (network : NetworkAdapter family sec)
    (configuration : Configuration family policy sec)
    (activation : QueuedActivation schema) :
    RandCosted M (Configuration family policy sec) :=
  KernelAlgebra.withCharge algebra .enqueue [activation.target] <|
    if activation.target ∈ configuration.corrupted then
      pure (configuration.enqueue (network.control activation))
    else
      pure (configuration.enqueue activation)

/--
Route an emission after the kernel has charged and authorized its source.

Keeping this core separate lets ordinary sends and `send-as` share exactly the
same delivery semantics without charging the routing primitive twice.
-/
noncomputable def routeEmissionCore
    (algebra : KernelAlgebra M Address)
    (network : NetworkAdapter family sec)
    (configuration : Configuration family policy sec)
    {source : Address} (emission : Emission schema source) :
    RandCosted M (Configuration family policy sec) :=
  let recorded := configuration.record (.emitted emission)
  match emission.routingPolicy.deliveryAuthority with
  | .kernel =>
      enqueueDirect algebra network recorded (.ofEmission emission)
  | .adversary =>
      KernelAlgebra.withCharge algebra .enqueue [source] <|
        pure (recorded.enqueue (network.observe emission))

/-- Route one ordinary emission according to its proof-carrying port capability. -/
noncomputable def routeEmission
    (algebra : KernelAlgebra M Address)
    (network : NetworkAdapter family sec)
    (configuration : Configuration family policy sec)
    {source : Address} (emission : Emission schema source) :
    RandCosted M (Configuration family policy sec) :=
  KernelAlgebra.withCharge algebra .route [source, emission.target.address] <|
    routeEmissionCore algebra network configuration emission

/--
Authorize and route an address-scoped `send-as` action.

The schema capability is the static half of the authorization.  The dynamic
half is membership of the claimed source in this exact configuration's
corrupted-address set.  A failed attempt is charged as routing work and
recorded, but cannot enqueue or expose the forged message.
-/
noncomputable def routeEmissionAs
    (algebra : KernelAlgebra M Address)
    (network : NetworkAdapter family sec)
    (configuration : Configuration family policy sec)
    (controller claimedSource : Address)
    (_authorization : schema.CanSendAs controller claimedSource)
    (emission : Emission schema claimedSource) :
    RandCosted M (Configuration family policy sec) :=
  KernelAlgebra.withCharge algebra .route
      [controller, claimedSource, emission.target.address] <|
    if claimedSource ∈ configuration.corrupted then
      routeEmissionCore algebra network
        (configuration.record (.sendAsAuthorized controller claimedSource)) emission
    else
      pure (configuration.record (.sendAsRejected controller claimedSource))

/-- Process the single action emitted by an honest ITM activation. -/
noncomputable def processAction
    (algebra : KernelAlgebra M Address)
    (network : NetworkAdapter family sec)
    (configuration : Configuration family policy sec)
    (source : Address)
    (honest : source ∉ configuration.corrupted)
    (state : family.State sec source)
    (action : LocalAction schema source
      (family.Erasure sec source) (family.Output sec source)) :
    RandCosted M (Configuration family policy sec) :=
  match action with
  | .yield =>
      pure (configuration.record (.yielded source))
  | .emit emission =>
      routeEmission algebra network configuration emission
  | .emitAs claimedSource authorization emission =>
      routeEmissionAs algebra network configuration source claimedSource
        authorization emission
  | .erase request =>
      KernelAlgebra.withCharge algebra .erase [source] <|
        RandCosted.bind
          (RandCosted.liftCosted (family.applyErasure sec source request state))
          (fun erased =>
            KernelAlgebra.withCharge algebra .writeState [source] <|
              let updated := configuration.set source erased honest
              let recorded := updated.record (.erased source request)
              KernelAlgebra.withCharge algebra .enqueue [source] <|
                pure (recorded.enqueue (.resume source)))
  | .spawn target initial =>
      let recorded := configuration.record (.spawned source target initial)
      KernelAlgebra.withCharge algebra .enqueue [target] <|
        pure (recorded.enqueue (.ofInput target initial))
  | .requestCorruption target =>
      KernelAlgebra.withCharge algebra .enqueue [source, target] <|
        pure (configuration.enqueueCorruption source target)
  | .output value =>
      KernelAlgebra.withCharge algebra .finish [source] <|
        pure (configuration.finish ⟨source, value⟩)

/--
Leak and commit a permitted corruption from one exact target state.

Both already-running and lazily initialized targets pass through this helper,
so leakage, state removal, the corrupted marker, and adversarial notification
have one authoritative order.
-/
noncomputable def corruptFromState
    (algebra : KernelAlgebra M Address)
    (network : NetworkAdapter family sec)
    (configuration : Configuration family policy sec)
    (source target : Address) (targetState : family.State sec target)
    (permitted : policy.mayCorrupt configuration.corrupted target) :
    RandCosted M (Configuration family policy sec) :=
  KernelAlgebra.withCharge algebra .corrupt [source, target] <|
    RandCosted.bind
      (RandCosted.liftCosted (family.leak sec target targetState))
      (fun leakage =>
        let corrupted := configuration.markCorrupted target leakage permitted
        KernelAlgebra.withCharge algebra .enqueue [target] <|
          pure (corrupted.enqueue (network.leakage target leakage)))

/--
Process one corruption request dequeued from the global FIFO.

A permitted dormant address is initialized through the family's exact `init`
handler before taking leakage.  Thus absence from the store means “not yet
activated”, not “immune to corruption”; both store cases subsequently use the
same exact corruption transition.
-/
noncomputable def processCorruption
    (algebra : KernelAlgebra M Address)
    (network : NetworkAdapter family sec)
    (configuration : Configuration family policy sec)
    (source target : Address) :
    RandCosted M (Configuration family policy sec) :=
  let requested := configuration.record (.corruptionRequested source target)
  KernelAlgebra.withCharge algebra .readState [target] <|
    letI := policy.decidableMayCorrupt requested.corrupted target
    if permitted : policy.mayCorrupt requested.corrupted target then
      match requested.get target with
      | some targetState =>
          corruptFromState algebra network requested source target targetState permitted
      | none =>
          KernelAlgebra.withCharge algebra .initialize [target] <|
            RandCosted.bind (family.init sec target) (fun targetState =>
              corruptFromState algebra network requested source target targetState permitted)
    else
      pure requested

/-- Activate one honest address, lazily initializing its typed local state. -/
noncomputable def activateHonest
    (algebra : KernelAlgebra M Address)
    (network : NetworkAdapter family sec)
    (configuration : Configuration family policy sec)
    (activation : QueuedActivation schema)
    (honest : activation.target ∉ configuration.corrupted) :
    RandCosted M (Configuration family policy sec) :=
  KernelAlgebra.withCharge algebra .readState [activation.target] <|
    let stateDist : RandCosted M (family.State sec activation.target) :=
      match configuration.get activation.target with
      | some state => pure state
      | none =>
          KernelAlgebra.withCharge algebra .initialize [activation.target] <|
            family.init sec activation.target
    RandCosted.bind stateDist (fun state =>
      RandCosted.bind
        (family.activate sec activation.target state activation.input)
        (fun result =>
          KernelAlgebra.withCharge algebra .writeState [activation.target] <|
            let updated := configuration.set activation.target result.state honest
            processAction algebra network updated activation.target honest
              result.state result.action))

/-- Consume exactly one queued activation. -/
noncomputable def stepOne
    (algebra : KernelAlgebra M Address)
    (network : NetworkAdapter family sec)
    (configuration : Configuration family policy sec) :
    RandCosted M (KernelStepResult family policy sec) :=
  if configuration.output.isSome then
    pure (.halted configuration)
  else KernelAlgebra.withCharge algebra .dequeue [] <| do
    match configuration.dequeue with
    | none => pure (.deadlock configuration)
    | some (event, remaining) =>
        match event with
        | .activation activation =>
            let recorded := remaining.record (.activated activation)
            if corrupted : activation.target ∈ recorded.corrupted then do
              let redirected ← enqueueDirect algebra network recorded
                (network.control activation)
              pure (classify redirected)
            else do
              let updated ← activateHonest algebra network recorded activation corrupted
              pure (classify updated)
        | .corruptionRequest source target => do
            let updated ← processCorruption algebra network remaining source target
            pure (classify updated)

/-- The observable reason a finite execution stopped. -/
inductive ExecutionOutcome
    (family : ITMFamily.{uCost, uAddress, uPayload, uPort, uCapability,
      uState, uLeakage, uErasure, uOutput} M Address schema)
    (sec : CryptoLib.Core.SecPar) where
  | output (result : MachineOutput family sec)
  | timeout
  | deadlock

/-- An outcome together with the exact final configuration and audit trace. -/
structure ExecutionResult
    (family : ITMFamily.{uCost, uAddress, uPayload, uPort, uCapability,
      uState, uLeakage, uErasure, uOutput} M Address schema)
    (policy : CorruptionPolicy Address) (sec : CryptoLib.Core.SecPar) where
  outcome : ExecutionOutcome family sec
  configuration : Configuration family policy sec

/-- Read an already-produced output or report timeout at fuel zero. -/
def atFuelZero
    (configuration : Configuration family policy sec) :
    ExecutionResult family policy sec :=
  match configuration.output with
  | some result => ⟨.output result, configuration⟩
  | none => ⟨.timeout, configuration⟩

/--
Run a finite prefix of the FIFO scheduler, accumulating exact component and
kernel costs once through `RandCosted.bind`.
-/
noncomputable def runCosted
    (algebra : KernelAlgebra M Address)
    (network : NetworkAdapter family sec) :
    Nat → Configuration family policy sec →
      RandCosted M (ExecutionResult family policy sec)
  | 0, configuration => pure (atFuelZero configuration)
  | fuel + 1, configuration =>
      match configuration.output with
      | some result => pure ⟨.output result, configuration⟩
      | none => do
          let step ← stepOne algebra network configuration
          match step with
          | .progressed updated => runCosted algebra network fuel updated
          | .halted updated =>
              match updated.output with
              | some result => pure ⟨.output result, updated⟩
              | none => pure ⟨ExecutionOutcome.deadlock, updated⟩
          | .deadlock updated => pure ⟨ExecutionOutcome.deadlock, updated⟩

/-- Interpret an output as a Boolean decision; timeout and deadlock are false. -/
def ExecutionOutcome.toBool
    (decide : (result : MachineOutput family sec) → Bool)
    (outcome : ExecutionOutcome family sec) : Bool :=
  match outcome with
  | .output result => decide result
  | .timeout | .deadlock => false

/-- The total Boolean game is defined only by erasing the exact runner. -/
noncomputable def decisionDist
    (algebra : KernelAlgebra M Address)
    (network : NetworkAdapter family sec)
    (decide : (result : MachineOutput family sec) → Bool)
    (fuel : Nat) (configuration : Configuration family policy sec) : PMF Bool :=
  PMF.map (fun result => result.outcome.toBool decide)
    (RandCosted.valueDist (runCosted algebra network fuel configuration))

end Kernel

end CryptoLib.Core.Infrastructure.UC

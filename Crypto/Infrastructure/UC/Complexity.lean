import Crypto.Infrastructure.Asymptotic.Bounds
import Crypto.Infrastructure.Complexity.Machine
import Crypto.Infrastructure.UC.Kernel

namespace Crypto.Infrastructure.UC

open Crypto.Infrastructure.Asymptotic
open Crypto.Infrastructure.Complexity
open Crypto.Infrastructure.Computation.Algebra
open Crypto.Infrastructure.Computation.Cost

universe uCost uAddress uPayload uPort uCapability
universe uState uLeakage uErasure uOutput uBoundFirst uBoundNext uBoundValue

variable {M : CostModel.{uCost}}
variable {Address : Type uAddress} [DecidableEq Address]
variable {schema : PortSchema.{uAddress, uPayload, uPort, uCapability} Address}
variable
  {family : ITMFamily.{uCost, uAddress, uPayload, uPort, uCapability,
    uState, uLeakage, uErasure, uOutput} M Address schema}
variable {policy : CorruptionPolicy Address}

/-- Independent exact budgets for the four component-owned handlers. -/
structure ComponentCostCertificate
    (family : ITMFamily.{uCost, uAddress, uPayload, uPort, uCapability,
      uState, uLeakage, uErasure, uOutput} M Address schema) where
  initBudget : Crypto.SecPar → Address → M.Cost
  activationBudget : Crypto.SecPar → Address → M.Cost
  erasureBudget : Crypto.SecPar → Address → M.Cost
  leakageBudget : Crypto.SecPar → Address → M.Cost
  init_sound : ∀ sec address,
    RandCosted.CostBound (family.init sec address) (initBudget sec address)
  activation_sound : ∀ sec address state input,
    RandCosted.CostBound (family.activate sec address state input)
      (activationBudget sec address)
  erasure_sound : ∀ sec address request state,
    M.instPartialOrder.le (family.applyErasure sec address request state).cost
      (erasureBudget sec address)
  leakage_sound : ∀ sec address state,
    M.instPartialOrder.le (family.leak sec address state).cost
      (leakageBudget sec address)

/-- Repeated left-to-right use of one common activation budget. -/
abbrev repeatActivationCost
    (M : CostModel.{uCost}) (count : Nat) (budget : M.Cost) : M.Cost :=
  M.instAddMonoid.toNatSMul.smul count budget

@[simp] theorem repeatActivationCost_zero
    (M : CostModel.{uCost}) (budget : M.Cost) :
    repeatActivationCost M 0 budget = M.instAddMonoid.zero := by
  letI := M.instAddMonoid
  exact zero_nsmul budget

theorem repeatActivationCost_succ
    (M : CostModel.{uCost}) (count : Nat) (budget : M.Cost) :
    repeatActivationCost M (count + 1) budget =
      M.instAddMonoid.add budget (repeatActivationCost M count budget) := by
  letI := M.instAddMonoid
  exact succ_nsmul' budget count

/-- Repeating a budget across two consecutive segments preserves their order. -/
theorem repeatActivationCost_add
    (M : CostModel.{uCost}) (first second : Nat) (budget : M.Cost) :
    repeatActivationCost M (first + second) budget =
      M.instAddMonoid.add
        (repeatActivationCost M first budget)
        (repeatActivationCost M second budget) := by
  letI := M.instAddMonoid
  exact add_nsmul budget first second

/-- Zero is below every repeated budget when it is below one use. -/
theorem zero_le_repeatActivationCost
    (M : CostModel.{uCost}) {budget : M.Cost}
    (zero_le : M.instPartialOrder.le M.instAddMonoid.zero budget) :
    ∀ count, M.instPartialOrder.le M.instAddMonoid.zero
      (repeatActivationCost M count budget) := by
  letI := M.instAddMonoid
  letI := M.instPartialOrder
  letI := M.instAddLeftMono
  letI := M.instAddRightMono
  intro count
  induction count with
  | zero =>
      simpa only [repeatActivationCost_zero] using
        (M.instPartialOrder.le_refl M.instAddMonoid.zero)
  | succ count ih =>
      rw [repeatActivationCost_succ]
      calc
        M.instAddMonoid.zero ≤ budget := zero_le
        _ = M.instAddMonoid.add budget M.instAddMonoid.zero := by
          exact (M.instAddMonoid.add_zero budget).symm
        _ ≤ M.instAddMonoid.add budget
            (repeatActivationCost M count budget) :=
          add_le_add_right ih budget

/-- Padding with additional nonnegative atomic charges only enlarges a budget. -/
theorem repeatActivationCost_mono_count
    (M : CostModel.{uCost}) {budget : M.Cost}
    (zero_le : M.instPartialOrder.le M.instAddMonoid.zero budget)
    {used available : Nat} (used_le : used ≤ available) :
    M.instPartialOrder.le
      (repeatActivationCost M used budget)
      (repeatActivationCost M available budget) := by
  letI := M.instAddMonoid
  letI := M.instPartialOrder
  letI := M.instAddLeftMono
  letI := M.instAddRightMono
  induction available with
  | zero =>
      have used_zero : used = 0 := Nat.eq_zero_of_le_zero used_le
      subst used
      exact M.instPartialOrder.le_refl _
  | succ available inductionHypothesis =>
      by_cases used_le_available : used ≤ available
      · calc
          repeatActivationCost M used budget ≤
              repeatActivationCost M available budget :=
            inductionHypothesis used_le_available
          _ ≤ repeatActivationCost M (available + 1) budget := by
            rw [repeatActivationCost_succ]
            calc
              repeatActivationCost M available budget =
                  M.instAddMonoid.add M.instAddMonoid.zero
                    (repeatActivationCost M available budget) := by
                    exact (M.instAddMonoid.zero_add _).symm
              _ ≤ M.instAddMonoid.add budget
                    (repeatActivationCost M available budget) :=
                  add_le_add_left zero_le _
      · have used_eq : used = available + 1 := by omega
        subst used
        exact M.instPartialOrder.le_refl _

/--
Auditable atomic bounds from which the one-step kernel budget is derived.

Every component handler and structural kernel operation is bounded by the same
security-parameter-dependent atom.  The theorem `step_sound` below follows by
structural composition of these fields; it is not independent evidence.
-/
structure StepCostCertificate
    (algebra : KernelAlgebra M Address)
    (network : (sec : Crypto.SecPar) → NetworkAdapter family sec) where
  component : ComponentCostCertificate family
  kernel : OperationBounds algebra
  atomBudget : Crypto.SecPar → M.Cost
  zero_le_atomBudget : ∀ sec,
    M.instPartialOrder.le M.instAddMonoid.zero (atomBudget sec)
  initBudget_le : ∀ sec address,
    M.instPartialOrder.le (component.initBudget sec address) (atomBudget sec)
  activationBudget_le : ∀ sec address,
    M.instPartialOrder.le (component.activationBudget sec address) (atomBudget sec)
  erasureBudget_le : ∀ sec address,
    M.instPartialOrder.le (component.erasureBudget sec address) (atomBudget sec)
  leakageBudget_le : ∀ sec address,
    M.instPartialOrder.le (component.leakageBudget sec address) (atomBudget sec)
  kernelBudget_le : ∀ sec {Result : Type}
      (operation : KernelOperation Address Result),
    M.instPartialOrder.le (kernel.budget operation) (atomBudget sec)

namespace StepCostCertificate

variable {algebra : KernelAlgebra M Address}
variable {network : (sec : Crypto.SecPar) → NetworkAdapter family sec}

/-- The largest number of component/kernel atoms in one `Kernel.stepOne` path. -/
def maximumAtomicCharges : Nat := 10

/-- The derived common budget for one complete kernel activation. -/
def budget
    (certificate : StepCostCertificate algebra network)
    (sec : Crypto.SecPar) : M.Cost :=
  repeatActivationCost M maximumAtomicCharges (certificate.atomBudget sec)

omit [DecidableEq Address] in
/-- The derived step budget is nonnegative. -/
theorem zero_le_budget
    (certificate : StepCostCertificate algebra network)
    (sec : Crypto.SecPar) :
    M.instPartialOrder.le M.instAddMonoid.zero (certificate.budget sec) :=
  zero_le_repeatActivationCost M (certificate.zero_le_atomBudget sec) _

omit [DecidableEq Address] in
private theorem pure_sound
    (certificate : StepCostCertificate algebra network)
    (sec : Crypto.SecPar) (count : Nat) {Value : Type uBoundValue} (value : Value) :
    RandCosted.CostBound (RandCosted.pure M value)
      (repeatActivationCost M count (certificate.atomBudget sec)) := by
  apply RandCosted.CostBound.weaken (RandCosted.CostBound.pure value)
  exact zero_le_repeatActivationCost M
    (certificate.zero_le_atomBudget sec) count

omit [DecidableEq Address] in
private theorem bind_sound
    (certificate : StepCostCertificate algebra network)
    (sec : Crypto.SecPar) {First : Type uBoundFirst} {Next : Type uBoundNext}
    {first : RandCosted M First} {next : First → RandCosted M Next}
    (firstCount nextCount : Nat)
    (firstBound : RandCosted.CostBound first
      (repeatActivationCost M firstCount (certificate.atomBudget sec)))
    (nextBound : ∀ value, RandCosted.CostBound (next value)
      (repeatActivationCost M nextCount (certificate.atomBudget sec))) :
    RandCosted.CostBound (RandCosted.bind first next)
      (repeatActivationCost M (firstCount + nextCount)
        (certificate.atomBudget sec)) := by
  rw [repeatActivationCost_add]
  exact RandCosted.CostBound.bind firstBound nextBound

omit [DecidableEq Address] in
private theorem pad_sound
    (certificate : StepCostCertificate algebra network)
    (sec : Crypto.SecPar) {Value : Type uBoundValue} {dist : RandCosted M Value}
    {used available : Nat}
    (bound : RandCosted.CostBound dist
      (repeatActivationCost M used (certificate.atomBudget sec)))
    (used_le : used ≤ available) :
    RandCosted.CostBound dist
      (repeatActivationCost M available (certificate.atomBudget sec)) := by
  apply RandCosted.CostBound.weaken bound
  exact repeatActivationCost_mono_count M
    (certificate.zero_le_atomBudget sec) used_le

omit [DecidableEq Address] in
private theorem init_sound
    (certificate : StepCostCertificate algebra network)
    (sec : Crypto.SecPar) (address : Address) :
    RandCosted.CostBound (family.init sec address)
      (repeatActivationCost M 1 (certificate.atomBudget sec)) := by
  letI := M.instAddMonoid
  letI := M.instPartialOrder
  apply RandCosted.CostBound.weaken
    (certificate.component.init_sound sec address)
  calc
    certificate.component.initBudget sec address ≤ certificate.atomBudget sec :=
      certificate.initBudget_le sec address
    _ = repeatActivationCost M 1 (certificate.atomBudget sec) :=
      (one_nsmul _).symm

omit [DecidableEq Address] in
private theorem activation_sound
    (certificate : StepCostCertificate algebra network)
    (sec : Crypto.SecPar) (address : Address)
    (state : family.State sec address) (input : ActivationInput schema address) :
    RandCosted.CostBound (family.activate sec address state input)
      (repeatActivationCost M 1 (certificate.atomBudget sec)) := by
  letI := M.instAddMonoid
  letI := M.instPartialOrder
  apply RandCosted.CostBound.weaken
    (certificate.component.activation_sound sec address state input)
  calc
    certificate.component.activationBudget sec address ≤ certificate.atomBudget sec :=
      certificate.activationBudget_le sec address
    _ = repeatActivationCost M 1 (certificate.atomBudget sec) :=
      (one_nsmul _).symm

omit [DecidableEq Address] in
private theorem erasure_sound
    (certificate : StepCostCertificate algebra network)
    (sec : Crypto.SecPar) (address : Address)
    (request : family.Erasure sec address) (state : family.State sec address) :
    RandCosted.CostBound
      (RandCosted.liftCosted (family.applyErasure sec address request state))
      (repeatActivationCost M 1 (certificate.atomBudget sec)) := by
  letI := M.instAddMonoid
  letI := M.instPartialOrder
  intro result hresult
  rw [PMF.mem_support_pure_iff] at hresult
  subst result
  calc
    (family.applyErasure sec address request state).cost ≤
        certificate.component.erasureBudget sec address :=
      certificate.component.erasure_sound sec address request state
    _ ≤ certificate.atomBudget sec := certificate.erasureBudget_le sec address
    _ = repeatActivationCost M 1 (certificate.atomBudget sec) := by
      letI := M.instAddMonoid
      exact (one_nsmul _).symm

omit [DecidableEq Address] in
private theorem leakage_sound
    (certificate : StepCostCertificate algebra network)
    (sec : Crypto.SecPar) (address : Address) (state : family.State sec address) :
    RandCosted.CostBound (RandCosted.liftCosted (family.leak sec address state))
      (repeatActivationCost M 1 (certificate.atomBudget sec)) := by
  letI := M.instAddMonoid
  letI := M.instPartialOrder
  intro result hresult
  rw [PMF.mem_support_pure_iff] at hresult
  subst result
  calc
    (family.leak sec address state).cost ≤
        certificate.component.leakageBudget sec address :=
      certificate.component.leakage_sound sec address state
    _ ≤ certificate.atomBudget sec := certificate.leakageBudget_le sec address
    _ = repeatActivationCost M 1 (certificate.atomBudget sec) := by
      letI := M.instAddMonoid
      exact (one_nsmul _).symm

omit [DecidableEq Address] in
private theorem charge_sound
    (certificate : StepCostCertificate algebra network)
    (sec : Crypto.SecPar) (primitive : KernelPrimitive) (addresses : List Address) :
    RandCosted.CostBound (KernelAlgebra.charge algebra primitive addresses)
      (repeatActivationCost M 1 (certificate.atomBudget sec)) := by
  letI := M.instAddMonoid
  letI := M.instPartialOrder
  intro result hresult
  calc
    result.cost ≤ certificate.kernel.budget (.perform primitive addresses) :=
      certificate.kernel.cost_le (.perform primitive addresses) result hresult
    _ ≤ certificate.atomBudget sec :=
      certificate.kernelBudget_le sec (.perform primitive addresses)
    _ = repeatActivationCost M 1 (certificate.atomBudget sec) := by
      letI := M.instAddMonoid
      exact (one_nsmul _).symm

omit [DecidableEq Address] in
private theorem withCharge_sound
    (certificate : StepCostCertificate algebra network)
    (sec : Crypto.SecPar) (primitive : KernelPrimitive) (addresses : List Address)
    {Value : Type uBoundValue} {next : RandCosted M Value} (nextCount : Nat)
    (nextBound : RandCosted.CostBound next
      (repeatActivationCost M nextCount (certificate.atomBudget sec))) :
    RandCosted.CostBound
      (KernelAlgebra.withCharge algebra primitive addresses next)
      (repeatActivationCost M (nextCount + 1) (certificate.atomBudget sec)) := by
  unfold KernelAlgebra.withCharge
  simpa only [Nat.add_comm] using
    bind_sound certificate sec 1 nextCount
      (charge_sound certificate sec primitive addresses) (fun _unit => nextBound)

private theorem enqueueDirect_sound
    (certificate : StepCostCertificate algebra network)
    (sec : Crypto.SecPar) (configuration : Configuration family policy sec)
    (activation : QueuedActivation schema) :
    RandCosted.CostBound
      (Kernel.enqueueDirect algebra (network sec) configuration activation)
      (repeatActivationCost M 1 (certificate.atomBudget sec)) := by
  unfold Kernel.enqueueDirect
  apply withCharge_sound certificate sec .enqueue [activation.target] 0
  split <;> exact pure_sound certificate sec 0 _

private theorem routeEmissionCore_sound
    (certificate : StepCostCertificate algebra network)
    (sec : Crypto.SecPar) (configuration : Configuration family policy sec)
    {source : Address} (emission : Emission schema source) :
    RandCosted.CostBound
      (Kernel.routeEmissionCore algebra (network sec) configuration emission)
      (repeatActivationCost M 1 (certificate.atomBudget sec)) := by
  unfold Kernel.routeEmissionCore
  cases emission.routingPolicy.deliveryAuthority <;> simp only
  · exact enqueueDirect_sound certificate sec _ _
  · apply withCharge_sound certificate sec .enqueue [source] 0
    exact pure_sound certificate sec 0 _

private theorem routeEmission_sound
    (certificate : StepCostCertificate algebra network)
    (sec : Crypto.SecPar) (configuration : Configuration family policy sec)
    {source : Address} (emission : Emission schema source) :
    RandCosted.CostBound
      (Kernel.routeEmission algebra (network sec) configuration emission)
      (repeatActivationCost M 2 (certificate.atomBudget sec)) := by
  unfold Kernel.routeEmission
  exact withCharge_sound certificate sec .route
    [source, emission.target.address] 1
    (routeEmissionCore_sound certificate sec configuration emission)

private theorem routeEmissionAs_sound
    (certificate : StepCostCertificate algebra network)
    (sec : Crypto.SecPar) (configuration : Configuration family policy sec)
    (controller claimedSource : Address)
    (authorization : schema.CanSendAs controller claimedSource)
    (emission : Emission schema claimedSource) :
    RandCosted.CostBound
      (Kernel.routeEmissionAs algebra (network sec) configuration controller
        claimedSource authorization emission)
      (repeatActivationCost M 2 (certificate.atomBudget sec)) := by
  unfold Kernel.routeEmissionAs
  apply withCharge_sound certificate sec .route
    [controller, claimedSource, emission.target.address] 1
  split
  · exact routeEmissionCore_sound certificate sec _ emission
  · apply pad_sound certificate sec (pure_sound certificate sec 0 _) (by omega)

private theorem processAction_sound
    (certificate : StepCostCertificate algebra network)
    (sec : Crypto.SecPar) (configuration : Configuration family policy sec)
    (source : Address) (honest : source ∉ configuration.corrupted)
    (state : family.State sec source)
    (action : LocalAction schema source
      (family.Erasure sec source) (family.Output sec source)) :
    RandCosted.CostBound
      (Kernel.processAction algebra (network sec) configuration source honest state action)
      (repeatActivationCost M 4 (certificate.atomBudget sec)) := by
  cases action with
  | yield =>
      simp only [Kernel.processAction]
      exact pad_sound certificate sec (pure_sound certificate sec 0 _) (by omega)
  | emit emission =>
      simp only [Kernel.processAction]
      exact pad_sound certificate sec
        (routeEmission_sound certificate sec configuration emission) (by omega)
  | emitAs claimedSource authorization emission =>
      simp only [Kernel.processAction]
      exact pad_sound certificate sec
        (routeEmissionAs_sound certificate sec configuration source claimedSource
          authorization emission) (by omega)
  | erase request =>
      simp only [Kernel.processAction]
      apply withCharge_sound certificate sec .erase [source] 3
      apply bind_sound certificate sec 1 2
        (erasure_sound certificate sec source request state)
      intro erased
      apply withCharge_sound certificate sec .writeState [source] 1
      apply withCharge_sound certificate sec .enqueue [source] 0
      exact pure_sound certificate sec 0 _
  | spawn target initial =>
      simp only [Kernel.processAction]
      apply pad_sound certificate sec
        (withCharge_sound certificate sec .enqueue [target] 0
          (pure_sound certificate sec 0 _)) (by omega)
  | requestCorruption target =>
      simp only [Kernel.processAction]
      apply pad_sound certificate sec
        (withCharge_sound certificate sec .enqueue [source, target] 0
          (pure_sound certificate sec 0 _)) (by omega)
  | output value =>
      simp only [Kernel.processAction]
      apply pad_sound certificate sec
        (withCharge_sound certificate sec .finish [source] 0
          (pure_sound certificate sec 0 _)) (by omega)

private theorem corruptFromState_sound
    (certificate : StepCostCertificate algebra network)
    (sec : Crypto.SecPar) (configuration : Configuration family policy sec)
    (source target : Address) (targetState : family.State sec target)
    (permitted : policy.mayCorrupt configuration.corrupted target) :
    RandCosted.CostBound
      (Kernel.corruptFromState algebra (network sec) configuration source target
        targetState permitted)
      (repeatActivationCost M 3 (certificate.atomBudget sec)) := by
  unfold Kernel.corruptFromState
  apply withCharge_sound certificate sec .corrupt [source, target] 2
  apply bind_sound certificate sec 1 1
    (leakage_sound certificate sec target targetState)
  intro leakage
  apply withCharge_sound certificate sec .enqueue [target] 0
  exact pure_sound certificate sec 0 _

private theorem processCorruption_sound
    (certificate : StepCostCertificate algebra network)
    (sec : Crypto.SecPar) (configuration : Configuration family policy sec)
    (source target : Address) :
    RandCosted.CostBound
      (Kernel.processCorruption algebra (network sec) configuration source target)
      (repeatActivationCost M 6 (certificate.atomBudget sec)) := by
  unfold Kernel.processCorruption
  apply withCharge_sound certificate sec .readState [target] 5
  dsimp only
  split
  · split
    · exact pad_sound certificate sec
        (corruptFromState_sound certificate sec _ source target _ _) (by omega)
    · apply withCharge_sound certificate sec .initialize [target] 4
      apply bind_sound certificate sec 1 3
        (init_sound certificate sec target)
      intro targetState
      exact corruptFromState_sound certificate sec _ source target targetState _
  · exact pad_sound certificate sec (pure_sound certificate sec 0 _) (by omega)

private theorem activateHonest_sound
    (certificate : StepCostCertificate algebra network)
    (sec : Crypto.SecPar) (configuration : Configuration family policy sec)
    (activation : QueuedActivation schema)
    (honest : activation.target ∉ configuration.corrupted) :
    RandCosted.CostBound
      (Kernel.activateHonest algebra (network sec) configuration activation honest)
      (repeatActivationCost M 9 (certificate.atomBudget sec)) := by
  unfold Kernel.activateHonest
  apply withCharge_sound certificate sec .readState [activation.target] 8
  apply bind_sound certificate sec 2 6
  · split
    · exact pad_sound certificate sec (pure_sound certificate sec 0 _) (by omega)
    · apply withCharge_sound certificate sec .initialize [activation.target] 1
      exact init_sound certificate sec activation.target
  · intro state
    apply bind_sound certificate sec 1 5
      (activation_sound certificate sec activation.target state activation.input)
    intro result
    apply withCharge_sound certificate sec .writeState [activation.target] 4
    exact processAction_sound certificate sec
      (configuration.set activation.target result.state honest)
      activation.target honest
      result.state result.action

/--
The complete one-step bound derived solely from component and kernel bounds.

The proof follows the actual interpreter branches and pads shorter paths with
the nonnegative atomic budget.  Sequential costs remain in execution order.
-/
theorem step_sound
    (certificate : StepCostCertificate algebra network)
    (sec : Crypto.SecPar) (configuration : Configuration family policy sec) :
    RandCosted.CostBound
      (Kernel.stepOne algebra (network sec) configuration) (certificate.budget sec) := by
  unfold budget maximumAtomicCharges
  unfold Kernel.stepOne
  split
  · exact pad_sound certificate sec (pure_sound certificate sec 0 _) (by omega)
  · apply withCharge_sound certificate sec .dequeue [] 9
    split
    · exact pad_sound certificate sec (pure_sound certificate sec 0 _) (by omega)
    · split
      · dsimp only
        split
        · apply pad_sound certificate sec (available := 9)
            (bind_sound certificate sec 1 0
              (enqueueDirect_sound certificate sec _ _) (fun redirected =>
                pure_sound certificate sec 0 (Kernel.classify redirected))) (by omega)
        · exact bind_sound certificate sec 9 0
            (activateHonest_sound certificate sec _ _ _) (fun updated =>
              pure_sound certificate sec 0 (Kernel.classify updated))
      · apply pad_sound certificate sec (available := 9)
          (bind_sound certificate sec 6 0
            (processCorruption_sound certificate sec _ _ _) (fun updated =>
              pure_sound certificate sec 0 (Kernel.classify updated))) (by omega)

/-- Every fuel-bounded exact execution costs at most one common budget per step. -/
theorem runCosted_sound
    (certificate : StepCostCertificate algebra network) :
    ∀ (fuel : Nat) (sec : Crypto.SecPar)
      (configuration : Configuration family policy sec),
      RandCosted.CostBound
        (Kernel.runCosted algebra (network sec) fuel configuration)
        (repeatActivationCost M fuel (certificate.budget sec)) := by
  intro fuel
  induction fuel with
  | zero =>
      intro sec configuration
      simpa [Kernel.runCosted] using
        (RandCosted.CostBound.pure (Kernel.atFuelZero configuration))
  | succ fuel inductionHypothesis =>
      intro sec configuration
      rw [repeatActivationCost_succ]
      simp only [Kernel.runCosted]
      split
      · apply RandCosted.CostBound.weaken
          (RandCosted.CostBound.pure _)
        simpa only [repeatActivationCost_succ] using
          zero_le_repeatActivationCost M
            (certificate.zero_le_budget sec) (fuel + 1)
      · apply RandCosted.CostBound.bind (certificate.step_sound sec configuration)
        intro step
        cases step with
        | progressed updated =>
            exact inductionHypothesis sec updated
        | halted updated =>
            simp only
            cases updated.output with
            | none =>
                change RandCosted.CostBound
                  (pure ({
                    outcome := Kernel.ExecutionOutcome.deadlock
                    configuration := updated } :
                    Kernel.ExecutionResult family policy sec))
                  (repeatActivationCost M fuel (certificate.budget sec))
                apply RandCosted.CostBound.weaken
                    (RandCosted.CostBound.pure _)
                exact zero_le_repeatActivationCost M
                  (certificate.zero_le_budget sec) fuel
            | some result =>
                change RandCosted.CostBound
                  (pure ({
                    outcome := Kernel.ExecutionOutcome.output result
                    configuration := updated } :
                    Kernel.ExecutionResult family policy sec))
                  (repeatActivationCost M fuel (certificate.budget sec))
                apply RandCosted.CostBound.weaken
                    (RandCosted.CostBound.pure _)
                exact zero_le_repeatActivationCost M
                  (certificate.zero_le_budget sec) fuel
        | deadlock updated =>
            apply RandCosted.CostBound.weaken
                (RandCosted.CostBound.pure _)
            exact zero_le_repeatActivationCost M
              (certificate.zero_le_budget sec) fuel

end StepCostCertificate

/-- Semantic evidence that a selected fuel is sufficient and stable. -/
structure FuelCertificate
    (algebra : KernelAlgebra M Address)
    (network : (sec : Crypto.SecPar) → NetworkAdapter family sec)
    (initial : (sec : Crypto.SecPar) → Configuration family policy sec)
    (fuel : Crypto.SecPar → Nat) where
  noTimeout : ∀ sec result, result ∈
      (Kernel.runCosted algebra (network sec) (fuel sec) (initial sec)).support →
      result.val.outcome ≠ Kernel.ExecutionOutcome.timeout
  stable : ∀ sec extra,
    RandCosted.valueDist
        (Kernel.runCosted algebra (network sec) (fuel sec + extra) (initial sec)) =
      RandCosted.valueDist
        (Kernel.runCosted algebra (network sec) (fuel sec) (initial sec))

namespace FuelCertificate

variable {algebra : KernelAlgebra M Address}
variable {network : (sec : Crypto.SecPar) → NetworkAdapter family sec}
variable {initial : (sec : Crypto.SecPar) → Configuration family policy sec}
variable {fuel larger : Crypto.SecPar → Nat}

/--
No-timeout and stability evidence extends to any pointwise larger fuel.

The proof uses value erasure only to transport support membership between the
stable executions.  It does not alter the exact runner or use a cost
certificate to accept or reject an execution path.
-/
noncomputable def extend
    (certificate : FuelCertificate (policy := policy) algebra network initial fuel)
    (fuel_le : ∀ sec, fuel sec ≤ larger sec) :
    FuelCertificate (policy := policy) algebra network initial larger where
  noTimeout := by
    intro sec result hresult
    let extra := larger sec - fuel sec
    have fuel_add_extra : fuel sec + extra = larger sec :=
      Nat.add_sub_of_le (fuel_le sec)
    have value_mem_larger : result.val ∈
        (RandCosted.valueDist
          (Kernel.runCosted algebra (network sec) (larger sec) (initial sec))).support := by
      rw [RandCosted.valueDist, PMF.mem_support_map_iff]
      exact ⟨result, hresult, rfl⟩
    have value_mem_base : result.val ∈
        (RandCosted.valueDist
          (Kernel.runCosted algebra (network sec) (fuel sec) (initial sec))).support := by
      rw [← certificate.stable sec extra]
      simpa only [fuel_add_extra] using value_mem_larger
    rw [RandCosted.valueDist, PMF.mem_support_map_iff] at value_mem_base
    rcases value_mem_base with ⟨baseResult, hbaseResult, hvalue⟩
    have base_no_timeout :=
      certificate.noTimeout sec baseResult hbaseResult
    simpa only [hvalue] using base_no_timeout
  stable := by
    intro sec extra
    let difference := larger sec - fuel sec
    have fuel_add_difference : fuel sec + difference = larger sec :=
      Nat.add_sub_of_le (fuel_le sec)
    calc
      RandCosted.valueDist
          (Kernel.runCosted algebra (network sec) (larger sec + extra) (initial sec)) =
        RandCosted.valueDist
          (Kernel.runCosted algebra (network sec) (fuel sec) (initial sec)) := by
            simpa only [← fuel_add_difference, Nat.add_assoc] using
              certificate.stable sec (difference + extra)
      _ = RandCosted.valueDist
          (Kernel.runCosted algebra (network sec) (larger sec) (initial sec)) := by
            simpa only [fuel_add_difference] using
              (certificate.stable sec difference).symm

end FuelCertificate

/--
Exact, measured, and polynomial annotations for a closed-world runner, together
with independent operational admission of that same runner and runtime.
-/
structure PPTExecutionCertificate
    (measure : NatMeasure M)
    (algebra : KernelAlgebra M Address)
    (network : (sec : Crypto.SecPar) → NetworkAdapter family sec)
    (initial : (sec : Crypto.SecPar) → Configuration family policy sec) where
  step : StepCostCertificate algebra network
  activationLimit : Crypto.SecPar → Nat
  stepRuntime : Crypto.SecPar → Nat
  budget_le_stepRuntime : ∀ sec,
    measure (step.budget sec) ≤ stepRuntime sec
  activationLimit_isPoly : IsPolyBounded activationLimit
  stepRuntime_isPoly : IsPolyBounded stepRuntime
  admission : PPTAdmissible
    (Input := fun sec => Configuration family policy sec)
    (Output := fun sec _configuration =>
      Kernel.ExecutionResult family policy sec)
    (fun sec configuration =>
      Kernel.runCosted algebra (network sec) (activationLimit sec) configuration)
    (fun sec => activationLimit sec * stepRuntime sec)
  fuel : FuelCertificate (policy := policy) algebra network initial activationLimit

namespace PPTExecutionCertificate

variable {measure : NatMeasure M}
variable {algebra : KernelAlgebra M Address}
variable {network : (sec : Crypto.SecPar) → NetworkAdapter family sec}
variable {initial : (sec : Crypto.SecPar) → Configuration family policy sec}

/-- The projected runtime used by the closed-world machine adapter. -/
def runtime
    (certificate : PPTExecutionCertificate (policy := policy) measure algebra network initial)
    (sec : Crypto.SecPar) : Nat :=
  certificate.activationLimit sec * certificate.stepRuntime sec

/-- The closed-world runner as one generic probabilistic machine. -/
noncomputable def toProbabilisticMachine
    (certificate : PPTExecutionCertificate (policy := policy) measure algebra network initial) :
    ProbabilisticMachine M
      (fun sec => Configuration family policy sec)
      (fun sec _configuration => Kernel.ExecutionResult family policy sec) where
  run := fun sec configuration =>
    Kernel.runCosted algebra (network sec)
      (certificate.activationLimit sec) configuration

/-- The exact fuel-folded cost certificate of the closed-world runner. -/
noncomputable def exactCertificate
    (certificate : PPTExecutionCertificate (policy := policy) measure algebra network initial) :
    ExactCostCertificate certificate.toProbabilisticMachine.run where
  budget := fun sec _configuration =>
    repeatActivationCost M (certificate.activationLimit sec)
      (certificate.step.budget sec)
  sound := fun sec configuration =>
    certificate.step.runCosted_sound (certificate.activationLimit sec) sec configuration

/-- Projecting the exact repeated budget yields the declared uniform runtime. -/
theorem budget_le_runtime
    (certificate : PPTExecutionCertificate (policy := policy) measure algebra network initial)
    (sec : Crypto.SecPar)
    (configuration : Configuration family policy sec) :
    measure (certificate.exactCertificate.budget sec configuration) ≤
      certificate.runtime sec := by
  letI := M.instAddMonoid
  change
    measure (certificate.activationLimit sec • certificate.step.budget sec) ≤
      certificate.activationLimit sec * certificate.stepRuntime sec
  simpa [NatMeasure.map_nsmul] using
    Nat.mul_le_mul_left (certificate.activationLimit sec)
      (certificate.budget_le_stepRuntime sec)

/-- Package the exact runner and its measured uniform runtime. -/
noncomputable def runtimeCertificate
    (certificate : PPTExecutionCertificate (policy := policy) measure algebra network initial) :
    RuntimeCertificate measure certificate.toProbabilisticMachine.run where
  toExactCostCertificate := certificate.exactCertificate
  runtime := certificate.runtime
  budget_le_runtime := certificate.budget_le_runtime

/-- Package the exact closed-world runner and its annotation-level runtime. -/
noncomputable def toTimedMachine
    (certificate : PPTExecutionCertificate (policy := policy) measure algebra network initial) :
    TimedMachine M measure
      (fun sec => Configuration family policy sec)
      (fun sec _configuration => Kernel.ExecutionResult family policy sec) where
  toProbabilisticMachine := certificate.toProbabilisticMachine
  certificate := certificate.runtimeCertificate

/-- The measured closed-world runtime is polynomial. -/
theorem runtime_isPoly
    (certificate : PPTExecutionCertificate (policy := policy) measure algebra network initial) :
    IsPolyBounded certificate.runtime :=
  IsPolyBounded.mul certificate.activationLimit_isPoly certificate.stepRuntime_isPoly

/--
Construct the unified PPT machine without changing its exact execution.

The conversion reuses the independent operational admission stored by the
closed-world certificate; polynomial annotation bounds alone are not promoted
to PPT.
-/
noncomputable def toPPTMachine
    (certificate : PPTExecutionCertificate (policy := policy) measure algebra network initial) :
    PPTMachine M measure
      (fun sec => Configuration family policy sec)
      (fun sec _configuration => Kernel.ExecutionResult family policy sec) :=
  PPTMachine.ofAdmittedTimedMachine certificate.toTimedMachine
    certificate.runtime_isPoly certificate.admission

end PPTExecutionCertificate

end Crypto.Infrastructure.UC

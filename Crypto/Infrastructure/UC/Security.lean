import Crypto.Infrastructure.GameBased.Indistinguishability
import Crypto.Infrastructure.UC.Execution

namespace Crypto.Infrastructure.UC

open Crypto.Infrastructure.Asymptotic
open Crypto.Infrastructure.Computation
open Crypto.Infrastructure.Computation.Cost
open Crypto.Infrastructure.GameBased

universe uCost uAddress uPayload uPort uCapability
universe uState uLeakage uErasure uOutput

/--
External operational admission for the exact handlers of one addressed ITM
under the claimed uniform runtime.

The generic UC cost accounting deliberately provides no constructor for this
predicate.  Bounds on annotated handler paths cannot account for arbitrary
Lean computation hidden in handler bodies, leakage functions, or erasure
functions.  Admission must therefore come from a host-independent operational
model of the same machine and runtime.
-/
opaque PPTAddressedITMAdmissible
    (M : CostModel.{uCost})
    {Address : Type uAddress}
    (schema : PortSchema.{uAddress, uPayload, uPort, uCapability} Address)
    {LocalAddress : Type uAddress} {embed : LocalAddress → Address}
    (machine : AddressedITM.{uCost, uAddress, uPayload, uPort, uCapability,
      uState, uLeakage, uErasure, uOutput} M schema LocalAddress embed)
    (runtime : Crypto.SecPar → Nat) : Prop

/--
Exact handler bounds and one uniform polynomial projection for an addressed
ITM, plus independent operational admission of those exact handlers.  This
certificate covers every entry point through which the kernel can activate or
inspect the component.
-/
structure PPTAddressedITMCertificate
    (M : CostModel.{uCost}) (measure : NatMeasure M)
    {Address : Type uAddress}
    (schema : PortSchema.{uAddress, uPayload, uPort, uCapability} Address)
    {LocalAddress : Type uAddress} {embed : LocalAddress → Address}
    (machine : AddressedITM.{uCost, uAddress, uPayload, uPort, uCapability,
      uState, uLeakage, uErasure, uOutput} M schema LocalAddress embed) where
  initBudget : Crypto.SecPar → LocalAddress → M.Cost
  activationBudget : Crypto.SecPar → LocalAddress → M.Cost
  erasureBudget : Crypto.SecPar → LocalAddress → M.Cost
  leakageBudget : Crypto.SecPar → LocalAddress → M.Cost
  init_sound : ∀ sec address,
    RandCosted.CostBound (machine.init sec address) (initBudget sec address)
  activation_sound : ∀ sec address state input,
    RandCosted.CostBound (machine.activate sec address state input)
      (activationBudget sec address)
  erasure_sound : ∀ sec address request state,
    M.instPartialOrder.le (machine.applyErasure sec address request state).cost
      (erasureBudget sec address)
  leakage_sound : ∀ sec address state,
    M.instPartialOrder.le (machine.leak sec address state).cost
      (leakageBudget sec address)
  runtime : Crypto.SecPar → Nat
  init_measured : ∀ sec address,
    measure (initBudget sec address) ≤ runtime sec
  activation_measured : ∀ sec address,
    measure (activationBudget sec address) ≤ runtime sec
  erasure_measured : ∀ sec address,
    measure (erasureBudget sec address) ≤ runtime sec
  leakage_measured : ∀ sec address,
    measure (leakageBudget sec address) ≤ runtime sec
  runtime_isPoly : IsPolyBounded runtime
  admission : PPTAddressedITMAdmissible M schema machine runtime

/-- A PPT-certified environment, kept distinct from every other UC role. -/
structure PPTEnvironment
    (M : CostModel.{uCost}) (measure : NatMeasure M)
    {Address : Type uAddress}
    (schema : PortSchema.{uAddress, uPayload, uPort, uCapability} Address)
    (LocalAddress : Type uAddress) (embed : LocalAddress → Address) where
  toEnvironment : Environment.{uCost, uAddress, uPayload, uPort, uCapability,
    uState, uLeakage, uErasure, uOutput} M schema LocalAddress embed
  certificate : PPTAddressedITMCertificate M measure schema toEnvironment.machine

/-- A PPT-certified real-world adversary. -/
structure PPTAdversary
    (M : CostModel.{uCost}) (measure : NatMeasure M)
    {Address : Type uAddress}
    (schema : PortSchema.{uAddress, uPayload, uPort, uCapability} Address)
    (LocalAddress : Type uAddress) (embed : LocalAddress → Address) where
  toAdversary : Adversary.{uCost, uAddress, uPayload, uPort, uCapability,
    uState, uLeakage, uErasure, uOutput} M schema LocalAddress embed
  certificate : PPTAddressedITMCertificate M measure schema toAdversary.machine

/-- A PPT-certified ideal-world simulator. -/
structure PPTSimulator
    (M : CostModel.{uCost}) (measure : NatMeasure M)
    {Address : Type uAddress}
    (schema : PortSchema.{uAddress, uPayload, uPort, uCapability} Address)
    (LocalAddress : Type uAddress) (embed : LocalAddress → Address) where
  toSimulator : Simulator.{uCost, uAddress, uPayload, uPort, uCapability,
    uState, uLeakage, uErasure, uOutput} M schema LocalAddress embed
  certificate : PPTAddressedITMCertificate M measure schema toSimulator.machine

variable {M : CostModel.{uCost}} {measure : NatMeasure M}
variable {EnvironmentAddress SystemAddress AdversarialAddress NetworkAddress :
  Type uAddress}
variable [DecidableEq EnvironmentAddress] [DecidableEq SystemAddress]
variable [DecidableEq AdversarialAddress] [DecidableEq NetworkAddress]
variable {schema : PortSchema.{uAddress, uPayload, uPort, uCapability}
  (WorldAddress EnvironmentAddress SystemAddress
    AdversarialAddress NetworkAddress)}

/--
A certified real execution whose world is definitionally role-separated and is
proved to contain exactly the supplied environment, protocol, adversary, and
network components.
-/
structure BoundRealExecution
    (policy : CorruptionPolicy
      (WorldAddress EnvironmentAddress SystemAddress
        AdversarialAddress NetworkAddress))
    (environment : PPTEnvironment.{uCost, uAddress, uPayload, uPort,
      uCapability, uState, uLeakage, uErasure, uOutput}
      M measure schema EnvironmentAddress ClosedWorldAddress.environment)
    (protocol : Protocol.{uCost, uAddress, uPayload, uPort, uCapability,
      uState, uLeakage, uErasure, uOutput}
      M schema SystemAddress ClosedWorldAddress.system)
    (adversary : PPTAdversary.{uCost, uAddress, uPayload, uPort,
      uCapability, uState, uLeakage, uErasure, uOutput}
      M measure schema AdversarialAddress ClosedWorldAddress.adversary)
    (network : Network.{uCost, uAddress, uPayload, uPort, uCapability,
      uState, uLeakage, uErasure, uOutput}
      M schema NetworkAddress ClosedWorldAddress.network) where
  certified : CertifiedRealWorld.{uCost, uAddress, uPayload, uPort,
    uCapability, uState, uLeakage, uErasure, uOutput}
    measure EnvironmentAddress SystemAddress AdversarialAddress NetworkAddress schema
  environment_eq : certified.world.environment = environment.toEnvironment
  policy_eq : certified.world.policy = policy
  protocol_eq : certified.world.protocol = protocol
  adversary_eq : certified.world.adversary = adversary.toAdversary
  network_eq : certified.world.network = network

/--
A certified ideal execution whose world contains exactly the supplied
environment, functionality, simulator, and network components.
-/
structure BoundIdealExecution
    (policy : CorruptionPolicy
      (WorldAddress EnvironmentAddress SystemAddress
        AdversarialAddress NetworkAddress))
    (environment : PPTEnvironment.{uCost, uAddress, uPayload, uPort,
      uCapability, uState, uLeakage, uErasure, uOutput}
      M measure schema EnvironmentAddress ClosedWorldAddress.environment)
    (functionality : IdealFunctionality.{uCost, uAddress, uPayload, uPort,
      uCapability, uState, uLeakage, uErasure, uOutput}
      M schema SystemAddress ClosedWorldAddress.system)
    (simulator : PPTSimulator.{uCost, uAddress, uPayload, uPort,
      uCapability, uState, uLeakage, uErasure, uOutput}
      M measure schema AdversarialAddress ClosedWorldAddress.adversary)
    (network : Network.{uCost, uAddress, uPayload, uPort, uCapability,
      uState, uLeakage, uErasure, uOutput}
      M schema NetworkAddress ClosedWorldAddress.network) where
  certified : CertifiedIdealWorld.{uCost, uAddress, uPayload, uPort,
    uCapability, uState, uLeakage, uErasure, uOutput}
    measure EnvironmentAddress SystemAddress AdversarialAddress NetworkAddress schema
  environment_eq : certified.world.environment = environment.toEnvironment
  policy_eq : certified.world.policy = policy
  functionality_eq : certified.world.functionality = functionality
  simulator_eq : certified.world.simulator = simulator.toSimulator
  network_eq : certified.world.network = network

/--
A UC experiment fixes the protocol, ideal functionality, and explicit network.
Its builders turn every certified external role into the corresponding fully
wired and certified closed world.
-/
structure Experiment
    (M : CostModel.{uCost}) (measure : NatMeasure M)
    (EnvironmentAddress SystemAddress AdversarialAddress NetworkAddress :
      Type uAddress)
    [DecidableEq EnvironmentAddress] [DecidableEq SystemAddress]
    [DecidableEq AdversarialAddress] [DecidableEq NetworkAddress]
    (schema : PortSchema.{uAddress, uPayload, uPort, uCapability}
      (WorldAddress EnvironmentAddress SystemAddress
        AdversarialAddress NetworkAddress)) where
  /-- The one corruption policy shared by the real and ideal executions. -/
  policy : CorruptionPolicy
    (WorldAddress EnvironmentAddress SystemAddress
      AdversarialAddress NetworkAddress)
  protocol : Protocol.{uCost, uAddress, uPayload, uPort, uCapability,
    uState, uLeakage, uErasure, uOutput}
    M schema SystemAddress ClosedWorldAddress.system
  functionality : IdealFunctionality.{uCost, uAddress, uPayload, uPort,
    uCapability, uState, uLeakage, uErasure, uOutput}
    M schema SystemAddress ClosedWorldAddress.system
  network : Network.{uCost, uAddress, uPayload, uPort, uCapability,
    uState, uLeakage, uErasure, uOutput}
    M schema NetworkAddress ClosedWorldAddress.network
  real :
    (adversary : PPTAdversary.{uCost, uAddress, uPayload, uPort,
      uCapability, uState, uLeakage, uErasure, uOutput}
      M measure schema AdversarialAddress ClosedWorldAddress.adversary) →
    (environment : PPTEnvironment.{uCost, uAddress, uPayload, uPort,
      uCapability, uState, uLeakage, uErasure, uOutput}
      M measure schema EnvironmentAddress ClosedWorldAddress.environment) →
      BoundRealExecution policy environment protocol adversary network
  ideal :
    (simulator : PPTSimulator.{uCost, uAddress, uPayload, uPort,
      uCapability, uState, uLeakage, uErasure, uOutput}
      M measure schema AdversarialAddress ClosedWorldAddress.adversary) →
    (environment : PPTEnvironment.{uCost, uAddress, uPayload, uPort,
      uCapability, uState, uLeakage, uErasure, uOutput}
      M measure schema EnvironmentAddress ClosedWorldAddress.environment) →
      BoundIdealExecution policy environment functionality simulator network

namespace Experiment

/-- Build the certified real/ideal pair compared by the environment. -/
def certifiedPair
    (experiment : Experiment.{uCost, uAddress, uPayload, uPort, uCapability,
      uState, uLeakage, uErasure, uOutput}
      M measure EnvironmentAddress SystemAddress AdversarialAddress
        NetworkAddress schema)
    (adversary : PPTAdversary.{uCost, uAddress, uPayload, uPort,
      uCapability, uState, uLeakage, uErasure, uOutput}
      M measure schema AdversarialAddress ClosedWorldAddress.adversary)
    (simulator : PPTSimulator.{uCost, uAddress, uPayload, uPort,
      uCapability, uState, uLeakage, uErasure, uOutput}
      M measure schema AdversarialAddress ClosedWorldAddress.adversary)
    (environment : PPTEnvironment.{uCost, uAddress, uPayload, uPort,
      uCapability, uState, uLeakage, uErasure, uOutput}
      M measure schema EnvironmentAddress ClosedWorldAddress.environment) :
    CertifiedWorldPair.{uCost, uAddress, uPayload, uPort, uCapability,
      uState, uLeakage, uErasure, uOutput}
      measure EnvironmentAddress SystemAddress AdversarialAddress
        NetworkAddress schema where
  real := (experiment.real adversary environment).certified
  ideal := (experiment.ideal simulator environment).certified
  environment_eq :=
    (experiment.real adversary environment).environment_eq.trans
      (experiment.ideal simulator environment).environment_eq.symm
  policy_eq :=
    (experiment.real adversary environment).policy_eq.trans
      (experiment.ideal simulator environment).policy_eq.symm

/-- The Boolean real execution, at the pair's shared certified fuel. -/
noncomputable def realExecution
    (experiment : Experiment.{uCost, uAddress, uPayload, uPort, uCapability,
      uState, uLeakage, uErasure, uOutput}
      M measure EnvironmentAddress SystemAddress AdversarialAddress
        NetworkAddress schema)
    (adversary : PPTAdversary.{uCost, uAddress, uPayload, uPort,
      uCapability, uState, uLeakage, uErasure, uOutput}
      M measure schema AdversarialAddress ClosedWorldAddress.adversary)
    (simulator : PPTSimulator.{uCost, uAddress, uPayload, uPort,
      uCapability, uState, uLeakage, uErasure, uOutput}
      M measure schema AdversarialAddress ClosedWorldAddress.adversary)
    (environment : PPTEnvironment.{uCost, uAddress, uPayload, uPort,
      uCapability, uState, uLeakage, uErasure, uOutput}
      M measure schema EnvironmentAddress ClosedWorldAddress.environment) :
    Game Bool :=
  (experiment.certifiedPair adversary simulator environment).realExecution

/-- The Boolean ideal execution, at the same shared certified fuel. -/
noncomputable def idealExecution
    (experiment : Experiment.{uCost, uAddress, uPayload, uPort, uCapability,
      uState, uLeakage, uErasure, uOutput}
      M measure EnvironmentAddress SystemAddress AdversarialAddress
        NetworkAddress schema)
    (adversary : PPTAdversary.{uCost, uAddress, uPayload, uPort,
      uCapability, uState, uLeakage, uErasure, uOutput}
      M measure schema AdversarialAddress ClosedWorldAddress.adversary)
    (simulator : PPTSimulator.{uCost, uAddress, uPayload, uPort,
      uCapability, uState, uLeakage, uErasure, uOutput}
      M measure schema AdversarialAddress ClosedWorldAddress.adversary)
    (environment : PPTEnvironment.{uCost, uAddress, uPayload, uPort,
      uCapability, uState, uLeakage, uErasure, uOutput}
      M measure schema EnvironmentAddress ClosedWorldAddress.environment) :
    Game Bool :=
  (experiment.certifiedPair adversary simulator environment).idealExecution

/--
The real game is semantically independent of the simulator used only to choose
the shared certified fuel.
-/
theorem realExecution_simulator_independent
    (experiment : Experiment.{uCost, uAddress, uPayload, uPort, uCapability,
      uState, uLeakage, uErasure, uOutput}
      M measure EnvironmentAddress SystemAddress AdversarialAddress
        NetworkAddress schema)
    (adversary : PPTAdversary.{uCost, uAddress, uPayload, uPort,
      uCapability, uState, uLeakage, uErasure, uOutput}
      M measure schema AdversarialAddress ClosedWorldAddress.adversary)
    (leftSimulator rightSimulator : PPTSimulator.{uCost, uAddress, uPayload,
      uPort, uCapability, uState, uLeakage, uErasure, uOutput}
      M measure schema AdversarialAddress ClosedWorldAddress.adversary)
    (environment : PPTEnvironment.{uCost, uAddress, uPayload, uPort,
      uCapability, uState, uLeakage, uErasure, uOutput}
      M measure schema EnvironmentAddress ClosedWorldAddress.environment) :
    realExecution experiment adversary leftSimulator environment =
      realExecution experiment adversary rightSimulator environment := by
  let realCertified := (experiment.real adversary environment).certified
  let leftPair := experiment.certifiedPair adversary leftSimulator environment
  let rightPair := experiment.certifiedPair adversary rightSimulator environment
  calc
    realExecution experiment adversary leftSimulator environment =
        realCertified.execution := by
      simpa only [realExecution, leftPair, realCertified,
        CertifiedWorldPair.realExecution, certifiedPair] using
        realCertified.execution_eq_of_activationLimit_le leftPair.commonFuel
          (fun _sec => Nat.le_max_left _ _)
    _ = realExecution experiment adversary rightSimulator environment := by
      symm
      simpa only [realExecution, rightPair, realCertified,
        CertifiedWorldPair.realExecution, certifiedPair] using
        realCertified.execution_eq_of_activationLimit_le rightPair.commonFuel
          (fun _sec => Nat.le_max_left _ _)

/--
The ideal game is semantically independent of the real adversary used only to
choose the shared certified fuel.
-/
theorem idealExecution_adversary_independent
    (experiment : Experiment.{uCost, uAddress, uPayload, uPort, uCapability,
      uState, uLeakage, uErasure, uOutput}
      M measure EnvironmentAddress SystemAddress AdversarialAddress
        NetworkAddress schema)
    (leftAdversary rightAdversary : PPTAdversary.{uCost, uAddress, uPayload,
      uPort, uCapability, uState, uLeakage, uErasure, uOutput}
      M measure schema AdversarialAddress ClosedWorldAddress.adversary)
    (simulator : PPTSimulator.{uCost, uAddress, uPayload, uPort,
      uCapability, uState, uLeakage, uErasure, uOutput}
      M measure schema AdversarialAddress ClosedWorldAddress.adversary)
    (environment : PPTEnvironment.{uCost, uAddress, uPayload, uPort,
      uCapability, uState, uLeakage, uErasure, uOutput}
      M measure schema EnvironmentAddress ClosedWorldAddress.environment) :
    idealExecution experiment leftAdversary simulator environment =
      idealExecution experiment rightAdversary simulator environment := by
  let idealCertified := (experiment.ideal simulator environment).certified
  let leftPair := experiment.certifiedPair leftAdversary simulator environment
  let rightPair := experiment.certifiedPair rightAdversary simulator environment
  calc
    idealExecution experiment leftAdversary simulator environment =
        idealCertified.execution := by
      simpa only [idealExecution, leftPair, idealCertified,
        CertifiedWorldPair.idealExecution, certifiedPair] using
        idealCertified.execution_eq_of_activationLimit_le leftPair.commonFuel
          (fun _sec => Nat.le_max_right _ _)
    _ = idealExecution experiment rightAdversary simulator environment := by
      symm
      simpa only [idealExecution, rightPair, idealCertified,
        CertifiedWorldPair.idealExecution, certifiedPair] using
        idealCertified.execution_eq_of_activationLimit_le rightPair.commonFuel
          (fun _sec => Nat.le_max_right _ _)

/--
Computational UC emulation with the standard quantifier order.  The adversary
cost model and its `NatMeasure` are explicit parameters of every quantified
PPT role and of both certified executions.
-/
def UCEmulates
    (experiment : Experiment.{uCost, uAddress, uPayload, uPort, uCapability,
      uState, uLeakage, uErasure, uOutput}
      M measure EnvironmentAddress SystemAddress AdversarialAddress
        NetworkAddress schema) : Prop :=
  ∀ adversary : PPTAdversary M measure schema
      AdversarialAddress ClosedWorldAddress.adversary,
    ∃ simulator : PPTSimulator M measure schema
        AdversarialAddress ClosedWorldAddress.adversary,
      ∀ environment : PPTEnvironment M measure schema
          EnvironmentAddress ClosedWorldAddress.environment,
        Indistinguishable
          (realExecution experiment adversary simulator environment)
          (idealExecution experiment adversary simulator environment)

/-- Perfect UC emulation against the same PPT role classes. -/
def PerfectUCEmulates
    (experiment : Experiment.{uCost, uAddress, uPayload, uPort, uCapability,
      uState, uLeakage, uErasure, uOutput}
      M measure EnvironmentAddress SystemAddress AdversarialAddress
        NetworkAddress schema) : Prop :=
  ∀ adversary : PPTAdversary M measure schema
      AdversarialAddress ClosedWorldAddress.adversary,
    ∃ simulator : PPTSimulator M measure schema
        AdversarialAddress ClosedWorldAddress.adversary,
      ∀ environment : PPTEnvironment M measure schema
          EnvironmentAddress ClosedWorldAddress.environment,
        ∀ sec : Crypto.SecPar,
          realExecution experiment adversary simulator environment sec =
            idealExecution experiment adversary simulator environment sec

/-- Exact equality of the two observable games implies computational UC. -/
theorem PerfectUCEmulates.ucEmulates
    {experiment : Experiment.{uCost, uAddress, uPayload, uPort, uCapability,
      uState, uLeakage, uErasure, uOutput}
      M measure EnvironmentAddress SystemAddress AdversarialAddress
        NetworkAddress schema}
    (perfect : PerfectUCEmulates experiment) :
    UCEmulates experiment := by
  intro adversary
  obtain ⟨simulator, simulatorPerfect⟩ := perfect adversary
  refine ⟨simulator, ?_⟩
  intro environment
  have advantage_zero :
      Advantage
          (realExecution experiment adversary simulator environment)
          (idealExecution experiment adversary simulator environment) =
        fun _sec => (0 : Real) := by
    funext sec
    simp only [Advantage, AcceptProb,
      simulatorPerfect environment sec, sub_self, abs_zero]
  unfold Indistinguishable
  rw [advantage_zero]
  exact isNegligible_zero

end Experiment

end Crypto.Infrastructure.UC

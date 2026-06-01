import Crypto.Infrastructure.UC.Protocol
import Mathlib.Data.Finset.Basic
import Mathlib.Probability.ProbabilityMassFunction.Basic

namespace Crypto.Infrastructure.UC.Layered

universe uInput uOutput uPrivateIn uBroadcastIn uPrivateOut uBroadcastOut

/-- Public parameters for a layered/YOSO execution. -/
structure Parameters where
  partiesPerLayer : Nat
  maxCorrupt : Nat
  layers : Nat

namespace Parameters

/-- The honest-majority threshold used by Shamir-style layered MPC. -/
def HonestMajority (params : Parameters) : Prop :=
  3 * params.maxCorrupt < params.partiesPerLayer

/-- The exact threshold form often used in manuscript statements. -/
def ExactShamirThreshold (params : Parameters) : Prop :=
  params.partiesPerLayer = 3 * params.maxCorrupt + 1

theorem exactShamirThreshold_honestMajority
    {params : Parameters} (h : params.ExactShamirThreshold) :
    params.HonestMajority := by
  unfold ExactShamirThreshold at h
  unfold HonestMajority
  rw [h]
  exact Nat.lt_succ_self (3 * params.maxCorrupt)

end Parameters

/-- Parties are indexed by layer and by their position inside that layer. -/
abbrev PartyId (params : Parameters) :=
  Fin params.layers × Fin params.partiesPerLayer

namespace PartyId

variable {params : Parameters}

/-- The layer component of a layered party identifier. -/
def layer (pid : PartyId params) : Fin params.layers :=
  pid.1

/-- The intra-layer party index. -/
def index (pid : PartyId params) : Fin params.partiesPerLayer :=
  pid.2

end PartyId

/-- Trusted roles used by the UC template for layered MPC. -/
inductive TrustedRole where
  | corrManager
  | bcastManager
  deriving DecidableEq, Repr

/-- Boundary roles used by the MPC ideal functionality. -/
inductive BoundaryRole where
  | input : Nat → BoundaryRole
  | output : Nat → BoundaryRole
  deriving DecidableEq, Repr

/-- Entities that can participate in a layered execution. -/
inductive Role (params : Parameters) where
  | party : PartyId params → Role params
  | trusted : TrustedRole → Role params
  | boundary : BoundaryRole → Role params
  deriving DecidableEq

namespace Corruption

variable {params : Parameters}

/-- Corrupted parties from a fixed layer. -/
def partiesInLayer
    (corrupted : Finset (PartyId params)) (layer : Fin params.layers) :
    Finset (PartyId params) :=
  corrupted.filter fun pid => pid.layer = layer

/-- Number of corrupted parties in a fixed layer. -/
def countInLayer
    (corrupted : Finset (PartyId params)) (layer : Fin params.layers) : Nat :=
  (partiesInLayer corrupted layer).card

/-- Decide whether a role is a party role in a fixed layer. -/
def isPartyInLayer (role : Role params) (layer : Fin params.layers) : Bool :=
  match role with
  | Role.party pid => decide (pid.layer = layer)
  | Role.trusted _ => false
  | Role.boundary _ => false

/-- Corrupted layered party roles from a fixed layer. -/
def rolesInLayer
    (corrupted : Finset (Role params)) (layer : Fin params.layers) :
    Finset (Role params) :=
  corrupted.filter fun role => isPartyInLayer role layer = true

/-- Number of corrupted layered party roles in a fixed layer. -/
def countRolesInLayer
    (corrupted : Finset (Role params)) (layer : Fin params.layers) : Nat :=
  (rolesInLayer corrupted layer).card

/-- Non-party roles such as trusted managers and boundary roles are never corrupt. -/
def OnlyParties (corrupted : Finset (Role params)) : Prop :=
  ∀ role ∈ corrupted, ∃ pid : PartyId params, role = Role.party pid

/-- The layered/YOSO corruption condition: each layer has at most `t` corruptions. -/
def Eligible (params : Parameters) (corrupted : Finset (Role params)) : Prop :=
  OnlyParties corrupted ∧
    ∀ layer : Fin params.layers, countRolesInLayer corrupted layer ≤ params.maxCorrupt

/-- Dynamic layered/YOSO corruption, bounded independently in every layer. -/
def layeredPolicy (params : Parameters) : CorruptionPolicy (Role params) where
  mode := Crypto.Infrastructure.UC.CorruptionMode.dynamic
  eligible := Eligible params

end Corruption

/-- View a layered protocol as a generic UC protocol. -/
def protocol
    (params : Parameters)
    (Input : Crypto.SecPar → Role params → Type uInput)
    (Output : Crypto.SecPar → Role params → Type uOutput)
    (machine :
      (role : Role params) →
      Crypto.Infrastructure.UC.InteractiveSystem
        (fun sec => Input sec role)
        (fun sec => Output sec role)) :
    Crypto.Infrastructure.UC.Protocol where
  Entity := Role params
  Input := Input
  Output := Output
  corruptionPolicy := Corruption.layeredPolicy params
  machine := machine

/--
The common local step shape for layered protocols in the paper.

A party reads private inputs and broadcasts from the previous layer, then emits
one private output for each party in the next layer plus one broadcast value.
Concrete protocols such as VSS, resharing, and multiplication will instantiate
the four message types and the step function.
-/
structure PartyStep
    (params : Parameters)
    (PrivateIn : Type uPrivateIn) (BroadcastIn : Type uBroadcastIn)
    (PrivateOut : Type uPrivateOut) (BroadcastOut : Type uBroadcastOut) where
  run :
    Crypto.SecPar →
    PartyId params →
    (Fin params.partiesPerLayer → Option PrivateIn) →
    (Fin params.partiesPerLayer → Option BroadcastIn) →
    PMF ((Fin params.partiesPerLayer → PrivateOut) × BroadcastOut)

/--
An MPC functionality `f : Input^n -> Output^m`, allowing randomized ideal
functionalities when needed.  Deterministic arithmetic-circuit MPC is the
special case built with `MPCFunctionality.deterministic`.
-/
structure MPCFunctionality (Input : Type uInput) (Output : Type uOutput) where
  inputCount : Nat
  outputCount : Nat
  eval : (Fin inputCount → Input) → PMF (Fin outputCount → Output)

namespace MPCFunctionality

variable {Input : Type uInput} {Output : Type uOutput}

/-- Build a deterministic MPC ideal functionality from a pure function. -/
noncomputable def deterministic
    (inputCount outputCount : Nat)
    (eval : (Fin inputCount → Input) → Fin outputCount → Output) :
    MPCFunctionality Input Output where
  inputCount := inputCount
  outputCount := outputCount
  eval inputs := PMF.pure (eval inputs)

/-- State buffers used by the MPC ideal functionality. -/
structure State (functionality : MPCFunctionality Input Output) where
  inputs : Fin functionality.inputCount → Option Input
  outputs : Fin functionality.outputCount → Option Output
  outDelivered : Bool

end MPCFunctionality

end Crypto.Infrastructure.UC.Layered

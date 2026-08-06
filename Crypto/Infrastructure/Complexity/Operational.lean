import CryptoFirstOrder.Core
import Crypto.Infrastructure.Computation.Cost.Measure
import Crypto.Infrastructure.Computation.Randomized
import Crypto.Infrastructure.Complexity.OracleMachineCore
import Crypto.Infrastructure.SecurityParameter

namespace Crypto.Infrastructure.Complexity

open Crypto.Infrastructure.Computation
open Crypto.Infrastructure.Computation.Cost
open Crypto.Infrastructure.Computation.Oracle

universe uArtifact uClaim uCost uValue uBase uOp uClosedInput uCallerInput uOutput
  uOracle uQuery uResponse

/--
A host-independent operational model for executable artifacts and the resource
claims assigned to them.

`Code` is deliberately abstract at this common boundary. The built-in
first-order model instantiates it with reified programs, while an external
backend can use its own code representation. `denote` and `claim` make the
semantic artifact and its operational resource claim explicit.
-/
structure OperationalModel
    (Artifact : Type uArtifact) (Claim : Type uClaim) where
  Code : Type (max uArtifact uClaim)
  denote : Code → Artifact
  claim : Code → Claim

namespace OperationalModel

/--
The explicit trust anchor for code validated outside the library. Internally
validated first-order code does not require this predicate.
-/
opaque ExternalValidCode
    {Artifact : Type uArtifact} {Claim : Type uClaim}
    (model : OperationalModel Artifact Claim) (code : model.Code) : Prop

end OperationalModel

/--
A first-order program, its structurally validated primitive algebra, and an
exact measured path bound. This is the internally checkable operational code
format; it contains no higher-order program continuation.
-/
structure FirstOrderOperationalCode
    (M : CostModel.{uCost}) (measure : NatMeasure M)
    {Base : Type uValue} (interpret : Base → Type uValue)
    {S : CryptoFirstOrder.Signature.{uValue, uValue} Base}
    (A : CryptoFirstOrder.CostedAlgebra M interpret S)
    (Input Output : CryptoFirstOrder.Ty Base) where
  program : CryptoFirstOrder.Program interpret S Input Output
  algebraValid : CryptoFirstOrder.ValidAlgebra M interpret A
  budget : CryptoFirstOrder.Ty.denote interpret Input → M.Cost
  costBound : CryptoFirstOrder.Program.CostBound A program budget
  runtime : Nat
  budget_le_runtime : ∀ input, measure (budget input) ≤ runtime

/--
A closed oracle adapter whose executable pieces are all programs in one
structurally validated first-order algebra.

The host-facing functions below are representation boundaries only: they
encode inputs and decode results.  Preparation, rejection, and every oracle
query are executed by the stored `Program`s.  Consequently this object cannot
be manufactured from an arbitrary `OracleEnv` or value-only host map.
-/
structure FirstOrderOracleAdapter
    (M : CostModel.{uCost}) (measure : NatMeasure M)
    (ClosedInput : Crypto.SecPar → Type uClosedInput)
    (CallerInput : Crypto.SecPar → Type uCallerInput)
    (Output : Crypto.SecPar → Type uOutput)
    (Spec : (sec : Crypto.SecPar) → CallerInput sec →
      OracleSpec.{uOracle, uQuery, uResponse})
    {Base : Type uBase} (interpret : Base → Type uValue)
    {S : CryptoFirstOrder.Signature.{uBase, uBase} Base}
    (A : CryptoFirstOrder.CostedAlgebra M interpret S)
    (PrepareInput PrepareOutput RejectInput RejectOutput
      QueryInput QueryOutput : CryptoFirstOrder.Ty Base) where
  algebraValid : CryptoFirstOrder.ValidAlgebra M interpret A
  accepted : (sec : Crypto.SecPar) → ClosedInput sec → Prop
  acceptedDecidable : ∀ sec input, Decidable (accepted sec input)
  prepareProgram : CryptoFirstOrder.Program interpret S PrepareInput PrepareOutput
  rejectProgram : CryptoFirstOrder.Program interpret S RejectInput RejectOutput
  queryProgram : CryptoFirstOrder.Program interpret S QueryInput QueryOutput
  prepareBudget : CryptoFirstOrder.Ty.denote interpret PrepareInput → M.Cost
  rejectBudget : CryptoFirstOrder.Ty.denote interpret RejectInput → M.Cost
  queryBudget : CryptoFirstOrder.Ty.denote interpret QueryInput → M.Cost
  prepareCostBound : CryptoFirstOrder.Program.CostBound
    A prepareProgram prepareBudget
  rejectCostBound : CryptoFirstOrder.Program.CostBound
    A rejectProgram rejectBudget
  queryCostBound : CryptoFirstOrder.Program.CostBound
    A queryProgram queryBudget
  prepareInput : ∀ sec, ClosedInput sec →
    CryptoFirstOrder.Ty.denote interpret PrepareInput
  prepareOutput : ∀ sec, ClosedInput sec →
    CryptoFirstOrder.Ty.denote interpret PrepareOutput → CallerInput sec
  rejectInput : ∀ sec, ClosedInput sec →
    CryptoFirstOrder.Ty.denote interpret RejectInput
  rejectOutput : ∀ sec, ClosedInput sec →
    CryptoFirstOrder.Ty.denote interpret RejectOutput → Output sec
  State : Type
  init : ∀ sec, (input : ClosedInput sec) → CallerInput sec → State
  queryInput : ∀ sec, (input : ClosedInput sec) →
    (callerInput : CallerInput sec) →
    (name : (Spec sec callerInput).Name) → Crypto.SecPar → State →
    (Spec sec callerInput).Query name →
      CryptoFirstOrder.Ty.denote interpret QueryInput
  queryOutput : ∀ sec, (input : ClosedInput sec) →
    (callerInput : CallerInput sec) →
    (name : (Spec sec callerInput).Name) →
    CryptoFirstOrder.Ty.denote interpret QueryOutput →
      (Spec sec callerInput).Response name × State
  prepareRuntime : Crypto.SecPar → Nat
  rejectRuntime : Crypto.SecPar → Nat
  queryRuntime : Crypto.SecPar → Nat
  prepareBudget_le_runtime : ∀ sec input,
    measure (prepareBudget (prepareInput sec input)) ≤ prepareRuntime sec
  rejectBudget_le_runtime : ∀ sec input,
    measure (rejectBudget (rejectInput sec input)) ≤ rejectRuntime sec
  queryBudget_le_runtime : ∀ sec input callerInput name querySec state query,
    accepted sec input →
    measure (queryBudget
      (queryInput sec input callerInput name querySec state query)) ≤
      queryRuntime sec

namespace FirstOrderOracleAdapter

variable
    {M : CostModel.{uCost}} {measure : NatMeasure M}
    {ClosedInput : Crypto.SecPar → Type uClosedInput}
    {CallerInput : Crypto.SecPar → Type uCallerInput}
    {Output : Crypto.SecPar → Type uOutput}
    {Spec : (sec : Crypto.SecPar) → CallerInput sec →
      OracleSpec.{uOracle, uQuery, uResponse}}
    {Base : Type uBase} {interpret : Base → Type uValue}
    {S : CryptoFirstOrder.Signature.{uBase, uBase} Base}
    {A : CryptoFirstOrder.CostedAlgebra M interpret S}
    {PrepareInput PrepareOutput RejectInput RejectOutput
      QueryInput QueryOutput : CryptoFirstOrder.Ty Base}

noncomputable def runPrepare
    (adapter : FirstOrderOracleAdapter M measure ClosedInput CallerInput Output
      Spec interpret A PrepareInput PrepareOutput RejectInput RejectOutput
      QueryInput QueryOutput)
    (sec : Crypto.SecPar) (input : ClosedInput sec) :
    RandCosted M (CallerInput sec) :=
  RandCosted.map (adapter.prepareOutput sec input)
    (CryptoFirstOrder.Program.runCosted A adapter.prepareProgram
      (adapter.prepareInput sec input))

noncomputable def runReject
    (adapter : FirstOrderOracleAdapter M measure ClosedInput CallerInput Output
      Spec interpret A PrepareInput PrepareOutput RejectInput RejectOutput
      QueryInput QueryOutput)
    (sec : Crypto.SecPar) (input : ClosedInput sec) :
    RandCosted M (Output sec) :=
  RandCosted.map (adapter.rejectOutput sec input)
    (CryptoFirstOrder.Program.runCosted A adapter.rejectProgram
      (adapter.rejectInput sec input))

noncomputable def oracleEnv
    (adapter : FirstOrderOracleAdapter M measure ClosedInput CallerInput Output
      Spec interpret A PrepareInput PrepareOutput RejectInput RejectOutput
      QueryInput QueryOutput)
    (sec : Crypto.SecPar) (input : ClosedInput sec)
    (callerInput : CallerInput sec) :
    CostedOracleEnv M (Spec sec callerInput) where
  State := adapter.State
  init := adapter.init sec input callerInput
  query := fun name querySec state query =>
    RandCosted.map (adapter.queryOutput sec input callerInput name)
      (CryptoFirstOrder.Program.runCosted A adapter.queryProgram
        (adapter.queryInput sec input callerInput name querySec state query))

/-- The only closed-run semantics admitted by the controlled adapter compiler. -/
noncomputable def close
    (adapter : FirstOrderOracleAdapter M measure ClosedInput CallerInput Output
      Spec interpret A PrepareInput PrepareOutput RejectInput RejectOutput
      QueryInput QueryOutput)
    (caller : OracleMachine M CallerInput (fun sec _input => Output sec) Spec) :
    RandomizedComputation M ClosedInput (fun sec _input => Output sec) :=
  fun sec input =>
    letI := adapter.acceptedDecidable sec input
    if adapter.accepted sec input then
      RandCosted.bind (adapter.runPrepare sec input) fun callerInput =>
        caller.runCosted sec callerInput
          (adapter.oracleEnv sec input callerInput)
    else
      adapter.runReject sec input

/-- Runtime expression fixed by the controlled compiler. -/
def closedRuntime
    (adapter : FirstOrderOracleAdapter M measure ClosedInput CallerInput Output
      Spec interpret A PrepareInput PrepareOutput RejectInput RejectOutput
      QueryInput QueryOutput)
    (callerRuntime : (Crypto.SecPar → Nat) × (Crypto.SecPar → Nat)) :
    Crypto.SecPar → Nat :=
  fun sec => max (adapter.rejectRuntime sec)
    (adapter.prepareRuntime sec +
      (callerRuntime.1 sec + callerRuntime.2 sec * adapter.queryRuntime sec))

end FirstOrderOracleAdapter

/--
The canonical operational model for one fixed first-order signature and exact
algebra. Its denotation is the language interpreter and its claim is the
stored uniform measured runtime.
-/
noncomputable def firstOrderOperationalModel
    (M : CostModel.{uCost}) (measure : NatMeasure M)
    {Base : Type uValue} (interpret : Base → Type uValue)
    {S : CryptoFirstOrder.Signature.{uValue, uValue} Base}
    (A : CryptoFirstOrder.CostedAlgebra M interpret S)
    (Input Output : CryptoFirstOrder.Ty Base)
    (Claim : Type uClaim) (claimOfRuntime : Nat → Claim) :
    OperationalModel
      (CryptoFirstOrder.Ty.denote interpret Input →
        RandCosted M (CryptoFirstOrder.Ty.denote interpret Output))
      Claim where
  Code := ULift.{uClaim} (FirstOrderOperationalCode M measure interpret A Input Output)
  denote code := CryptoFirstOrder.Program.runCosted A code.down.program
  claim code := claimOfRuntime code.down.runtime

/--
The security-parameter-indexed lift of the canonical first-order model. The
same reified program is run at every index; the security parameter cannot be
used to select hidden Lean code.
-/
noncomputable def firstOrderMachineOperationalModel
    (M : CostModel.{uCost}) (measure : NatMeasure M)
    {Base : Type uValue} (interpret : Base → Type uValue)
    {S : CryptoFirstOrder.Signature.{uValue, uValue} Base}
    (A : CryptoFirstOrder.CostedAlgebra M interpret S)
    (Input Output : CryptoFirstOrder.Ty Base)
    (Claim : Type uClaim) (claimOfRuntime : Nat → Claim) :
    OperationalModel
      ((sec : Crypto.SecPar) → CryptoFirstOrder.Ty.denote interpret Input →
        RandCosted M (CryptoFirstOrder.Ty.denote interpret Output))
      Claim where
  Code := ULift.{uClaim} (FirstOrderOperationalCode M measure interpret A Input Output)
  denote code := fun _sec => CryptoFirstOrder.Program.runCosted A code.down.program
  claim code := claimOfRuntime code.down.runtime

namespace OperationalModel

/--
Validation has exactly two sources: an explicitly external backend obligation,
or the library's canonical first-order model with a structural algebra witness
and an exact measured path-bound certificate.

The second constructor closes PR1's generic validation hole for the minimal
first-order language. It does not assert that a Lean implementation of a
bottom algebra operation matches a particular physical instruction set.
-/
inductive ValidCode :
    {Artifact : Type uArtifact} → {Claim : Type uClaim} →
    (model : OperationalModel Artifact Claim) → model.Code → Prop where
  | external
      {Artifact : Type uArtifact} {Claim : Type uClaim}
      {model : OperationalModel Artifact Claim} {code : model.Code} :
      ExternalValidCode model code → ValidCode model code
  | firstOrder
      {M : CostModel.{uArtifact}} {measure : NatMeasure M}
      {Base : Type uArtifact} {interpret : Base → Type uArtifact}
      {S : CryptoFirstOrder.Signature.{uArtifact, uArtifact} Base}
      {A : CryptoFirstOrder.CostedAlgebra M interpret S}
      {Input Output : CryptoFirstOrder.Ty Base}
      {Claim : Type uClaim} {claimOfRuntime : Nat → Claim}
      (code : FirstOrderOperationalCode M measure interpret A Input Output) :
      @ValidCode
        (CryptoFirstOrder.Ty.denote interpret Input →
          RandCosted M (CryptoFirstOrder.Ty.denote interpret Output))
        Claim
        (firstOrderOperationalModel M measure interpret A Input Output
          Claim claimOfRuntime)
        (ULift.up code)
  | firstOrderMachine
      {M : CostModel.{uArtifact}} {measure : NatMeasure M}
      {Base : Type uArtifact} {interpret : Base → Type uArtifact}
      {S : CryptoFirstOrder.Signature.{uArtifact, uArtifact} Base}
      {A : CryptoFirstOrder.CostedAlgebra M interpret S}
      {Input Output : CryptoFirstOrder.Ty Base}
      {Claim : Type uClaim} {claimOfRuntime : Nat → Claim}
      (code : FirstOrderOperationalCode M measure interpret A Input Output) :
      @ValidCode
        ((sec : Crypto.SecPar) → CryptoFirstOrder.Ty.denote interpret Input →
          RandCosted M (CryptoFirstOrder.Ty.denote interpret Output))
        Claim
        (firstOrderMachineOperationalModel M measure interpret A Input Output
          Claim claimOfRuntime)
        (ULift.up code)
end OperationalModel

/--
A semantic artifact and resource claim realized by one validated code object
in an explicit operational model.

Unlike the former opaque admission predicates, the realization exposes the
model, code, denotation equation, and claim equation. Validation is internal
for the canonical first-order model and remains explicit for external models.
-/
def OperationalRealization
    {Artifact : Type uArtifact} {Claim : Type uClaim}
    (artifact : Artifact) (claim : Claim) : Prop :=
  ∃ (model : OperationalModel Artifact Claim) (code : model.Code),
    model.ValidCode code ∧
      model.denote code = artifact ∧
      model.claim code = claim

namespace OperationalRealization

/-- Package one validated operational code object as a realization. -/
theorem ofValidatedCode
    {Artifact : Type uArtifact} {Claim : Type uClaim}
    {artifact : Artifact} {claim : Claim}
    (model : OperationalModel Artifact Claim) (code : model.Code)
    (valid : model.ValidCode code)
    (denote_eq : model.denote code = artifact)
    (claim_eq : model.claim code = claim) :
    OperationalRealization artifact claim := by
  exact ⟨model, code, valid, denote_eq, claim_eq⟩

/-- Internally validated first-order code realizes its interpreted run. -/
theorem ofFirstOrderCode
    {M : CostModel.{uValue}} {measure : NatMeasure M}
    {Base : Type uValue} {interpret : Base → Type uValue}
    {S : CryptoFirstOrder.Signature.{uValue, uValue} Base}
    {A : CryptoFirstOrder.CostedAlgebra M interpret S}
    {Input Output : CryptoFirstOrder.Ty Base}
    (code : FirstOrderOperationalCode M measure interpret A Input Output) :
    OperationalRealization
      (CryptoFirstOrder.Program.runCosted A code.program) code.runtime := by
  exact
    ⟨firstOrderOperationalModel M measure interpret A Input Output Nat id,
      ULift.up code, OperationalModel.ValidCode.firstOrder code, rfl, rfl⟩

/--
Internally validated first-order code realizes the corresponding constant
security-parameter-indexed machine and runtime.
-/
theorem ofFirstOrderMachineCode
    {M : CostModel.{uValue}} {measure : NatMeasure M}
    {Base : Type uValue} {interpret : Base → Type uValue}
    {S : CryptoFirstOrder.Signature.{uValue, uValue} Base}
    {A : CryptoFirstOrder.CostedAlgebra M interpret S}
    {Input Output : CryptoFirstOrder.Ty Base}
    (code : FirstOrderOperationalCode M measure interpret A Input Output) :
    OperationalRealization
      (fun _sec : Crypto.SecPar =>
        CryptoFirstOrder.Program.runCosted A code.program)
      (fun _sec : Crypto.SecPar => code.runtime) := by
  exact
    ⟨firstOrderMachineOperationalModel M measure interpret A Input Output
        (Crypto.SecPar → Nat) (fun runtime _sec => runtime),
      ULift.up code, OperationalModel.ValidCode.firstOrderMachine code, rfl, rfl⟩

end OperationalRealization

end Crypto.Infrastructure.Complexity

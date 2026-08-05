import Crypto.Infrastructure.Computation.FirstOrder.Basic
import Crypto.Infrastructure.Computation.Cost.Measure
import Crypto.Infrastructure.SecurityParameter

namespace Crypto.Infrastructure.Complexity

open Crypto.Infrastructure.Computation
open Crypto.Infrastructure.Computation.Cost

universe uArtifact uClaim uCost uValue

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
    {S : FirstOrder.Signature.{uValue, uValue} Base}
    (A : FirstOrder.CostedAlgebra M interpret S)
    (Input Output : FirstOrder.Ty Base) where
  program : FirstOrder.Program interpret S Input Output
  algebraValid : FirstOrder.ValidAlgebra M interpret A
  budget : FirstOrder.Ty.denote interpret Input → M.Cost
  costBound : FirstOrder.Program.CostBound A program budget
  runtime : Nat
  budget_le_runtime : ∀ input, measure (budget input) ≤ runtime

/--
The canonical operational model for one fixed first-order signature and exact
algebra. Its denotation is the language interpreter and its claim is the
stored uniform measured runtime.
-/
noncomputable def firstOrderOperationalModel
    (M : CostModel.{uCost}) (measure : NatMeasure M)
    {Base : Type uValue} (interpret : Base → Type uValue)
    {S : FirstOrder.Signature.{uValue, uValue} Base}
    (A : FirstOrder.CostedAlgebra M interpret S)
    (Input Output : FirstOrder.Ty Base)
    (Claim : Type uClaim) (claimOfRuntime : Nat → Claim) :
    OperationalModel
      (FirstOrder.Ty.denote interpret Input →
        RandCosted M (FirstOrder.Ty.denote interpret Output))
      Claim where
  Code := ULift.{uClaim} (FirstOrderOperationalCode M measure interpret A Input Output)
  denote code := FirstOrder.Program.runCosted A code.down.program
  claim code := claimOfRuntime code.down.runtime

/--
The security-parameter-indexed lift of the canonical first-order model. The
same reified program is run at every index; the security parameter cannot be
used to select hidden Lean code.
-/
noncomputable def firstOrderMachineOperationalModel
    (M : CostModel.{uCost}) (measure : NatMeasure M)
    {Base : Type uValue} (interpret : Base → Type uValue)
    {S : FirstOrder.Signature.{uValue, uValue} Base}
    (A : FirstOrder.CostedAlgebra M interpret S)
    (Input Output : FirstOrder.Ty Base)
    (Claim : Type uClaim) (claimOfRuntime : Nat → Claim) :
    OperationalModel
      ((sec : Crypto.SecPar) → FirstOrder.Ty.denote interpret Input →
        RandCosted M (FirstOrder.Ty.denote interpret Output))
      Claim where
  Code := ULift.{uClaim} (FirstOrderOperationalCode M measure interpret A Input Output)
  denote code := fun _sec => FirstOrder.Program.runCosted A code.down.program
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
      {S : FirstOrder.Signature.{uArtifact, uArtifact} Base}
      {A : FirstOrder.CostedAlgebra M interpret S}
      {Input Output : FirstOrder.Ty Base}
      {Claim : Type uClaim} {claimOfRuntime : Nat → Claim}
      (code : FirstOrderOperationalCode M measure interpret A Input Output) :
      @ValidCode
        (FirstOrder.Ty.denote interpret Input →
          RandCosted M (FirstOrder.Ty.denote interpret Output))
        Claim
        (firstOrderOperationalModel M measure interpret A Input Output
          Claim claimOfRuntime)
        (ULift.up code)
  | firstOrderMachine
      {M : CostModel.{uArtifact}} {measure : NatMeasure M}
      {Base : Type uArtifact} {interpret : Base → Type uArtifact}
      {S : FirstOrder.Signature.{uArtifact, uArtifact} Base}
      {A : FirstOrder.CostedAlgebra M interpret S}
      {Input Output : FirstOrder.Ty Base}
      {Claim : Type uClaim} {claimOfRuntime : Nat → Claim}
      (code : FirstOrderOperationalCode M measure interpret A Input Output) :
      @ValidCode
        ((sec : Crypto.SecPar) → FirstOrder.Ty.denote interpret Input →
          RandCosted M (FirstOrder.Ty.denote interpret Output))
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
    {S : FirstOrder.Signature.{uValue, uValue} Base}
    {A : FirstOrder.CostedAlgebra M interpret S}
    {Input Output : FirstOrder.Ty Base}
    (code : FirstOrderOperationalCode M measure interpret A Input Output) :
    OperationalRealization
      (FirstOrder.Program.runCosted A code.program) code.runtime := by
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
    {S : FirstOrder.Signature.{uValue, uValue} Base}
    {A : FirstOrder.CostedAlgebra M interpret S}
    {Input Output : FirstOrder.Ty Base}
    (code : FirstOrderOperationalCode M measure interpret A Input Output) :
    OperationalRealization
      (fun _sec : Crypto.SecPar =>
        FirstOrder.Program.runCosted A code.program)
      (fun _sec : Crypto.SecPar => code.runtime) := by
  exact
    ⟨firstOrderMachineOperationalModel M measure interpret A Input Output
        (Crypto.SecPar → Nat) (fun runtime _sec => runtime),
      ULift.up code, OperationalModel.ValidCode.firstOrderMachine code, rfl, rfl⟩

end OperationalRealization

end Crypto.Infrastructure.Complexity

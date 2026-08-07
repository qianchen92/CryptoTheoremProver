import CryptoLib.Core.Infrastructure.Complexity.Basic
import Mathlib.Data.ZMod.Basic

namespace CryptoLib.Test.FirstOrder

open CryptoLib.Core.Infrastructure.Complexity
open CryptoLib.Core.Infrastructure.Computation
open CryptoLib.Core.Infrastructure.Computation.Cost
open scoped CryptoLib.Program

/-- Two abstract carrier names for a small ElGamal-shaped regression. -/
inductive GroupBase where
  | scalar
  | group
  deriving DecidableEq

abbrev interpret : GroupBase → Type
  | .scalar => ZMod 5
  | .group => ZMod 5

abbrev scalarTy :
    CryptoLib.Program.Ty GroupBase := .base .scalar

abbrev groupTy :
    CryptoLib.Program.Ty GroupBase := .base .group

local instance scalarFintype :
    Fintype
      (CryptoLib.Program.Ty.denote
        interpret scalarTy) := by
  change Fintype (ZMod 5)
  infer_instance

local instance scalarNonempty :
    Nonempty
      (CryptoLib.Program.Ty.denote
        interpret scalarTy) := by
  change Nonempty (ZMod 5)
  infer_instance

local instance scalarGroupSMul :
    SMul
      (CryptoLib.Program.Ty.denote
        interpret scalarTy)
      (CryptoLib.Program.Ty.denote
        interpret groupTy) := by
  change SMul (ZMod 5) (ZMod 5)
  infer_instance

local instance groupAdd :
    Add
      (CryptoLib.Program.Ty.denote
        interpret groupTy) := by
  change Add (ZMod 5)
  infer_instance

def groupGenerator :
    CryptoLib.Program.Ty.denote interpret groupTy := by
  change ZMod 5
  exact 1

/-- Uniform scalar sampling, scalar action, then group addition. -/
abbrev GroupSignature :=
  CryptoLib.Program.Signature.sum
    (CryptoLib.Program.UniformSampleOperation.signature
      scalarTy)
    (CryptoLib.Program.Signature.sum
      (CryptoLib.Program.SMulOperation.signature
        scalarTy groupTy)
      (CryptoLib.Program.AddOperation.signature groupTy))

noncomputable def groupAlgebra :
    CryptoLib.Program.CostedAlgebra
      CostModel.nat interpret GroupSignature :=
  CryptoLib.Program.CostedAlgebra.sum
    (CryptoLib.Program.UniformSampleOperation.algebra
      CostModel.nat interpret scalarTy 2)
    (CryptoLib.Program.CostedAlgebra.sum
      (CryptoLib.Program.SMulOperation.algebra
        CostModel.nat interpret scalarTy groupTy 3)
      (CryptoLib.Program.AddOperation.algebra
        CostModel.nat interpret groupTy 1))

/-- The exact algebra uses only the structurally admitted built-in primitives. -/
noncomputable def groupAlgebraValid :
    CryptoLib.Program.ValidAlgebra
      CostModel.nat interpret groupAlgebra :=
  CryptoLib.Program.ValidAlgebra.sum
    (M := CostModel.nat) (interpret := interpret)
    (CryptoLib.Program.ValidAlgebra.uniformSample
      (M := CostModel.nat) (interpret := interpret)
      scalarTy (2 : Nat))
    (CryptoLib.Program.ValidAlgebra.sum
      (M := CostModel.nat) (interpret := interpret)
      (CryptoLib.Program.ValidAlgebra.smul
        (M := CostModel.nat) (interpret := interpret)
        scalarTy groupTy (3 : Nat))
      (CryptoLib.Program.ValidAlgebra.add
        (M := CostModel.nat) (interpret := interpret)
        groupTy (1 : Nat)))

/-- The uniform distribution descriptor used by the generic `sample T D` form. -/
def scalarUniformSampler :
    CryptoLib.Program.Sampler
      GroupSignature scalarTy :=
  CryptoLib.Program.SmartOperation.uniformSampler
    scalarTy

/--
Sample `r`, compute `r • 1` and `r • input`, then add the two group values.
The nested surface operations A-normalize to four calls whose continuations are
represented by syntax under successively extended environments.
-/
noncomputable def groupCode :
    CryptoLib.Program.Code
      interpret GroupSignature [groupTy] groupTy :=
    first_order input do
      let sampled ← sample scalarTy scalarUniformSampler
      let result ←
        (sampled • value(groupGenerator)) + (sampled • input)
      return result

/-- Nested smart operations compile to the same core code as explicit ANF. -/
example :
    groupCode =
      (first_order input do
        let sampled ← sample scalarTy scalarUniformSampler
        let firstGroup ← sampled • value(groupGenerator)
        let secondGroup ← sampled • input
        let result ← firstGroup + secondGroup
        return result) := by
  rfl

noncomputable def groupProgram :
    CryptoLib.Program.Procedure
      interpret GroupSignature groupTy groupTy where
  body := groupCode

/-- A singleton typed context reduces to the original unary input representation. -/
noncomputable def unaryProgram :
    CryptoLib.Program.Procedure.NAry
      interpret GroupSignature [groupTy] groupTy where
  body := first_order (input) do
    return input

/-- A static three-input context is compiled to one right-associated tuple input. -/
noncomputable def ternaryProgram :
    CryptoLib.Program.Procedure.NAry
      interpret GroupSignature [groupTy, groupTy, groupTy] groupTy where
  body := first_order (left, middle, right) do
    let partialSum ← left + middle
    let result ← partialSum + right
    return result

private theorem sampleBound
    (args :
      CryptoLib.Program.Ty.denote interpret .unit) :
    RandCosted.CostBound
      (groupAlgebra.exec (.inl .sample) args) 2 := by
  exact
    CryptoLib.Program.UniformSampleOperation.costBound_exec
      CostModel.nat interpret scalarTy 2 .sample args

private theorem smulBound
    (args :
      CryptoLib.Program.Ty.denote interpret
        (.prod scalarTy groupTy)) :
    RandCosted.CostBound
      (groupAlgebra.exec (.inr (.inl .smul)) args) 3 := by
  exact
    CryptoLib.Program.SMulOperation.costBound_exec
      CostModel.nat interpret scalarTy groupTy 3 .smul args

private theorem addBound
    (args :
      CryptoLib.Program.Ty.denote interpret
        (.prod groupTy groupTy)) :
    RandCosted.CostBound
      (groupAlgebra.exec (.inr (.inr .add)) args) 1 := by
  exact
    CryptoLib.Program.AddOperation.costBound_exec
      CostModel.nat interpret groupTy 1 .add args

/-- The represented four-call program has exact path budget `2 + 3 + 3 + 1`. -/
theorem groupProgramCostBound :
    CryptoLib.Program.Procedure.CostBound
      groupAlgebra groupProgram (fun _input => 9) := by
  intro input
  change
    CryptoLib.Program.Code.CostBound
      groupAlgebra groupCode (.cons input .nil) 9
  unfold groupCode
  apply CryptoLib.Program.Code.CostBound.call
    (nextBudget := (7 : Nat)) (operationBound := sampleBound _)
  intro sampled
  apply CryptoLib.Program.Code.CostBound.call
    (nextBudget := (4 : Nat)) (operationBound := smulBound _)
  intro firstGroup
  apply CryptoLib.Program.Code.CostBound.call
    (nextBudget := (1 : Nat)) (operationBound := smulBound _)
  intro secondGroup
  apply CryptoLib.Program.Code.CostBound.call
    (nextBudget := (0 : Nat)) (operationBound := addBound _)
  intro result
  exact CryptoLib.Program.Code.CostBound.ret
    (.var .here) _

/-- A complete internally checkable code certificate for the sample program. -/
noncomputable def groupOperationalCode :
    FirstOrderOperationalCode CostModel.nat NatMeasure.nat
      interpret groupAlgebra groupTy groupTy where
  program := groupProgram
  algebraValid := groupAlgebraValid
  budget := fun _input => 9
  costBound := groupProgramCostBound
  runtime := 9
  budget_le_runtime := fun _input => Nat.le_refl 9

/-- No external `ValidCode` hypothesis is needed for this PPT construction. -/
noncomputable def groupPPTMachine :
    PPTMachine CostModel.nat NatMeasure.nat
      (fun _sec => ZMod 5) (fun _sec _input => ZMod 5) :=
  PPTMachine.ofFirstOrderCode groupOperationalCode

/-- Cost erasure of the built-in sampler is the finite uniform distribution. -/
example
    (args :
      CryptoLib.Program.Ty.denote interpret .unit) :
    RandCosted.valueDist (groupAlgebra.exec (.inl .sample) args) =
      CryptoLib.Core.Infrastructure.Probability.uniformPMF (ZMod 5) := by
  exact
    CryptoLib.Program.UniformSampleOperation.valueDist_exec
      CostModel.nat interpret scalarTy 2 args

end CryptoLib.Test.FirstOrder

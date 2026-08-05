import Crypto.Infrastructure.Complexity.Basic
import Mathlib.Data.ZMod.Basic

namespace CryptoTest.Infrastructure.Computation.FirstOrder

open Crypto.Infrastructure.Complexity
open Crypto.Infrastructure.Computation
open Crypto.Infrastructure.Computation.Cost
open scoped Crypto.Infrastructure.Computation.FirstOrder

/-- Two abstract carrier names for a small ElGamal-shaped regression. -/
inductive GroupBase where
  | scalar
  | group
  deriving DecidableEq

abbrev interpret : GroupBase → Type
  | .scalar => ZMod 5
  | .group => ZMod 5

abbrev scalarTy :
    Crypto.Infrastructure.Computation.FirstOrder.Ty GroupBase := .base .scalar

abbrev groupTy :
    Crypto.Infrastructure.Computation.FirstOrder.Ty GroupBase := .base .group

local instance scalarFintype :
    Fintype
      (Crypto.Infrastructure.Computation.FirstOrder.Ty.denote
        interpret scalarTy) := by
  change Fintype (ZMod 5)
  infer_instance

local instance scalarNonempty :
    Nonempty
      (Crypto.Infrastructure.Computation.FirstOrder.Ty.denote
        interpret scalarTy) := by
  change Nonempty (ZMod 5)
  infer_instance

local instance scalarGroupSMul :
    SMul
      (Crypto.Infrastructure.Computation.FirstOrder.Ty.denote
        interpret scalarTy)
      (Crypto.Infrastructure.Computation.FirstOrder.Ty.denote
        interpret groupTy) := by
  change SMul (ZMod 5) (ZMod 5)
  infer_instance

local instance groupAdd :
    Add
      (Crypto.Infrastructure.Computation.FirstOrder.Ty.denote
        interpret groupTy) := by
  change Add (ZMod 5)
  infer_instance

def groupGenerator :
    Crypto.Infrastructure.Computation.FirstOrder.Ty.denote interpret groupTy := by
  change ZMod 5
  exact 1

/-- Uniform scalar sampling, scalar action, then group addition. -/
abbrev GroupSignature :=
  Crypto.Infrastructure.Computation.FirstOrder.Signature.sum
    (Crypto.Infrastructure.Computation.FirstOrder.UniformSampleOperation.signature
      scalarTy)
    (Crypto.Infrastructure.Computation.FirstOrder.Signature.sum
      (Crypto.Infrastructure.Computation.FirstOrder.SMulOperation.signature
        scalarTy groupTy)
      (Crypto.Infrastructure.Computation.FirstOrder.AddOperation.signature groupTy))

noncomputable def groupAlgebra :
    Crypto.Infrastructure.Computation.FirstOrder.CostedAlgebra
      CostModel.nat interpret GroupSignature :=
  Crypto.Infrastructure.Computation.FirstOrder.CostedAlgebra.sum
    (Crypto.Infrastructure.Computation.FirstOrder.UniformSampleOperation.algebra
      CostModel.nat interpret scalarTy 2)
    (Crypto.Infrastructure.Computation.FirstOrder.CostedAlgebra.sum
      (Crypto.Infrastructure.Computation.FirstOrder.SMulOperation.algebra
        CostModel.nat interpret scalarTy groupTy 3)
      (Crypto.Infrastructure.Computation.FirstOrder.AddOperation.algebra
        CostModel.nat interpret groupTy 1))

/-- The exact algebra uses only the structurally admitted built-in primitives. -/
noncomputable def groupAlgebraValid :
    Crypto.Infrastructure.Computation.FirstOrder.ValidAlgebra
      CostModel.nat interpret groupAlgebra :=
  Crypto.Infrastructure.Computation.FirstOrder.ValidAlgebra.sum
    (M := CostModel.nat) (interpret := interpret)
    (Crypto.Infrastructure.Computation.FirstOrder.ValidAlgebra.uniformSample
      (M := CostModel.nat) (interpret := interpret)
      scalarTy (2 : Nat))
    (Crypto.Infrastructure.Computation.FirstOrder.ValidAlgebra.sum
      (M := CostModel.nat) (interpret := interpret)
      (Crypto.Infrastructure.Computation.FirstOrder.ValidAlgebra.smul
        (M := CostModel.nat) (interpret := interpret)
        scalarTy groupTy (3 : Nat))
      (Crypto.Infrastructure.Computation.FirstOrder.ValidAlgebra.add
        (M := CostModel.nat) (interpret := interpret)
        groupTy (1 : Nat)))

/--
Sample `r`, compute `r • 1` and `r • input`, then add the two group values.
Every continuation is represented by syntax under an extended environment.
-/
noncomputable def groupCode :
    Crypto.Infrastructure.Computation.FirstOrder.Code
      interpret GroupSignature [groupTy] groupTy :=
    first_order input do
      let sampled ← call (.inl .sample) with unit
      let firstGroup ←
        call (.inr (.inl .smul)) with (sampled, value(groupGenerator))
      let secondGroup ←
        call (.inr (.inl .smul)) with (sampled, input)
      let result ← call (.inr (.inr .add)) with (firstGroup, secondGroup)
      return result

noncomputable def groupProgram :
    Crypto.Infrastructure.Computation.FirstOrder.Program
      interpret GroupSignature groupTy groupTy where
  body := groupCode

private theorem sampleBound
    (args :
      Crypto.Infrastructure.Computation.FirstOrder.Ty.denote interpret .unit) :
    RandCosted.CostBound
      (groupAlgebra.exec (.inl .sample) args) 2 := by
  exact
    Crypto.Infrastructure.Computation.FirstOrder.UniformSampleOperation.costBound_exec
      CostModel.nat interpret scalarTy 2 .sample args

private theorem smulBound
    (args :
      Crypto.Infrastructure.Computation.FirstOrder.Ty.denote interpret
        (.prod scalarTy groupTy)) :
    RandCosted.CostBound
      (groupAlgebra.exec (.inr (.inl .smul)) args) 3 := by
  exact
    Crypto.Infrastructure.Computation.FirstOrder.SMulOperation.costBound_exec
      CostModel.nat interpret scalarTy groupTy 3 .smul args

private theorem addBound
    (args :
      Crypto.Infrastructure.Computation.FirstOrder.Ty.denote interpret
        (.prod groupTy groupTy)) :
    RandCosted.CostBound
      (groupAlgebra.exec (.inr (.inr .add)) args) 1 := by
  exact
    Crypto.Infrastructure.Computation.FirstOrder.AddOperation.costBound_exec
      CostModel.nat interpret groupTy 1 .add args

/-- The represented four-call program has exact path budget `2 + 3 + 3 + 1`. -/
theorem groupProgramCostBound :
    Crypto.Infrastructure.Computation.FirstOrder.Program.CostBound
      groupAlgebra groupProgram (fun _input => 9) := by
  intro input
  change
    Crypto.Infrastructure.Computation.FirstOrder.Code.CostBound
      groupAlgebra groupCode (.cons input .nil) 9
  unfold groupCode
  apply Crypto.Infrastructure.Computation.FirstOrder.Code.CostBound.call
    (nextBudget := (7 : Nat)) (operationBound := sampleBound _)
  intro sampled
  apply Crypto.Infrastructure.Computation.FirstOrder.Code.CostBound.call
    (nextBudget := (4 : Nat)) (operationBound := smulBound _)
  intro firstGroup
  apply Crypto.Infrastructure.Computation.FirstOrder.Code.CostBound.call
    (nextBudget := (1 : Nat)) (operationBound := smulBound _)
  intro secondGroup
  apply Crypto.Infrastructure.Computation.FirstOrder.Code.CostBound.call
    (nextBudget := (0 : Nat)) (operationBound := addBound _)
  intro result
  exact Crypto.Infrastructure.Computation.FirstOrder.Code.CostBound.ret
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
      Crypto.Infrastructure.Computation.FirstOrder.Ty.denote interpret .unit) :
    RandCosted.valueDist (groupAlgebra.exec (.inl .sample) args) =
      Crypto.Infrastructure.Probability.uniformPMF (ZMod 5) := by
  exact
    Crypto.Infrastructure.Computation.FirstOrder.UniformSampleOperation.valueDist_exec
      CostModel.nat interpret scalarTy 2 args

end CryptoTest.Infrastructure.Computation.FirstOrder

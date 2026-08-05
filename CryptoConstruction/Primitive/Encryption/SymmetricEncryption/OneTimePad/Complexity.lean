import Crypto.Infrastructure.Complexity.ProgramMachine
import Crypto.Infrastructure.Computation.Algebra.Bounds
import CryptoConstruction.Primitive.Encryption.SymmetricEncryption.OneTimePad.Scheme

namespace CryptoConstruction.Primitive.Encryption.SymmetricEncryption.OneTimePad

open Crypto.Infrastructure.Complexity
open Crypto.Infrastructure.Computation
open Crypto.Infrastructure.Computation.Algebra
open Crypto.Infrastructure.Computation.Cost
open scoped OneTimePadParameter

universe uCost uGroup

variable {M : CostModel.{uCost}}

/-- Uniform operation budgets attached to the exact OTP algebra. -/
structure ParamEfficiencyCertificate (pp : PublicParam M) where
  bounds : OperationBounds pp.algebra
  sampleKeyBudget : M.Cost
  sampleKeyBudget_sound :
    M.instPartialOrder.le (bounds.budget Operation.sampleKey) sampleKeyBudget
  addBudget : M.Cost
  addBudget_sound : ∀ left right,
    M.instPartialOrder.le (bounds.budget (Operation.add left right)) addBudget
  negBudget : M.Cost
  negBudget_sound : ∀ value,
    M.instPartialOrder.le (bounds.budget (Operation.neg value)) negBudget

/-- Static key-generation budget: one exact key-sampling operation. -/
def keygenBudget
    (pp : PublicParam M) (certificate : ParamEfficiencyCertificate pp) : M.Cost :=
  certificate.sampleKeyBudget

/-- Static encryption budget: one exact group addition. -/
def encryptBudget
    (pp : PublicParam M) (certificate : ParamEfficiencyCertificate pp) : M.Cost :=
  certificate.addBudget

/-- Static decryption budget: negation followed by addition. -/
def decryptBudget
    (pp : PublicParam M) (certificate : ParamEfficiencyCertificate pp) : M.Cost :=
  M.instAddMonoid.add certificate.negBudget certificate.addBudget

private theorem sampleKeyOperationBound
    (pp : PublicParam M) (certificate : ParamEfficiencyCertificate pp)
    (args : FirstOrder.Ty.denote (Language.interpret pp) .unit) :
    RandCosted.CostBound
      ((Language.algebra pp).exec Language.Operation.sampleKey args)
      certificate.sampleKeyBudget := by
  simpa [Language.algebra] using
    RandCosted.CostBound.weaken
      (certificate.bounds.cost_le
        (Operation.sampleKey (math := pp.toAdditiveGroupParam)))
      certificate.sampleKeyBudget_sound

private theorem addOperationBound
    (pp : PublicParam M) (certificate : ParamEfficiencyCertificate pp)
    (args : FirstOrder.Ty.denote (Language.interpret pp)
      (.prod Language.carrierTy Language.carrierTy)) :
    RandCosted.CostBound
      ((Language.algebra pp).exec Language.Operation.add args)
      certificate.addBudget := by
  simpa [Language.algebra] using
    RandCosted.CostBound.weaken
      (certificate.bounds.cost_le (Operation.add args.1 args.2))
      (certificate.addBudget_sound args.1 args.2)

private theorem negOperationBound
    (pp : PublicParam M) (certificate : ParamEfficiencyCertificate pp)
    (args : FirstOrder.Ty.denote (Language.interpret pp)
      Language.carrierTy) :
    RandCosted.CostBound
      ((Language.algebra pp).exec Language.Operation.neg args)
      certificate.negBudget := by
  simpa [Language.algebra] using
    RandCosted.CostBound.weaken
      (certificate.bounds.cost_le (Operation.neg args))
      (certificate.negBudget_sound args)

/-- Statically bounded key generation, indexing the same program body. -/
def keygenBoundedProgram
    (pp : PublicParam M) (certificate : ParamEfficiencyCertificate pp) :
    FirstOrder.Program.Bounded
      (Input := .unit) (Output := Language.carrierTy)
      (Language.algebra pp)
      (fun _input => keygenBudget pp certificate) where
  program := keygenProgram pp
  certificate := by
    intro input
    have bound :
        FirstOrder.Code.CostBound (Language.algebra pp)
          (keygenProgram pp).body (.cons input .nil)
          (M.instAddMonoid.add certificate.sampleKeyBudget
            M.instAddMonoid.zero) := by
      unfold keygenProgram
      apply FirstOrder.Code.CostBound.call
        (operationBound := sampleKeyOperationBound pp certificate _)
      intro key
      exact FirstOrder.Code.CostBound.ret (.var .here) _
    apply RandCosted.CostBound.weaken bound
    letI := M.instPartialOrder
    exact le_of_eq (M.instAddMonoid.add_zero certificate.sampleKeyBudget)

/-- Statically bounded encryption, indexing the same program body. -/
def encryptBoundedProgram
    (pp : PublicParam M) (certificate : ParamEfficiencyCertificate pp) :
    FirstOrder.Program.Bounded
      (Input := .prod Language.carrierTy Language.carrierTy)
      (Output := Language.carrierTy) (Language.algebra pp)
      (fun _input => encryptBudget pp certificate) where
  program := encryptProgram pp
  certificate := by
    intro input
    have bound :
        FirstOrder.Code.CostBound (Language.algebra pp)
          (encryptProgram pp).body (.cons input .nil)
          (M.instAddMonoid.add certificate.addBudget
            M.instAddMonoid.zero) := by
      unfold encryptProgram
      apply FirstOrder.Code.CostBound.call
        (operationBound := addOperationBound pp certificate _)
      intro ciphertext
      exact FirstOrder.Code.CostBound.ret (.var .here) _
    apply RandCosted.CostBound.weaken bound
    letI := M.instPartialOrder
    exact le_of_eq (M.instAddMonoid.add_zero certificate.addBudget)

/-- Statically bounded decryption, indexing the same program body. -/
def decryptBoundedProgram
    (pp : PublicParam M) (certificate : ParamEfficiencyCertificate pp) :
    FirstOrder.Program.Bounded
      (Input := .prod Language.carrierTy Language.carrierTy)
      (Output := Language.carrierTy) (Language.algebra pp)
      (fun _input => decryptBudget pp certificate) where
  program := decryptProgram pp
  certificate := by
    intro input
    have bound :
        FirstOrder.Code.CostBound (Language.algebra pp)
          (decryptProgram pp).body (.cons input .nil)
          (M.instAddMonoid.add certificate.negBudget
            (M.instAddMonoid.add certificate.addBudget
              M.instAddMonoid.zero)) := by
      unfold decryptProgram
      apply FirstOrder.Code.CostBound.call
        (operationBound := negOperationBound pp certificate _)
      intro negatedKey
      apply FirstOrder.Code.CostBound.call
        (operationBound := addOperationBound pp certificate _)
      intro message
      exact FirstOrder.Code.CostBound.ret (.var .here) _
    apply RandCosted.CostBound.weaken bound
    letI := M.instPartialOrder
    exact le_of_eq (congrArg (M.instAddMonoid.add certificate.negBudget)
      (M.instAddMonoid.add_zero certificate.addBudget))

/-- Global setup efficiency for an OTP family. -/
structure EfficiencyCertificate (F : Family M) where
  setupBudget : Crypto.SecPar → M.Cost
  setupCostBound : Program.CostBound (setupProgram F) setupBudget

/-- Exact setup efficiency for a fixed OTP family. -/
noncomputable def EfficiencyCertificate.ofFixed
    (pp : PublicParam M) (setupCost : M.Cost) :
    EfficiencyCertificate (Family.ofFixed pp setupCost) where
  setupBudget := fun _sec => setupCost
  setupCostBound := by
    intro sec result hresult
    simp only [setupProgram, Program.Code.runCosted, familyAlgebra,
      Family.ofFixed, RandCosted.liftCosted, PMF.mem_support_pure_iff] at hresult
    subst result
    letI := M.instPartialOrder
    exact le_refl setupCost

/-- The authoritative setup program satisfies the supplied global certificate. -/
theorem setup_costBound
    (F : Family M) (certificate : EfficiencyCertificate F) :
    Program.CostBound (setupProgram F) certificate.setupBudget :=
  certificate.setupCostBound

theorem keygenProgram_costBound
    (pp : PublicParam M) (certificate : ParamEfficiencyCertificate pp) :
    FirstOrder.Program.CostBound (Language.algebra pp) (keygenProgram pp)
      (fun _input => keygenBudget pp certificate) :=
  (keygenBoundedProgram pp certificate).certificate

theorem encryptProgram_costBound
    (pp : PublicParam M) (certificate : ParamEfficiencyCertificate pp) :
    FirstOrder.Program.CostBound (Language.algebra pp) (encryptProgram pp)
      (fun _input => encryptBudget pp certificate) :=
  (encryptBoundedProgram pp certificate).certificate

theorem decryptProgram_costBound
    (pp : PublicParam M) (certificate : ParamEfficiencyCertificate pp) :
    FirstOrder.Program.CostBound (Language.algebra pp) (decryptProgram pp)
      (fun _input => decryptBudget pp certificate) :=
  (decryptBoundedProgram pp certificate).certificate

/-- Fixed-parameter encryption with an explicit natural-number runtime observation. -/
noncomputable def encryptTimedMachine
    (measure : NatMeasure M)
    (pp : PublicParam M) (certificate : ParamEfficiencyCertificate pp) :
    TimedMachine M measure
      (fun _sec => pp.Carrier × pp.Carrier)
      (fun _sec _input => pp.Carrier) :=
  TimedMachine.ofFirstOrderProgram measure
    (Language.algebra pp) (encryptProgram pp)
    (fun _input => encryptBudget pp certificate)
    (measure (encryptBudget pp certificate))
    (encryptProgram_costBound pp certificate)
    (fun _input => Nat.le_refl _)

@[simp] theorem encryptTimedMachine_runDist
    (measure : NatMeasure M)
    (F : Family M) (pp : PublicParam M)
    (certificate : ParamEfficiencyCertificate pp)
    (sec : Crypto.SecPar) (input : pp.Carrier × pp.Carrier) :
    (encryptTimedMachine measure pp certificate).runDist sec input =
      (scheme F).encryptDist pp input.1 input.2 := by
  rfl

end CryptoConstruction.Primitive.Encryption.SymmetricEncryption.OneTimePad

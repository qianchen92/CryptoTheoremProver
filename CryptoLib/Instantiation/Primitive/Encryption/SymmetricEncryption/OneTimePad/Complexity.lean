import CryptoLib.Core.Infrastructure.Complexity.ProgramMachine
import CryptoLib.Core.Infrastructure.Computation.Algebra.Bounds
import CryptoLib.Instantiation.Primitive.Encryption.SymmetricEncryption.OneTimePad.Scheme

namespace CryptoLib.Instantiation.Primitive.Encryption.SymmetricEncryption.OneTimePad

open CryptoLib.Core.Infrastructure.Complexity
open CryptoLib.Core.Infrastructure.Computation
open CryptoLib.Core.Infrastructure.Computation.Algebra
open CryptoLib.Core.Infrastructure.Computation.Cost
open scoped OneTimePadParameter

universe uCost uGroup

variable
    {M : CostModel.{uCost}}
    (measure : NatMeasure M)
    (F : Family.{uCost, uGroup} M)
    (pp : PublicParam.{uCost, uGroup} M)

/-- Uniform operation budgets attached to the exact OTP algebra. -/
structure ParamEfficiencyCertificate where
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

variable
    (certificate : ParamEfficiencyCertificate pp)
    (setupCost : M.Cost)

/-- Static key-generation budget: one exact key-sampling operation. -/
def keygenBudget : M.Cost :=
  certificate.sampleKeyBudget

/-- Static encryption budget: one exact group addition. -/
def encryptBudget : M.Cost :=
  certificate.addBudget

/-- Static decryption budget: negation followed by addition. -/
def decryptBudget : M.Cost :=
  M.instAddMonoid.add certificate.negBudget certificate.addBudget

private theorem sampleKeyOperationBound
    (args : CryptoLib.Program.Ty.denote (Language.interpret pp) .unit) :
    RandCosted.CostBound
      ((Language.algebra pp).exec Language.Operation.sampleKey args)
      certificate.sampleKeyBudget := by
  simpa [Language.algebra] using
    RandCosted.CostBound.weaken
      (certificate.bounds.cost_le
        (Operation.sampleKey (math := pp.toAdditiveGroupParam)))
      certificate.sampleKeyBudget_sound

private theorem addOperationBound
    (args : CryptoLib.Program.Ty.denote (Language.interpret pp)
      (.prod Language.carrierTy Language.carrierTy)) :
    RandCosted.CostBound
      ((Language.algebra pp).exec Language.Operation.add args)
      certificate.addBudget := by
  simpa [Language.algebra] using
    RandCosted.CostBound.weaken
      (certificate.bounds.cost_le (Operation.add args.1 args.2))
      (certificate.addBudget_sound args.1 args.2)

private theorem negOperationBound
    (args : CryptoLib.Program.Ty.denote (Language.interpret pp)
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
    : CryptoLib.Program.Procedure.Bounded
      (Input := .unit) (Output := Language.carrierTy)
      (Language.algebra pp)
      (fun _input => keygenBudget pp certificate) where
  program := keygenProgram pp
  certificate := by
    intro input
    have bound :
        CryptoLib.Program.Code.CostBound (Language.algebra pp)
          (keygenProgram pp).body (.cons input .nil)
          (M.instAddMonoid.add certificate.sampleKeyBudget
            M.instAddMonoid.zero) := by
      unfold keygenProgram
      apply CryptoLib.Program.Code.CostBound.call
        (operationBound := sampleKeyOperationBound pp certificate _)
      intro key
      exact CryptoLib.Program.Code.CostBound.ret (.var .here) _
    apply RandCosted.CostBound.weaken bound
    letI := M.instPartialOrder
    exact le_of_eq (M.instAddMonoid.add_zero certificate.sampleKeyBudget)

/-- Statically bounded encryption, indexing the same program body. -/
def encryptBoundedProgram
    : CryptoLib.Program.Procedure.Bounded
      (Input := .prod Language.carrierTy Language.carrierTy)
      (Output := Language.carrierTy) (Language.algebra pp)
      (fun _input => encryptBudget pp certificate) where
  program := encryptProgram pp
  certificate := by
    intro input
    have bound :
        CryptoLib.Program.Code.CostBound (Language.algebra pp)
          (encryptProgram pp).body (.cons input .nil)
          (M.instAddMonoid.add certificate.addBudget
            M.instAddMonoid.zero) := by
      unfold encryptProgram
      apply CryptoLib.Program.Code.CostBound.call
        (operationBound := addOperationBound pp certificate _)
      intro ciphertext
      exact CryptoLib.Program.Code.CostBound.ret (.var .here) _
    apply RandCosted.CostBound.weaken bound
    letI := M.instPartialOrder
    exact le_of_eq (M.instAddMonoid.add_zero certificate.addBudget)

/-- Statically bounded decryption, indexing the same program body. -/
def decryptBoundedProgram
    : CryptoLib.Program.Procedure.Bounded
      (Input := .prod Language.carrierTy Language.carrierTy)
      (Output := Language.carrierTy) (Language.algebra pp)
      (fun _input => decryptBudget pp certificate) where
  program := decryptProgram pp
  certificate := by
    intro input
    have bound :
        CryptoLib.Program.Code.CostBound (Language.algebra pp)
          (decryptProgram pp).body (.cons input .nil)
          (M.instAddMonoid.add certificate.negBudget
            (M.instAddMonoid.add certificate.addBudget
              M.instAddMonoid.zero)) := by
      unfold decryptProgram
      apply CryptoLib.Program.Code.CostBound.call
        (operationBound := negOperationBound pp certificate _)
      intro negatedKey
      apply CryptoLib.Program.Code.CostBound.call
        (operationBound := addOperationBound pp certificate _)
      intro message
      exact CryptoLib.Program.Code.CostBound.ret (.var .here) _
    apply RandCosted.CostBound.weaken bound
    letI := M.instPartialOrder
    exact le_of_eq (congrArg (M.instAddMonoid.add certificate.negBudget)
      (M.instAddMonoid.add_zero certificate.addBudget))

/-- Global setup efficiency for an OTP family. -/
structure EfficiencyCertificate where
  setupBudget : CryptoLib.Core.SecPar → M.Cost
  setupCostBound : Program.CostBound (setupProgram F) setupBudget

variable (familyCertificate : EfficiencyCertificate F)

/-- Exact setup efficiency for a fixed OTP family. -/
noncomputable def EfficiencyCertificate.ofFixed
    : EfficiencyCertificate (Family.ofFixed pp setupCost) where
  setupBudget := fun _sec => setupCost
  setupCostBound := by
    intro sec result hresult
    simp only [setupProgram,
      CryptoLib.Core.Infrastructure.Computation.Program.Code.runCosted, familyAlgebra,
      Family.ofFixed, RandCosted.liftCosted, PMF.mem_support_pure_iff] at hresult
    subst result
    letI := M.instPartialOrder
    exact le_refl setupCost

/-- The authoritative setup program satisfies the supplied global certificate. -/
theorem setup_costBound
    : Program.CostBound (setupProgram F) familyCertificate.setupBudget :=
  familyCertificate.setupCostBound

theorem keygenProgram_costBound
    : CryptoLib.Program.Procedure.CostBound (Language.algebra pp) (keygenProgram pp)
      (fun _input => keygenBudget pp certificate) :=
  (keygenBoundedProgram pp certificate).certificate

theorem encryptProgram_costBound
    : CryptoLib.Program.Procedure.CostBound (Language.algebra pp) (encryptProgram pp)
      (fun _input => encryptBudget pp certificate) :=
  (encryptBoundedProgram pp certificate).certificate

theorem decryptProgram_costBound
    : CryptoLib.Program.Procedure.CostBound (Language.algebra pp) (decryptProgram pp)
      (fun _input => decryptBudget pp certificate) :=
  (decryptBoundedProgram pp certificate).certificate

/-- Fixed-parameter encryption with an explicit natural-number runtime observation. -/
noncomputable def encryptTimedMachine
    : TimedMachine M measure
      (fun _sec => pp.Carrier × pp.Carrier)
      (fun _sec _input => pp.Carrier) :=
  TimedMachine.ofFirstOrderProgram measure
    (Language.algebra pp) (encryptProgram pp)
    (fun _input => encryptBudget pp certificate)
    (measure (encryptBudget pp certificate))
    (encryptProgram_costBound pp certificate)
    (fun _input => Nat.le_refl _)

@[simp] theorem encryptTimedMachine_runDist
    (sec : CryptoLib.Core.SecPar) (input : pp.Carrier × pp.Carrier) :
    (encryptTimedMachine measure pp certificate).runDist sec input =
      (scheme F).encryptDist pp input.1 input.2 := by
  rfl

end CryptoLib.Instantiation.Primitive.Encryption.SymmetricEncryption.OneTimePad

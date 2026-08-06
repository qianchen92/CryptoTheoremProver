import Crypto.Infrastructure.Complexity.ProgramMachine
import CryptoConstruction.Primitive.Encryption.AsymmetricEncryption.ElGamal.Scheme

namespace CryptoConstruction.Primitive.Encryption.AsymmetricEncryption.ElGamal

open Crypto.Infrastructure.Complexity
open Crypto.Infrastructure.Computation
open Crypto.Infrastructure.Computation.Cost
open scoped DDHParameter

universe uCost uParameter uScalar uGroup

variable
    {M : CostModel.{uCost}}
    {Parameter : Type uParameter}
    {Scalar : Type uScalar}
    {Carrier : Type uGroup}
    (measure : NatMeasure M)
    (pp : PublicParam.{uCost, uScalar, uGroup} M Scalar Carrier)
    (certificate : Crypto.Assumption.DL.DDH.ParamEfficiencyCertificate pp)

/-- Static key-generation budget: one scalar sample and one scalar action. -/
def keygenBudget : M.Cost :=
  M.instAddMonoid.add certificate.scalarSampleBudget
    (M.instAddMonoid.add certificate.smulBudget M.instAddMonoid.zero)

/-- One scalar sample, two scalar actions, and one carrier addition. -/
def encryptBudget : M.Cost :=
  M.instAddMonoid.add certificate.scalarSampleBudget
      (M.instAddMonoid.add certificate.smulBudget
        (M.instAddMonoid.add certificate.smulBudget
          (M.instAddMonoid.add certificate.addBudget M.instAddMonoid.zero)))

/-- One scalar action followed by one carrier subtraction. -/
def decryptBudget : M.Cost :=
  M.instAddMonoid.add certificate.smulBudget certificate.subBudget

private theorem scalarSampleOperationBound
    (args : CryptoFirstOrder.Ty.denote (Language.interpret pp) .unit) :
    RandCosted.CostBound
      ((Language.algebra pp).exec Language.Operation.sampleScalar args)
      certificate.scalarSampleBudget := by
  simpa [Language.algebra] using
    RandCosted.CostBound.weaken
      (certificate.bounds.cost_le
        (Crypto.Assumption.DL.DDH.Op.sampleScalar
          (math := pp.toDecisionalCyclicAction)))
      certificate.scalarSampleBudget_sound

private theorem smulOperationBound
    (args : CryptoFirstOrder.Ty.denote (Language.interpret pp)
      (.prod Language.scalarTy Language.carrierTy)) :
    RandCosted.CostBound
      ((Language.algebra pp).exec Language.Operation.smul args)
      certificate.smulBudget := by
  simpa [Language.algebra] using
    RandCosted.CostBound.weaken
      (certificate.bounds.cost_le
        (Crypto.Assumption.DL.DDH.Op.smul args.1.down args.2.down))
      (certificate.smulBudget_sound args.1.down args.2.down)

private theorem addOperationBound
    (args : CryptoFirstOrder.Ty.denote (Language.interpret pp)
      (.prod Language.carrierTy Language.carrierTy)) :
    RandCosted.CostBound
      ((Language.algebra pp).exec Language.Operation.add args)
      certificate.addBudget := by
  simpa [Language.algebra] using
    RandCosted.CostBound.weaken
      (certificate.bounds.cost_le
        (Crypto.Assumption.DL.DDH.Op.add args.1.down args.2.down))
      (certificate.addBudget_sound args.1.down args.2.down)

private theorem subOperationBound
    (args : CryptoFirstOrder.Ty.denote (Language.interpret pp)
      (.prod Language.carrierTy Language.carrierTy)) :
    RandCosted.CostBound
      ((Language.algebra pp).exec Language.Operation.sub args)
      certificate.subBudget := by
  simpa [Language.algebra] using
    RandCosted.CostBound.weaken
      (certificate.bounds.cost_le
        (Crypto.Assumption.DL.DDH.Op.sub args.1.down args.2.down))
      (certificate.subBudget_sound args.1.down args.2.down)

/-- The key-generation bound indexes the same first-order program body. -/
noncomputable def keygenBoundedProgram
    : CryptoFirstOrder.Program.Bounded
      (Input := .unit)
      (Output := .prod Language.carrierTy Language.scalarTy)
      (Language.algebra pp)
      (fun _input => keygenBudget pp certificate) where
  program := keygenProgram pp
  certificate := by
    intro input
    unfold keygenProgram
    apply CryptoFirstOrder.Code.CostBound.call
      (operationBound := scalarSampleOperationBound pp certificate _)
    intro sk
    apply CryptoFirstOrder.Code.CostBound.call
      (operationBound := smulOperationBound pp certificate _)
    intro pk
    exact CryptoFirstOrder.Code.CostBound.ret
      (.pair (.var .here) (.var (.there .here))) _

/-- The encryption bound indexes the same first-order program body. -/
noncomputable def encryptBoundedProgram
    : CryptoFirstOrder.Program.Bounded
      (Input := .prod Language.carrierTy Language.carrierTy)
      (Output := .prod Language.carrierTy Language.carrierTy)
      (Language.algebra pp)
      (fun _input => encryptBudget pp certificate) where
  program := encryptProgram pp
  certificate := by
    intro input
    unfold encryptProgram
    apply CryptoFirstOrder.Code.CostBound.call
      (operationBound := scalarSampleOperationBound pp certificate _)
    intro r
    apply CryptoFirstOrder.Code.CostBound.call
      (operationBound := smulOperationBound pp certificate _)
    intro firstComponent
    apply CryptoFirstOrder.Code.CostBound.call
      (operationBound := smulOperationBound pp certificate _)
    intro shared
    apply CryptoFirstOrder.Code.CostBound.call
      (operationBound := addOperationBound pp certificate _)
    intro secondComponent
    exact CryptoFirstOrder.Code.CostBound.ret
      (.pair (.var (.there (.there .here))) (.var .here)) _

/-- The decryption bound indexes the same first-order program body. -/
noncomputable def decryptBoundedProgram
    : CryptoFirstOrder.Program.Bounded
      (Input := .prod Language.scalarTy
        (.prod Language.carrierTy Language.carrierTy))
      (Output := Language.carrierTy)
      (Language.algebra pp)
      (fun _input => decryptBudget pp certificate) where
  program := decryptProgram pp
  certificate := by
    intro input
    have bound :
        CryptoFirstOrder.Code.CostBound (Language.algebra pp)
          (decryptProgram pp).body (.cons input .nil)
          (M.instAddMonoid.add certificate.smulBudget
            (M.instAddMonoid.add certificate.subBudget
              M.instAddMonoid.zero)) := by
      unfold decryptProgram
      apply CryptoFirstOrder.Code.CostBound.call
        (operationBound := smulOperationBound pp certificate _)
      intro shared
      apply CryptoFirstOrder.Code.CostBound.call
        (operationBound := subOperationBound pp certificate _)
      intro message
      exact CryptoFirstOrder.Code.CostBound.ret (.var .here) _
    apply RandCosted.CostBound.weaken bound
    letI := M.instPartialOrder
    exact le_of_eq (congrArg (M.instAddMonoid.add certificate.smulBudget)
      (M.instAddMonoid.add_zero certificate.subBudget))

private theorem encryptExecution_exact
    (pk message : pp.Carrier)
    (value : Language.CarrierValue pp × Language.CarrierValue pp)
    (cost : M.Cost)
    (execution : CryptoFirstOrder.Code.Execution (A := Language.algebra pp)
      (encryptProgram pp).body
      (.cons
        (Language.liftCarrier pp pk,
          Language.liftCarrier pp message) .nil)
      value cost) :
    ∃ sampleResult : Costed M (ULift.{uGroup} pp.Scalar),
      sampleResult ∈ (pp.algebra.exec .sampleScalar).support ∧
    ∃ firstResult : Costed M (ULift.{uScalar} pp.Carrier),
      firstResult ∈
        (pp.algebra.exec (.smul sampleResult.val.down pp.generator)).support ∧
    ∃ sharedResult : Costed M (ULift.{uScalar} pp.Carrier),
      sharedResult ∈
        (pp.algebra.exec (.smul sampleResult.val.down pk)).support ∧
    ∃ additionResult : Costed M (ULift.{uScalar} pp.Carrier),
      additionResult ∈
        (pp.algebra.exec (.add message sharedResult.val.down)).support ∧
      value = (firstResult.val, additionResult.val) ∧
      cost =
        M.instAddMonoid.add sampleResult.cost
          (M.instAddMonoid.add firstResult.cost
            (M.instAddMonoid.add sharedResult.cost
              (M.instAddMonoid.add additionResult.cost
                M.instAddMonoid.zero))) := by
  unfold encryptProgram at execution
  cases execution with
  | call sampleResult hsample remainingExecution =>
      cases remainingExecution with
      | call firstResult hfirst remainingExecution =>
          cases remainingExecution with
          | call sharedResult hshared remainingExecution =>
              cases remainingExecution with
              | call additionResult haddition returnExecution =>
                  cases returnExecution
                  refine ⟨sampleResult, ?_, firstResult, ?_,
                    sharedResult, ?_, additionResult, ?_, rfl, rfl⟩
                  · simpa [Language.algebra, CryptoFirstOrder.Expr.eval,
                      CryptoFirstOrder.Env.get] using hsample
                  · simpa [Language.algebra, CryptoFirstOrder.Expr.eval,
                      CryptoFirstOrder.Env.get] using hfirst
                  · simpa [Language.algebra, CryptoFirstOrder.Expr.eval,
                      CryptoFirstOrder.Env.get] using hshared
                  · simpa [Language.algebra, CryptoFirstOrder.Expr.eval,
                      CryptoFirstOrder.Env.get] using haddition

/--
Every encryption result records exactly one sampler, two scalar actions, and
one addition path. This theorem exposes the exact costs selected by the sole
DDH handler; it does not consult an upper-bound certificate.
-/
theorem encryptProgram_exactCost
    (pk message : pp.Carrier)
    (result : Costed M
      (Language.CarrierValue pp × Language.CarrierValue pp))
    (hresult : result ∈
      (CryptoFirstOrder.Program.runCosted
        (Language.algebra pp) (encryptProgram pp)
        (Language.liftCarrier pp pk,
          Language.liftCarrier pp message)).support) :
    ∃ sampleResult : Costed M (ULift.{uGroup} pp.Scalar),
      sampleResult ∈ (pp.algebra.exec .sampleScalar).support ∧
    ∃ firstResult : Costed M (ULift.{uScalar} pp.Carrier),
      firstResult ∈
        (pp.algebra.exec (.smul sampleResult.val.down pp.generator)).support ∧
    ∃ sharedResult : Costed M (ULift.{uScalar} pp.Carrier),
      sharedResult ∈
        (pp.algebra.exec (.smul sampleResult.val.down pk)).support ∧
    ∃ additionResult : Costed M (ULift.{uScalar} pp.Carrier),
      additionResult ∈
        (pp.algebra.exec (.add message sharedResult.val.down)).support ∧
      result.val = (firstResult.val, additionResult.val) ∧
      result.cost =
        M.instAddMonoid.add sampleResult.cost
          (M.instAddMonoid.add firstResult.cost
            (M.instAddMonoid.add sharedResult.cost
              (M.instAddMonoid.add additionResult.cost
                M.instAddMonoid.zero))) :=
  encryptExecution_exact pp pk message result.val result.cost
    (CryptoFirstOrder.Code.execution_of_mem_support_runCosted
      (encryptProgram pp).body
      (.cons
        (Language.liftCarrier pp pk,
          Language.liftCarrier pp message) .nil)
      result hresult)

theorem keygenProgram_costBound
    : CryptoFirstOrder.Program.CostBound (Language.algebra pp) (keygenProgram pp)
      (fun _input => keygenBudget pp certificate) :=
  (keygenBoundedProgram pp certificate).certificate

theorem encryptProgram_costBound
    : CryptoFirstOrder.Program.CostBound (Language.algebra pp) (encryptProgram pp)
      (fun _input => encryptBudget pp certificate) :=
  (encryptBoundedProgram pp certificate).certificate

theorem decryptProgram_costBound
    : CryptoFirstOrder.Program.CostBound (Language.algebra pp) (decryptProgram pp)
      (fun _input => decryptBudget pp certificate) :=
  (decryptBoundedProgram pp certificate).certificate

/-- Fixed-parameter encryption projected explicitly to `Nat` runtime. -/
noncomputable def encryptTimedMachine
    : TimedMachine M measure
      (fun _sec => pp.Carrier × pp.Carrier)
      (fun _sec _input => pp.Carrier × pp.Carrier) where
  toProbabilisticMachine :=
    { run := fun _sec input =>
        RandCosted.map (Language.carrierPairDown pp)
          (CryptoFirstOrder.Program.runCosted
            (Language.algebra pp) (encryptProgram pp)
            (Language.liftCarrier pp input.1,
              Language.liftCarrier pp input.2)) }
  certificate :=
    { budget := fun _sec _input => encryptBudget pp certificate
      sound := fun _sec input =>
        RandCosted.CostBound.map
          (encryptProgram_costBound pp certificate
            (Language.liftCarrier pp input.1,
              Language.liftCarrier pp input.2))
          (Language.carrierPairDown pp)
      runtime := fun _sec => measure (encryptBudget pp certificate)
      budget_le_runtime := fun _sec _input => Nat.le_refl _ }

@[simp] theorem encryptTimedMachine_runDist
    (F : Family M Parameter Scalar Carrier) (parameter : Parameter)
    (certificate : Crypto.Assumption.DL.DDH.ParamEfficiencyCertificate
      (F.publicParam parameter))
    (sec : Crypto.SecPar) (input : Carrier × Carrier) :
    (encryptTimedMachine measure (F.publicParam parameter) certificate).runDist sec input =
      (scheme F).encryptDist parameter input.1 input.2 := by
  rfl

end CryptoConstruction.Primitive.Encryption.AsymmetricEncryption.ElGamal

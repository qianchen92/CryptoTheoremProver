import Crypto.Infrastructure.Complexity.ProgramMachine
import Crypto.Infrastructure.Probability.Uniform
import CryptoConstruction.Primitive.Encryption.AsymmetricEncryption.ElGamal.Construction
import Crypto.Primitive.Encryption.AsymmetricEncryption.Syntax

namespace CryptoConstruction.Primitive.Encryption.AsymmetricEncryption.ElGamal

open Crypto.Infrastructure.Complexity
open Crypto.Infrastructure.Computation
open Crypto.Infrastructure.Computation.Algebra
open Crypto.Infrastructure.Computation.Cost
open Crypto.Primitive.Encryption.AsymmetricEncryption
open scoped DDHParameter

universe uCost uScalar uGroup

variable {M : CostModel.{uCost}}

abbrev Family (M : CostModel.{uCost}) :=
  Crypto.Assumption.DL.DDH.Family.{uCost, uScalar, uGroup} M

private abbrev ParameterCertificate
    (pp : PublicParam.{uCost, uScalar, uGroup} M) :=
  Crypto.Assumption.DL.DDH.ParamEfficiencyCertificate pp

/-- Static key-generation budget: one scalar sample and one scalar action. -/
def keygenBudget
    (pp : PublicParam.{uCost, uScalar, uGroup} M)
    (certificate : ParameterCertificate pp) : M.Cost :=
  M.instAddMonoid.add certificate.scalarSampleBudget
    (M.instAddMonoid.add certificate.smulBudget M.instAddMonoid.zero)

/-- One scalar sample, two scalar actions, and one carrier addition. -/
def encryptBudget
    (pp : PublicParam.{uCost, uScalar, uGroup} M)
    (certificate : ParameterCertificate pp) : M.Cost :=
  M.instAddMonoid.add certificate.scalarSampleBudget
      (M.instAddMonoid.add certificate.smulBudget
        (M.instAddMonoid.add certificate.smulBudget
          (M.instAddMonoid.add certificate.addBudget M.instAddMonoid.zero)))

/-- One scalar action followed by one carrier subtraction. -/
def decryptBudget
    (pp : PublicParam.{uCost, uScalar, uGroup} M)
    (certificate : ParameterCertificate pp) : M.Cost :=
  M.instAddMonoid.add certificate.smulBudget certificate.subBudget

/-- ElGamal key generation over the DDH parameter's sole exact algebra. -/
def keygenProgram (pp : PublicParam.{uCost, uScalar, uGroup} M) :
    Program pp.algebra Unit (pp.Carrier × pp.Scalar) where
  body _input :=
    .bind (.call .sampleScalar) fun secretKey =>
      .bind (.call (.smul secretKey.down pp.generator)) fun publicKey =>
        .pure (publicKey.down, secretKey.down)

/-- ElGamal encryption over the DDH parameter's sole exact algebra. -/
def encryptProgram (pp : PublicParam.{uCost, uScalar, uGroup} M) :
    Program pp.algebra (pp.Carrier × pp.Carrier)
      (ULift.{uScalar} (pp.Carrier × pp.Carrier)) where
  body input :=
    .bind (.call .sampleScalar) fun nonce =>
      .bind (.call (.smul nonce.down pp.generator)) fun firstComponent =>
        .bind (.call (.smul nonce.down input.1)) fun shared =>
          .bind (.call (.add input.2 shared.down)) fun secondComponent =>
            .pure (ULift.up (firstComponent.down, secondComponent.down))

/-- ElGamal decryption over the same exact DDH algebra. -/
def decryptProgram (pp : PublicParam.{uCost, uScalar, uGroup} M) :
    Program pp.algebra
      (pp.Scalar × (pp.Carrier × pp.Carrier))
      (ULift.{uScalar} pp.Carrier) where
  body input :=
    .bind (.call (.smul input.1 input.2.1)) fun shared =>
      .call (.sub input.2.2 shared.down)

/-- The key-generation bound indexes the same program body. -/
noncomputable def keygenBoundedProgram
    (pp : PublicParam.{uCost, uScalar, uGroup} M)
    (certificate : ParameterCertificate pp) :
    Program.BoundedProgram
      (Input := Unit) (Output := pp.Carrier × pp.Scalar)
      certificate.bounds (fun _input => keygenBudget pp certificate) where
  program := keygenProgram pp
  certificate := by
    letI := M.instAddMonoid
    intro input
    simpa [keygenProgram, keygenBudget] using
      Program.Code.Bound.bind
        (Program.Code.Bound.weaken
          (Program.Code.Bound.call
            (bounds := certificate.bounds)
            (Crypto.Assumption.DL.DDH.Op.sampleScalar
              (math := pp.toDecisionalCyclicAction)))
          certificate.scalarSampleBudget_sound)
        fun (secretKey : ULift.{uGroup} pp.Scalar) =>
          Program.Code.Bound.bind
            (Program.Code.Bound.weaken
              (Program.Code.Bound.call
                (bounds := certificate.bounds)
                (Crypto.Assumption.DL.DDH.Op.smul
                  secretKey.down pp.generator))
              (certificate.smulBudget_sound secretKey.down pp.generator))
            fun (publicKey : ULift.{uScalar} pp.Carrier) =>
              Program.Code.Bound.pure
                (A := pp.algebra) (publicKey.down, secretKey.down)

/-- The encryption bound indexes the same program body. -/
noncomputable def encryptBoundedProgram
    (pp : PublicParam.{uCost, uScalar, uGroup} M)
    (certificate : ParameterCertificate pp) :
    Program.BoundedProgram
      (Input := pp.Carrier × pp.Carrier)
      (Output := ULift.{uScalar} (pp.Carrier × pp.Carrier))
      certificate.bounds (fun _input => encryptBudget pp certificate) where
  program := encryptProgram pp
  certificate := by
    letI := M.instAddMonoid
    intro input
    simpa [encryptProgram, encryptBudget] using
      Program.Code.Bound.bind
        (Program.Code.Bound.weaken
          (Program.Code.Bound.call
            (bounds := certificate.bounds)
            (Crypto.Assumption.DL.DDH.Op.sampleScalar
              (math := pp.toDecisionalCyclicAction)))
          certificate.scalarSampleBudget_sound)
        fun (nonce : ULift.{uGroup} pp.Scalar) =>
          Program.Code.Bound.bind
            (Program.Code.Bound.weaken
              (Program.Code.Bound.call
                (bounds := certificate.bounds)
                (Crypto.Assumption.DL.DDH.Op.smul nonce.down pp.generator))
              (certificate.smulBudget_sound nonce.down pp.generator))
            fun (firstComponent : ULift.{uScalar} pp.Carrier) =>
              Program.Code.Bound.bind
                (Program.Code.Bound.weaken
                  (Program.Code.Bound.call
                    (bounds := certificate.bounds)
                    (Crypto.Assumption.DL.DDH.Op.smul nonce.down input.1))
                  (certificate.smulBudget_sound nonce.down input.1))
                fun (shared : ULift.{uScalar} pp.Carrier) =>
                  Program.Code.Bound.bind
                    (Program.Code.Bound.weaken
                      (Program.Code.Bound.call
                        (bounds := certificate.bounds)
                        (Crypto.Assumption.DL.DDH.Op.add input.2 shared.down))
                      (certificate.addBudget_sound input.2 shared.down))
                    fun (secondComponent : ULift.{uScalar} pp.Carrier) =>
                      Program.Code.Bound.pure
                        (A := pp.algebra)
                        (ULift.up
                          (firstComponent.down, secondComponent.down))

/-- The decryption bound indexes the same program body. -/
noncomputable def decryptBoundedProgram
    (pp : PublicParam.{uCost, uScalar, uGroup} M)
    (certificate : ParameterCertificate pp) :
    Program.BoundedProgram
      (Input := pp.Scalar × (pp.Carrier × pp.Carrier))
      (Output := ULift.{uScalar} pp.Carrier)
      certificate.bounds (fun _input => decryptBudget pp certificate) where
  program := decryptProgram pp
  certificate := by
    letI := M.instAddMonoid
    intro input
    simpa [decryptProgram, decryptBudget] using
      Program.Code.Bound.bind
        (Program.Code.Bound.weaken
          (Program.Code.Bound.call
            (bounds := certificate.bounds)
            (Crypto.Assumption.DL.DDH.Op.smul input.1 input.2.1))
          (certificate.smulBudget_sound input.1 input.2.1))
        fun (shared : ULift.{uScalar} pp.Carrier) =>
          Program.Code.Bound.weaken
            (Program.Code.Bound.call
              (bounds := certificate.bounds)
              (Crypto.Assumption.DL.DDH.Op.sub input.2.2 shared.down))
            (certificate.subBudget_sound input.2.2 shared.down)

private theorem encryptExecution_exact
    (pp : PublicParam.{uCost, uScalar, uGroup} M)
    (publicKey message : pp.Carrier)
    (value : ULift.{uScalar} (pp.Carrier × pp.Carrier)) (cost : M.Cost)
    (execution : Program.Code.Execution
      ((encryptProgram pp).body (publicKey, message)) value cost) :
    ∃ sampleResult : Costed M (ULift.{uGroup} pp.Scalar),
      sampleResult ∈ (pp.algebra.exec .sampleScalar).support ∧
    ∃ firstResult : Costed M (ULift.{uScalar} pp.Carrier),
      firstResult ∈
        (pp.algebra.exec (.smul sampleResult.val.down pp.generator)).support ∧
    ∃ sharedResult : Costed M (ULift.{uScalar} pp.Carrier),
      sharedResult ∈
        (pp.algebra.exec (.smul sampleResult.val.down publicKey)).support ∧
    ∃ additionResult : Costed M (ULift.{uScalar} pp.Carrier),
      additionResult ∈
        (pp.algebra.exec (.add message sharedResult.val.down)).support ∧
      value = ULift.up (firstResult.val.down, additionResult.val.down) ∧
      cost =
        M.instAddMonoid.add sampleResult.cost
          (M.instAddMonoid.add firstResult.cost
            (M.instAddMonoid.add sharedResult.cost
              (M.instAddMonoid.add additionResult.cost
                M.instAddMonoid.zero))) := by
  simp only [encryptProgram] at execution
  cases execution with
  | bind sampleExecution remainingExecution =>
      cases sampleExecution with
      | call _ sampleResult hsample =>
          cases remainingExecution with
          | bind firstExecution remainingExecution =>
              cases firstExecution with
              | call _ firstResult hfirst =>
                  cases remainingExecution with
                  | bind sharedExecution remainingExecution =>
                      cases sharedExecution with
                      | call _ sharedResult hshared =>
                          cases remainingExecution with
                          | bind additionExecution pureExecution =>
                              cases additionExecution with
                              | call _ additionResult haddition =>
                                  cases pureExecution
                                  refine ⟨sampleResult, hsample, firstResult, hfirst,
                                    sharedResult, hshared, additionResult,
                                    haddition, rfl, rfl⟩

/--
Every encryption result records exactly one sampler, two scalar actions, and
one addition path.  This theorem exposes the exact costs selected by the sole
DDH handler; it does not consult an upper-bound certificate.
-/
theorem encryptProgram_exactCost
    (pp : PublicParam.{uCost, uScalar, uGroup} M)
    (publicKey message : pp.Carrier)
    (result : Costed M (ULift.{uScalar} (pp.Carrier × pp.Carrier)))
    (hresult : result ∈
      (Program.runCosted (encryptProgram pp) (publicKey, message)).support) :
    ∃ sampleResult : Costed M (ULift.{uGroup} pp.Scalar),
      sampleResult ∈ (pp.algebra.exec .sampleScalar).support ∧
    ∃ firstResult : Costed M (ULift.{uScalar} pp.Carrier),
      firstResult ∈
        (pp.algebra.exec (.smul sampleResult.val.down pp.generator)).support ∧
    ∃ sharedResult : Costed M (ULift.{uScalar} pp.Carrier),
      sharedResult ∈
        (pp.algebra.exec (.smul sampleResult.val.down publicKey)).support ∧
    ∃ additionResult : Costed M (ULift.{uScalar} pp.Carrier),
      additionResult ∈
        (pp.algebra.exec (.add message sharedResult.val.down)).support ∧
      result.val = ULift.up (firstResult.val.down, additionResult.val.down) ∧
      result.cost =
        M.instAddMonoid.add sampleResult.cost
          (M.instAddMonoid.add firstResult.cost
            (M.instAddMonoid.add sharedResult.cost
              (M.instAddMonoid.add additionResult.cost
                M.instAddMonoid.zero))) :=
  encryptExecution_exact pp publicKey message result.val result.cost
    (Program.Code.execution_of_mem_support_runCosted
      ((encryptProgram pp).body (publicKey, message)) result hresult)

/-- ElGamal executes setup, key generation, encryption, and decryption only through Programs. -/
noncomputable def scheme (F : Family.{uCost, uScalar, uGroup} M) :
    Scheme M Crypto.SecPar (PublicParam.{uCost, uScalar, uGroup} M)
      PublicKey SecretKey Message Ciphertext where
  setup := fun sec =>
    Program.runCosted (Crypto.Assumption.DL.DDH.setupProgram F) sec
  keygen := fun pp => Program.runCosted (keygenProgram pp) ()
  encrypt := fun pp publicKey message =>
    RandCosted.map ULift.down
      (Program.runCosted (encryptProgram pp) (publicKey, message))
  decrypt := fun pp secretKey ciphertext =>
    RandCosted.map ULift.down
      (Program.runCosted (decryptProgram pp) (secretKey, ciphertext))

@[simp] theorem scheme_setup_eq_family_setup
    (F : Family.{uCost, uScalar, uGroup} M) (sec : Crypto.SecPar) :
    (scheme F).setup sec = F.setup sec :=
  rfl

/-- Erasing key-generation costs recovers ordinary ElGamal key generation. -/
@[simp] theorem keygenProgram_valueDist
    (pp : PublicParam.{uCost, uScalar, uGroup} M) :
    Program.valueDist (keygenProgram pp) () =
      PMF.bind
        (Crypto.Infrastructure.Probability.uniformPMF pp.Scalar)
        (fun secretKey => PMF.pure (secretKey • pp.generator, secretKey)) := by
  change Program.Code.valueDist ((keygenProgram pp).body ()) = _
  simp [keygenProgram,
    Program.Code.valueDist_call_eq
      (Crypto.Assumption.DL.DDH.algebraLaws pp),
    Crypto.Assumption.DL.DDH.algebraLaws, Function.comp_def]

/-- Erasing encryption costs recovers ordinary ElGamal encryption. -/
@[simp] theorem encryptProgram_valueDist
    (pp : PublicParam.{uCost, uScalar, uGroup} M)
    (publicKey message : pp.Carrier) :
    PMF.map ULift.down
        (Program.valueDist (encryptProgram pp) (publicKey, message)) =
      PMF.bind
        (Crypto.Infrastructure.Probability.uniformPMF pp.Scalar)
        (fun nonce =>
          PMF.pure (nonce • pp.generator, message + nonce • publicKey)) := by
  change PMF.map ULift.down
    (Program.Code.valueDist
      ((encryptProgram pp).body (publicKey, message))) = _
  simp [encryptProgram,
    Program.Code.valueDist_call_eq
      (Crypto.Assumption.DL.DDH.algebraLaws pp),
    Crypto.Assumption.DL.DDH.algebraLaws,
    PMF.map_bind, PMF.pure_map, Function.comp_def]

/-- Erasing decryption costs recovers ordinary ElGamal decryption. -/
@[simp] theorem decryptProgram_valueDist
    (pp : PublicParam.{uCost, uScalar, uGroup} M)
    (secretKey : pp.Scalar) (ciphertext : pp.Carrier × pp.Carrier) :
    PMF.map ULift.down
        (Program.valueDist (decryptProgram pp) (secretKey, ciphertext)) =
      PMF.pure (ciphertext.2 - secretKey • ciphertext.1) := by
  change PMF.map ULift.down
    (Program.Code.valueDist
      ((decryptProgram pp).body (secretKey, ciphertext))) = _
  simp [decryptProgram,
    Program.Code.valueDist_call_eq
      (Crypto.Assumption.DL.DDH.algebraLaws pp),
    Crypto.Assumption.DL.DDH.algebraLaws, PMF.pure_map]

@[simp] theorem scheme_setupDist
    (F : Family.{uCost, uScalar, uGroup} M) (sec : Crypto.SecPar) :
    (scheme F).setupDist sec = F.setupDist sec :=
  rfl

@[simp] theorem scheme_keygenDist
    (F : Family.{uCost, uScalar, uGroup} M)
    (pp : PublicParam.{uCost, uScalar, uGroup} M) :
    (scheme F).keygenDist pp =
      PMF.bind
        (Crypto.Infrastructure.Probability.uniformPMF pp.Scalar)
        (fun secretKey => PMF.pure (secretKey • pp.generator, secretKey)) :=
  keygenProgram_valueDist pp

@[simp] theorem scheme_encryptDist
    (F : Family.{uCost, uScalar, uGroup} M)
    (pp : PublicParam.{uCost, uScalar, uGroup} M)
    (publicKey message : pp.Carrier) :
    (scheme F).encryptDist pp publicKey message =
      PMF.bind
        (Crypto.Infrastructure.Probability.uniformPMF pp.Scalar)
        (fun nonce =>
          PMF.pure (nonce • pp.generator, message + nonce • publicKey)) := by
  unfold Scheme.encryptDist scheme
  rw [RandCosted.valueDist_map]
  exact encryptProgram_valueDist pp publicKey message

@[simp] theorem scheme_decryptDist
    (F : Family.{uCost, uScalar, uGroup} M)
    (pp : PublicParam.{uCost, uScalar, uGroup} M)
    (secretKey : pp.Scalar) (ciphertext : pp.Carrier × pp.Carrier) :
    (scheme F).decryptDist pp secretKey ciphertext =
      PMF.pure (ciphertext.2 - secretKey • ciphertext.1) := by
  unfold Scheme.decryptDist scheme
  rw [RandCosted.valueDist_map]
  exact decryptProgram_valueDist pp secretKey ciphertext

theorem keygenProgram_costBound
    (pp : PublicParam.{uCost, uScalar, uGroup} M)
    (certificate : ParameterCertificate pp) :
    Program.CostBound (keygenProgram pp)
      (fun _input => keygenBudget pp certificate) :=
  (keygenBoundedProgram pp certificate).costBound

theorem encryptProgram_costBound
    (pp : PublicParam.{uCost, uScalar, uGroup} M)
    (certificate : ParameterCertificate pp) :
    Program.CostBound (encryptProgram pp)
      (fun _input => encryptBudget pp certificate) :=
  (encryptBoundedProgram pp certificate).costBound

theorem decryptProgram_costBound
    (pp : PublicParam.{uCost, uScalar, uGroup} M)
    (certificate : ParameterCertificate pp) :
    Program.CostBound (decryptProgram pp)
      (fun _input => decryptBudget pp certificate) :=
  (decryptBoundedProgram pp certificate).costBound

/-- Fixed-parameter encryption projected explicitly to `Nat` runtime. -/
noncomputable def encryptTimedMachine
    (measure : NatMeasure M)
    (pp : PublicParam.{uCost, uScalar, uGroup} M)
    (certificate : ParameterCertificate pp) :
    TimedMachine M measure
      (fun _sec => pp.Carrier × pp.Carrier)
      (fun _sec _input => pp.Carrier × pp.Carrier) :=
  (TimedMachine.ofBoundedProgram measure
      (fun _sec => pp.algebra)
      (fun _sec => certificate.bounds)
      (fun _sec _input => encryptBudget pp certificate)
      (fun _sec => measure (encryptBudget pp certificate))
      (fun _sec => encryptBoundedProgram pp certificate)
      (by
        intro sec input
        exact Nat.le_refl _)).map
    (fun _sec _input result => result.down)

@[simp] theorem encryptTimedMachine_runDist
    (measure : NatMeasure M)
    (F : Family.{uCost, uScalar, uGroup} M)
    (pp : PublicParam.{uCost, uScalar, uGroup} M)
    (certificate : ParameterCertificate pp)
    (sec : Crypto.SecPar) (input : pp.Carrier × pp.Carrier) :
    (encryptTimedMachine measure pp certificate).runDist sec input =
      (scheme F).encryptDist pp input.1 input.2 := by
  rfl

end CryptoConstruction.Primitive.Encryption.AsymmetricEncryption.ElGamal

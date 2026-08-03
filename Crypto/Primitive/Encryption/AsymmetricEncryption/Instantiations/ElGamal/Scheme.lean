import Crypto.Assumption.DL.DDH
import Crypto.Infrastructure.Complexity.ProgramMachine
import Crypto.Primitive.Encryption.AsymmetricEncryption.Instantiations.ElGamal.Construction
import Crypto.Primitive.Encryption.AsymmetricEncryption.Syntax

namespace Crypto.Primitive.Encryption.AsymmetricEncryption.Instantiations.ElGamal

open Crypto.Infrastructure.Complexity
open Crypto.Infrastructure.Computation
open Crypto.Infrastructure.Computation.Algebra
open Crypto.Infrastructure.Computation.Cost
open Crypto.Primitive.Encryption.AsymmetricEncryption
open scoped DDHParameter

universe uScalar uGroup

abbrev Family :=
  Crypto.Assumption.DL.DDH.Family.{uScalar, uGroup}

/-- Static key-generation budget: one scalar sample and one scalar multiplication. -/
def keygenBudget
    (pp : PublicParam.{uScalar, uGroup})
    (certificate :
      Crypto.Assumption.DL.DDH.ParamEfficiencyCertificate pp) : Cost :=
  certificate.scalarSamplerBounds.sampleBudget +
    certificate.additiveBounds.smulBudget

/-- One scalar sample, two scalar multiplications, and one group addition. -/
def encryptBudget
    (pp : PublicParam.{uScalar, uGroup})
    (certificate :
      Crypto.Assumption.DL.DDH.ParamEfficiencyCertificate pp) : Cost :=
  certificate.scalarSamplerBounds.sampleBudget +
    (certificate.additiveBounds.smulBudget +
      (certificate.additiveBounds.smulBudget +
        certificate.additiveBounds.addBudget))

/-- One scalar multiplication followed by one subtraction. -/
def decryptBudget
    (pp : PublicParam.{uScalar, uGroup})
    (certificate :
      Crypto.Assumption.DL.DDH.ParamEfficiencyCertificate pp) : Cost :=
  certificate.additiveBounds.smulBudget +
    certificate.additiveBounds.subBudget

/-- Exactly the primitive capabilities used by ElGamal at one public parameter. -/
inductive Op (pp : PublicParam.{uScalar, uGroup}) :
    Type (max uScalar uGroup) → Type (max uScalar uGroup + 1) where
  | sampleScalar : Op pp (ULift.{uGroup} pp.Scalar)
  | add (left right : pp.Carrier) : Op pp (ULift.{uScalar} pp.Carrier)
  | sub (left right : pp.Carrier) : Op pp (ULift.{uScalar} pp.Carrier)
  | smul (scalar : pp.Scalar) (value : pp.Carrier) :
      Op pp (ULift.{uScalar} pp.Carrier)

/-- The typed primitive signature selected by one ElGamal parameter. -/
def signature (pp : PublicParam.{uScalar, uGroup}) : Signature where
  Op := Op pp

/-- The sole exact interpreter for ElGamal primitive operations. -/
noncomputable def algebra (pp : PublicParam.{uScalar, uGroup}) :
    CostedAlgebra natCostModel (signature pp) where
  exec operation :=
    match operation with
    | .sampleScalar => RandCosted.map ULift.up pp.scalarSampler.sample
    | .add left right =>
        RandCosted.liftCosted (Costed.map ULift.up (pp.backend.add left right))
    | .sub left right =>
        RandCosted.liftCosted (Costed.map ULift.up (pp.backend.sub left right))
    | .smul scalar value =>
        RandCosted.liftCosted (Costed.map ULift.up (pp.backend.smul scalar value))

/-- Cost-erased mathematical specifications for the exact ElGamal handler. -/
noncomputable def algebraLaws (pp : PublicParam.{uScalar, uGroup}) :
    AlgebraLaws (algebra pp) where
  semantics operation :=
    match operation with
    | .sampleScalar =>
        PMF.map ULift.up
          (Crypto.Infrastructure.Computation.Distribution.uniformPMF pp.Scalar)
    | .add left right => PMF.pure (ULift.up (left + right))
    | .sub left right => PMF.pure (ULift.up (left - right))
    | .smul scalar value => PMF.pure (ULift.up (scalar • value))
  exec_spec operation := by
    cases operation with
    | sampleScalar =>
        simpa [algebra] using
          congrArg (PMF.map ULift.up) pp.scalarSamplerLaws.sample_spec
    | add left right => simp [algebra]
    | sub left right => simp [algebra]
    | smul scalar value => simp [algebra]

/-- Independent operation bounds for the exact ElGamal handler. -/
noncomputable def operationBounds
    (pp : PublicParam.{uScalar, uGroup})
    (certificate : Crypto.Assumption.DL.DDH.ParamEfficiencyCertificate pp) :
    OperationBounds (algebra pp) where
  budget operation :=
    match operation with
    | .sampleScalar => certificate.scalarSamplerBounds.sampleBudget
    | .add _ _ => certificate.additiveBounds.addBudget
    | .sub _ _ => certificate.additiveBounds.subBudget
    | .smul _ _ => certificate.additiveBounds.smulBudget
  cost_le operation result hresult := by
    cases operation with
    | sampleScalar =>
        simp only [algebra, RandCosted.map, RandCostedT.map] at hresult
        rw [PMF.mem_support_map_iff] at hresult
        rcases hresult with ⟨sampleResult, hsampleResult, hresult⟩
        subst result
        exact certificate.scalarSamplerBounds.cost_le sampleResult hsampleResult
    | add left right =>
        simp only [algebra, RandCosted.liftCosted, RandCostedT.liftCosted] at hresult
        rw [PMF.mem_support_pure_iff] at hresult
        subst result
        exact certificate.additiveBounds.addCost_le left right
    | sub left right =>
        simp only [algebra, RandCosted.liftCosted, RandCostedT.liftCosted] at hresult
        rw [PMF.mem_support_pure_iff] at hresult
        subst result
        exact certificate.additiveBounds.subCost_le left right
    | smul scalar value =>
        simp only [algebra, RandCosted.liftCosted, RandCostedT.liftCosted] at hresult
        rw [PMF.mem_support_pure_iff] at hresult
        subst result
        exact certificate.additiveBounds.smulCost_le scalar value

/-- ElGamal key generation, represented once as an input-parameterized program. -/
def keygenProgram (pp : PublicParam.{uScalar, uGroup}) :
    Program (algebra pp) Unit (pp.Carrier × pp.Scalar) where
  body _input :=
    .bind (.call .sampleScalar) fun secretKey =>
      .bind (.call (.smul secretKey.down pp.generator)) fun publicKey =>
        .pure (publicKey.down, secretKey.down)

/-- ElGamal encryption, represented once as an input-parameterized program. -/
def encryptProgram (pp : PublicParam.{uScalar, uGroup}) :
    Program (algebra pp) (pp.Carrier × pp.Carrier)
      (ULift.{uScalar} (pp.Carrier × pp.Carrier)) where
  body input :=
    .bind (.call .sampleScalar) fun nonce =>
      .bind (.call (.smul nonce.down pp.generator)) fun firstComponent =>
        .bind (.call (.smul nonce.down input.1)) fun shared =>
          .bind (.call (.add input.2 shared.down)) fun secondComponent =>
            .pure (ULift.up (firstComponent.down, secondComponent.down))

/-- ElGamal decryption syntax over its exact primitive algebra. -/
def decryptProgram (pp : PublicParam.{uScalar, uGroup}) :
    Program (algebra pp)
      (pp.Scalar × (pp.Carrier × pp.Carrier))
      (ULift.{uScalar} pp.Carrier) where
  body input :=
    .bind (.call (.smul input.1 input.2.1)) fun shared =>
      .call (.sub input.2.2 shared.down)

/-- Structural budget certificate for the single key-generation program. -/
noncomputable def keygenBoundedProgram
    (pp : PublicParam.{uScalar, uGroup})
    (certificate : Crypto.Assumption.DL.DDH.ParamEfficiencyCertificate pp) :
    Program.BoundedProgram
      (Input := Unit) (Output := pp.Carrier × pp.Scalar)
      (operationBounds pp certificate)
      (fun _input => keygenBudget pp certificate) where
  program := keygenProgram pp
  certificate := by
    intro input
    simpa [keygenProgram, keygenBudget] using
      Program.Code.Bound.bind
        (Program.Code.Bound.call (A := algebra pp) Op.sampleScalar)
        fun (secretKey : ULift.{uGroup} pp.Scalar) =>
          Program.Code.Bound.bind
            (Program.Code.Bound.call
              (A := algebra pp) (Op.smul secretKey.down pp.generator))
            fun (publicKey : ULift.{uScalar} pp.Carrier) =>
              Program.Code.Bound.pure
                (A := algebra pp) (publicKey.down, secretKey.down)

/-- Structural budget certificate for the single encryption program. -/
noncomputable def encryptBoundedProgram
    (pp : PublicParam.{uScalar, uGroup})
    (certificate : Crypto.Assumption.DL.DDH.ParamEfficiencyCertificate pp) :
    Program.BoundedProgram
      (Input := pp.Carrier × pp.Carrier)
      (Output := ULift.{uScalar} (pp.Carrier × pp.Carrier))
      (operationBounds pp certificate)
      (fun _input => encryptBudget pp certificate) where
  program := encryptProgram pp
  certificate := by
    intro input
    simpa [encryptProgram, encryptBudget] using
      Program.Code.Bound.bind
        (Program.Code.Bound.call (A := algebra pp) Op.sampleScalar)
        fun (nonce : ULift.{uGroup} pp.Scalar) =>
          Program.Code.Bound.bind
            (Program.Code.Bound.call
              (A := algebra pp) (Op.smul nonce.down pp.generator))
            fun (firstComponent : ULift.{uScalar} pp.Carrier) =>
              Program.Code.Bound.bind
                (Program.Code.Bound.call
                  (A := algebra pp) (Op.smul nonce.down input.1))
                fun (shared : ULift.{uScalar} pp.Carrier) =>
                  Program.Code.Bound.bind
                    (Program.Code.Bound.call
                      (A := algebra pp) (Op.add input.2 shared.down))
                    fun (secondComponent : ULift.{uScalar} pp.Carrier) =>
                      Program.Code.Bound.pure
                        (A := algebra pp)
                        (ULift.up
                          (firstComponent.down, secondComponent.down))

/-- Structural budget certificate for the single decryption program. -/
noncomputable def decryptBoundedProgram
    (pp : PublicParam.{uScalar, uGroup})
    (certificate : Crypto.Assumption.DL.DDH.ParamEfficiencyCertificate pp) :
    Program.BoundedProgram
      (Input := pp.Scalar × (pp.Carrier × pp.Carrier))
      (Output := ULift.{uScalar} pp.Carrier)
      (operationBounds pp certificate)
      (fun _input => decryptBudget pp certificate) where
  program := decryptProgram pp
  certificate := by
    intro input
    simpa [decryptProgram, decryptBudget] using
      Program.Code.Bound.bind
        (Program.Code.Bound.call
          (A := algebra pp) (Op.smul input.1 input.2.1))
        fun (shared : ULift.{uScalar} pp.Carrier) =>
          Program.Code.Bound.call
            (A := algebra pp) (Op.sub input.2.2 shared.down)

/-- Costed ElGamal key generation. -/
noncomputable def keygenComputation
    (pp : PublicParam.{uScalar, uGroup}) :
    RandCosted (pp.Carrier × pp.Scalar) :=
  Program.runCosted (keygenProgram pp) ()

/-- Costed ElGamal encryption. -/
noncomputable def encryptComputation
    (pp : PublicParam.{uScalar, uGroup})
    (publicKey message : pp.Carrier) :
    RandCosted (pp.Carrier × pp.Carrier) :=
  RandCosted.map ULift.down
    (Program.runCosted (encryptProgram pp) (publicKey, message))

/--
Every concrete encryption result comes from one scalar-sampler path, and its
cost is exactly the sequential sum of the four primitive costs on that path.

This is extracted from the typed program's structural execution relation; it
does not consult the independent upper-bound certificate.
-/
theorem encryptComputation_exactCost
    (pp : PublicParam.{uScalar, uGroup})
    (publicKey message : pp.Carrier)
    (result : Costed (pp.Carrier × pp.Carrier))
    (hresult : result ∈ (encryptComputation pp publicKey message).support) :
    ∃ sampleResult : Costed pp.Scalar,
      sampleResult ∈ pp.scalarSampler.sample.support ∧
      result.val =
        ((pp.backend.smul sampleResult.val pp.generator).val,
          (pp.backend.add message
            (pp.backend.smul sampleResult.val publicKey).val).val) ∧
      result.cost =
        sampleResult.cost +
          ((pp.backend.smul sampleResult.val pp.generator).cost +
            ((pp.backend.smul sampleResult.val publicKey).cost +
              (pp.backend.add message
                (pp.backend.smul sampleResult.val publicKey).val).cost)) := by
  simp only [encryptComputation, RandCosted.map, RandCostedT.map] at hresult
  rw [PMF.mem_support_map_iff] at hresult
  rcases hresult with ⟨liftedResult, hliftedResult, hresult⟩
  subst result
  rcases liftedResult with ⟨liftedValue, liftedCost⟩
  have hexecution :=
    Program.Code.execution_of_mem_support_runCosted
      ((encryptProgram pp).body (publicKey, message))
      ⟨liftedValue, liftedCost⟩ hliftedResult
  simp only [encryptProgram] at hexecution
  cases hexecution with
  | bind sampleExecution remainingExecution =>
      cases sampleExecution with
      | call _ sampleLifted hsampleLifted =>
          simp only [algebra, RandCosted.map, RandCostedT.map] at hsampleLifted
          rw [PMF.mem_support_map_iff] at hsampleLifted
          rcases hsampleLifted with ⟨sampleResult, hsampleResult, hsampleLifted⟩
          subst sampleLifted
          cases remainingExecution with
          | bind firstExecution remainingExecution =>
              cases firstExecution with
              | call _ firstResult hfirstResult =>
                  simp only [algebra, RandCosted.liftCosted,
                    RandCostedT.liftCosted] at hfirstResult
                  rw [PMF.mem_support_pure_iff] at hfirstResult
                  subst firstResult
                  cases remainingExecution with
                  | bind sharedExecution remainingExecution =>
                      cases sharedExecution with
                      | call _ sharedResult hsharedResult =>
                          simp only [algebra, RandCosted.liftCosted,
                            RandCostedT.liftCosted] at hsharedResult
                          rw [PMF.mem_support_pure_iff] at hsharedResult
                          subst sharedResult
                          cases remainingExecution with
                          | bind addExecution pureExecution =>
                              cases addExecution with
                              | call _ addResult haddResult =>
                                  simp only [algebra, RandCosted.liftCosted,
                                    RandCostedT.liftCosted] at haddResult
                                  rw [PMF.mem_support_pure_iff] at haddResult
                                  subst addResult
                                  cases pureExecution
                                  refine ⟨sampleResult, hsampleResult, rfl, ?_⟩
                                  change
                                    sampleResult.cost +
                                        ((pp.backend.smul sampleResult.val
                                            pp.generator).cost +
                                          ((pp.backend.smul sampleResult.val
                                              publicKey).cost +
                                            ((pp.backend.add message
                                                (pp.backend.smul sampleResult.val
                                                  publicKey).val).cost + 0))) = _
                                  simp only [add_zero]

/-- Deterministic compatibility boundary for the generic encryption scheme. -/
def decryptComputation
    (pp : PublicParam.{uScalar, uGroup})
    (secretKey : pp.Scalar) (ciphertext : pp.Carrier × pp.Carrier) :
    Costed pp.Carrier :=
  Costed.bind (pp.backend.smul secretKey ciphertext.1) fun shared =>
    pp.backend.sub ciphertext.2 shared

/-- The deterministic writer is exactly the point-mass program interpretation. -/
@[simp] theorem decryptProgram_runCosted
    (pp : PublicParam.{uScalar, uGroup})
    (secretKey : pp.Scalar) (ciphertext : pp.Carrier × pp.Carrier) :
    Program.runCosted (decryptProgram pp) (secretKey, ciphertext) =
      RandCosted.map ULift.up
        (RandCosted.liftCosted
          (decryptComputation pp secretKey ciphertext)) := by
  simp [Program.runCosted, decryptProgram, Program.Code.runCosted,
    algebra, RandCostedT.bind, decryptComputation,
    RandCosted.liftCosted, RandCostedT.liftCosted, Costed.bind,
    CostedT.bind, CostedT.map, PMF.pure_map]

/-- ElGamal with execution-path costs derived from its typed program. -/
noncomputable def scheme (F : Family.{uScalar, uGroup}) :
    Scheme Crypto.SecPar PublicParam PublicKey SecretKey Message Ciphertext where
  setup := fun sec =>
    Program.runCosted (Crypto.Assumption.DL.DDH.setupProgram F) sec
  keygen := keygenComputation
  encrypt := encryptComputation
  decrypt := decryptComputation

/-- ElGamal setup is the exact typed DDH setup program, with no semantic change. -/
@[simp] theorem scheme_setup_eq_family_setup
    (F : Family.{uScalar, uGroup}) (sec : Crypto.SecPar) :
    (scheme F).setup sec = F.setup sec := by
  rfl

/-- Erasing key-generation costs recovers semantic ElGamal key generation. -/
@[simp] theorem keygenComputation_valueDist
    (pp : PublicParam.{uScalar, uGroup}) :
    RandCosted.valueDist (keygenComputation pp) =
      PMF.bind
        (Crypto.Infrastructure.Computation.Distribution.uniformPMF pp.Scalar)
        (fun secretKey => PMF.pure (secretKey • pp.generator, secretKey)) := by
  change Program.Code.valueDist ((keygenProgram pp).body ()) = _
  simp [keygenProgram,
    Program.Code.valueDist_call_eq (algebraLaws pp), algebraLaws,
    Function.comp_def]

/-- Erasing encryption costs recovers semantic ElGamal encryption. -/
@[simp] theorem encryptComputation_valueDist
    (pp : PublicParam.{uScalar, uGroup})
    (publicKey message : pp.Carrier) :
    RandCosted.valueDist (encryptComputation pp publicKey message) =
      PMF.bind
        (Crypto.Infrastructure.Computation.Distribution.uniformPMF pp.Scalar)
        (fun nonce =>
          PMF.pure (nonce • pp.generator, message + nonce • publicKey)) := by
  unfold encryptComputation
  rw [RandCosted.valueDist_map]
  change
    PMF.map ULift.down
      (Program.Code.valueDist
        ((encryptProgram pp).body (publicKey, message))) = _
  simp [encryptProgram,
    Program.Code.valueDist_call_eq (algebraLaws pp), algebraLaws,
    PMF.map_bind, PMF.pure_map, Function.comp_def]

/-- The deterministic costed decryption has the ordinary ElGamal value. -/
@[simp] theorem decryptComputation_value
    (pp : PublicParam.{uScalar, uGroup})
    (secretKey : pp.Scalar) (ciphertext : pp.Carrier × pp.Carrier) :
    (decryptComputation pp secretKey ciphertext).val =
      ciphertext.2 - secretKey • ciphertext.1 := by
  simp [decryptComputation, Costed.bind]

/-- Cost erasure at the scheme boundary recovers semantic DDH setup. -/
@[simp] theorem scheme_setupDist
    (F : Family.{uScalar, uGroup}) (sec : Crypto.SecPar) :
    (scheme F).setupDist sec = F.setupDist sec := by
  simp [Scheme.setupDist, scheme,
    Crypto.Assumption.DL.DDH.Family.setupDist]

/-- Cost erasure exposes the ordinary ElGamal key distribution. -/
@[simp] theorem scheme_keygenDist
    (F : Family.{uScalar, uGroup}) (pp : PublicParam.{uScalar, uGroup}) :
    (scheme F).keygenDist pp =
      PMF.bind
        (Crypto.Infrastructure.Computation.Distribution.uniformPMF pp.Scalar)
        (fun secretKey => PMF.pure (secretKey • pp.generator, secretKey)) := by
  simp [Scheme.keygenDist, scheme]

/-- Cost erasure exposes the ordinary ElGamal encryption distribution. -/
@[simp] theorem scheme_encryptDist
    (F : Family.{uScalar, uGroup}) (pp : PublicParam.{uScalar, uGroup})
    (publicKey message : pp.Carrier) :
    (scheme F).encryptDist pp publicKey message =
      PMF.bind
        (Crypto.Infrastructure.Computation.Distribution.uniformPMF pp.Scalar)
        (fun nonce =>
          PMF.pure (nonce • pp.generator, message + nonce • publicKey)) := by
  simp [Scheme.encryptDist, scheme]

/-- Cost erasure exposes ordinary ElGamal decryption. -/
@[simp] theorem scheme_decryptValue
    (F : Family.{uScalar, uGroup}) (pp : PublicParam.{uScalar, uGroup})
    (secretKey : pp.Scalar) (ciphertext : pp.Carrier × pp.Carrier) :
    (scheme F).decryptValue pp secretKey ciphertext =
      ciphertext.2 - secretKey • ciphertext.1 := by
  simp [Scheme.decryptValue, scheme]

/-- The key-generation program has its advertised input-independent budget. -/
theorem keygenProgram_costBound
    (pp : PublicParam.{uScalar, uGroup})
    (certificate : Crypto.Assumption.DL.DDH.ParamEfficiencyCertificate pp) :
    Program.CostBound (keygenProgram pp)
      (fun _input => keygenBudget pp certificate) :=
  (keygenBoundedProgram pp certificate).costBound

/-- The encryption program has its advertised compositional budget. -/
theorem encryptProgram_costBound
    (pp : PublicParam.{uScalar, uGroup})
    (certificate : Crypto.Assumption.DL.DDH.ParamEfficiencyCertificate pp) :
    Program.CostBound (encryptProgram pp)
      (fun _input => encryptBudget pp certificate) :=
  (encryptBoundedProgram pp certificate).costBound

/-- The decryption program has its advertised compositional budget. -/
theorem decryptProgram_costBound
    (pp : PublicParam.{uScalar, uGroup})
    (certificate : Crypto.Assumption.DL.DDH.ParamEfficiencyCertificate pp) :
    Program.CostBound (decryptProgram pp)
      (fun _input => decryptBudget pp certificate) :=
  (decryptBoundedProgram pp certificate).costBound

/-- Every costed key-generation path satisfies the static budget. -/
theorem keygenComputation_costBound
    (pp : PublicParam.{uScalar, uGroup})
    (certificate : Crypto.Assumption.DL.DDH.ParamEfficiencyCertificate pp) :
    ∀ result, result ∈ (keygenComputation pp).support →
      result.cost ≤ keygenBudget pp certificate :=
  keygenProgram_costBound pp certificate ()

/-- Every costed encryption path satisfies the static budget. -/
theorem encryptComputation_costBound
    (pp : PublicParam.{uScalar, uGroup})
    (certificate : Crypto.Assumption.DL.DDH.ParamEfficiencyCertificate pp)
    (publicKey message : pp.Carrier) :
    ∀ result, result ∈ (encryptComputation pp publicKey message).support →
      result.cost ≤ encryptBudget pp certificate :=
  by
    intro result hresult
    simp only [encryptComputation, RandCosted.map, RandCostedT.map] at hresult
    rw [PMF.mem_support_map_iff] at hresult
    rcases hresult with ⟨liftedResult, hliftedResult, hresult⟩
    subst result
    exact encryptProgram_costBound pp certificate
      (publicKey, message) liftedResult hliftedResult

/-- Deterministic costed decryption satisfies the static budget. -/
theorem decryptComputation_cost_le
    (pp : PublicParam.{uScalar, uGroup})
    (certificate : Crypto.Assumption.DL.DDH.ParamEfficiencyCertificate pp)
    (secretKey : pp.Scalar) (ciphertext : pp.Carrier × pp.Carrier) :
    (decryptComputation pp secretKey ciphertext).cost ≤
      decryptBudget pp certificate :=
  Nat.add_le_add
    (certificate.additiveBounds.smulCost_le secretKey ciphertext.1)
    (certificate.additiveBounds.subCost_le ciphertext.2
      (pp.backend.smul secretKey ciphertext.1).val)

/-- ElGamal encryption at a fixed parameter as a program-derived timed machine. -/
noncomputable def encryptTimedMachine
    (pp : PublicParam.{uScalar, uGroup})
    (certificate : Crypto.Assumption.DL.DDH.ParamEfficiencyCertificate pp) :
  TimedMachine (pp.Carrier × pp.Carrier) (pp.Carrier × pp.Carrier) :=
  TimedMachine.ofMappedBoundedProgram
    NatMeasure.nat
    (fun _sec => algebra pp)
    (fun _sec => operationBounds pp certificate)
    (fun _sec _input => encryptBudget pp certificate)
    (fun _sec => encryptBudget pp certificate)
    ULift.down
    (fun _sec => encryptBoundedProgram pp certificate)
    (by
      intro sec input
      exact Nat.le_refl _)

/-- The timed encryption machine has exactly the semantic ElGamal distribution. -/
@[simp] theorem encryptTimedMachine_runDist
    (F : Family.{uScalar, uGroup}) (pp : PublicParam.{uScalar, uGroup})
    (certificate : Crypto.Assumption.DL.DDH.ParamEfficiencyCertificate pp)
    (sec : Crypto.SecPar) (input : pp.Carrier × pp.Carrier) :
    (encryptTimedMachine pp certificate).runDist sec input =
      (scheme F).encryptDist pp input.1 input.2 := by
  change
    RandCosted.valueDist
      (RandCosted.map ULift.down
        (RandCostedT.mapCost NatMeasure.nat
          (Program.runCosted (encryptProgram pp) input))) =
      RandCosted.valueDist (encryptComputation pp input.1 input.2)
  rw [RandCosted.valueDist_map, RandCostedT.valueDist_mapCost]
  unfold encryptComputation
  rw [RandCosted.valueDist_map]

end Crypto.Primitive.Encryption.AsymmetricEncryption.Instantiations.ElGamal

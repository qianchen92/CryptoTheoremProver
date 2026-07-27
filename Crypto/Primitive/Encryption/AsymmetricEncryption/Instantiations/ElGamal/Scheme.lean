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

universe uScalar uGroup

abbrev Family :=
  Crypto.Assumption.DL.DDH.Family.{uScalar, uGroup}

/-- Static key-generation budget: one scalar sample and one scalar multiplication. -/
def keygenBudget
    (pp : PublicParam.{uScalar, uGroup})
    (certificate :
      Crypto.Assumption.DL.DDH.ParamEfficiencyCertificate pp) : Cost :=
  pp.scalarSampler.sampleBudget +
    certificate.additiveBounds.smulBudget

/--
Static encryption budget: one scalar sample, two scalar multiplications, and
one group addition.
-/
def encryptBudget
    (pp : PublicParam.{uScalar, uGroup})
    (certificate :
      Crypto.Assumption.DL.DDH.ParamEfficiencyCertificate pp) : Cost :=
  pp.scalarSampler.sampleBudget +
    (certificate.additiveBounds.smulBudget +
      (certificate.additiveBounds.smulBudget +
        certificate.additiveBounds.addBudget))

/-- Static decryption budget: one scalar multiplication and one subtraction. -/
def decryptBudget
    (pp : PublicParam.{uScalar, uGroup})
    (certificate :
      Crypto.Assumption.DL.DDH.ParamEfficiencyCertificate pp) : Cost :=
  certificate.additiveBounds.smulBudget +
    certificate.additiveBounds.subBudget

/-- ElGamal key-generation syntax, independent of any efficiency certificate. -/
def keygenProgram
    (pp : PublicParam.{uScalar, uGroup}) :
    Program pp.Scalar pp.Carrier pp.Scalar
      pp.backend pp.scalarSampler
      (pp.Carrier × pp.Scalar) :=
  Program.bindSample
    (Program.sample
      (backend := pp.backend)
      (sampler := pp.scalarSampler))
    (fun secretKey =>
      Program.bindCarrier
        (Program.smul
          (backend := pp.backend)
          (sampler := pp.scalarSampler)
          secretKey pp.generator)
        (fun publicKey => Program.pure (publicKey, secretKey)))

/-- ElGamal encryption syntax, independent of any efficiency certificate. -/
def encryptProgram
    (pp : PublicParam.{uScalar, uGroup})
    (publicKey message : pp.Carrier) :
    Program pp.Scalar pp.Carrier pp.Scalar
      pp.backend pp.scalarSampler
      (ULift.{uScalar} (pp.Carrier × pp.Carrier)) :=
  Program.bindSample
    (Program.sample
      (backend := pp.backend)
      (sampler := pp.scalarSampler))
    (fun nonce =>
      Program.bindCarrier
        (Program.smul
          (backend := pp.backend)
          (sampler := pp.scalarSampler)
          nonce pp.generator)
        (fun firstComponent =>
          Program.bindCarrier
            (Program.smul
              (backend := pp.backend)
              (sampler := pp.scalarSampler)
              nonce publicKey)
            (fun shared =>
              Program.bindCarrier
                (Program.add
                  (backend := pp.backend)
                  (sampler := pp.scalarSampler)
                  message shared)
                (fun secondComponent =>
                  Program.pure
                    (ULift.up (firstComponent, secondComponent))))))

/-- ElGamal decryption syntax, independent of any efficiency certificate. -/
def decryptProgram
    (pp : PublicParam.{uScalar, uGroup})
    (secretKey : pp.Scalar) (ciphertext : pp.Carrier × pp.Carrier) :
    Program pp.Scalar pp.Carrier pp.Scalar
      pp.backend pp.scalarSampler
      (ULift.{uScalar} pp.Carrier) :=
  Program.bindCarrier
    (Program.smul
      (backend := pp.backend)
      (sampler := pp.scalarSampler)
      secretKey ciphertext.1)
    (fun shared =>
      Program.sub
        (backend := pp.backend)
        (sampler := pp.scalarSampler)
        ciphertext.2 shared)

/-- Statically bounded ElGamal key generation. -/
def keygenBoundedProgram
    (pp : PublicParam.{uScalar, uGroup})
    (certificate :
      Crypto.Assumption.DL.DDH.ParamEfficiencyCertificate pp) :
    Program.BoundedProgram
      (backend := pp.backend)
      (sampler := pp.scalarSampler)
      (keygenBudget pp certificate) (pp.Carrier × pp.Scalar) :=
  Program.BoundedProgram.bindSample
    (Program.BoundedProgram.sample
      (backend := pp.backend)
      (sampler := pp.scalarSampler))
    (fun secretKey =>
      Program.BoundedProgram.bindCarrier
        (Program.BoundedProgram.smul
          certificate.additiveBounds secretKey pp.generator)
        (fun publicKey => Program.BoundedProgram.pure (publicKey, secretKey)))

/-- Statically bounded ElGamal encryption. -/
def encryptBoundedProgram
    (pp : PublicParam.{uScalar, uGroup})
    (certificate :
      Crypto.Assumption.DL.DDH.ParamEfficiencyCertificate pp)
    (publicKey message : pp.Carrier) :
    Program.BoundedProgram
      (backend := pp.backend)
      (sampler := pp.scalarSampler)
      (encryptBudget pp certificate)
      (ULift.{uScalar} (pp.Carrier × pp.Carrier)) :=
  Program.BoundedProgram.bindSample
    (Program.BoundedProgram.sample
      (backend := pp.backend)
      (sampler := pp.scalarSampler))
    (fun nonce =>
      Program.BoundedProgram.bindCarrier
        (Program.BoundedProgram.smul
          certificate.additiveBounds nonce pp.generator)
        (fun firstComponent =>
          Program.BoundedProgram.bindCarrier
            (Program.BoundedProgram.smul
              certificate.additiveBounds nonce publicKey)
            (fun shared =>
              Program.BoundedProgram.bindCarrier
                (Program.BoundedProgram.add
                  certificate.additiveBounds message shared)
                (fun secondComponent =>
                  Program.BoundedProgram.pure
                    (ULift.up (firstComponent, secondComponent))))))

/-- Statically bounded ElGamal decryption. -/
def decryptBoundedProgram
    (pp : PublicParam.{uScalar, uGroup})
    (certificate :
      Crypto.Assumption.DL.DDH.ParamEfficiencyCertificate pp)
    (secretKey : pp.Scalar) (ciphertext : pp.Carrier × pp.Carrier) :
    Program.BoundedProgram
      (backend := pp.backend)
      (sampler := pp.scalarSampler)
      (decryptBudget pp certificate) (ULift.{uScalar} pp.Carrier) :=
  Program.BoundedProgram.bindCarrier
    (Program.BoundedProgram.smul
      certificate.additiveBounds secretKey ciphertext.1)
    (fun shared =>
      Program.BoundedProgram.sub
        certificate.additiveBounds ciphertext.2 shared)

/-- Costed ElGamal key generation. -/
noncomputable def keygenComputation
    (pp : PublicParam.{uScalar, uGroup}) :
    RandCosted (pp.Carrier × pp.Scalar) :=
  Program.runCosted (keygenProgram pp)

/-- Costed ElGamal encryption. -/
noncomputable def encryptComputation
    (pp : PublicParam.{uScalar, uGroup})
    (publicKey message : pp.Carrier) :
    RandCosted (pp.Carrier × pp.Carrier) :=
  RandCosted.map ULift.down
    (Program.runCosted (encryptProgram pp publicKey message))

/-- Deterministic costed ElGamal decryption. -/
def decryptComputation
    (pp : PublicParam.{uScalar, uGroup})
    (secretKey : pp.Scalar) (ciphertext : pp.Carrier × pp.Carrier) :
    Costed pp.Carrier :=
  Costed.bind
    (pp.backend.smul secretKey ciphertext.1)
    fun shared =>
      pp.backend.sub ciphertext.2 shared

/-- The deterministic decryption writer is exactly the program interpretation. -/
@[simp] theorem decryptProgram_runCosted
    (pp : PublicParam.{uScalar, uGroup})
    (secretKey : pp.Scalar) (ciphertext : pp.Carrier × pp.Carrier) :
    Program.runCosted (decryptProgram pp secretKey ciphertext) =
      RandCosted.map ULift.up
        (RandCosted.liftCosted
          (decryptComputation pp secretKey ciphertext)) := by
  simp [decryptProgram, Program.bindCarrier, Program.runCosted,
    RandCosted.bind, RandCosted.liftCosted, RandCosted.map,
    PMF.pure_map, Costed.bind, Costed.map, decryptComputation]

/-- ElGamal with execution-path costs derived from its algebraic program. -/
noncomputable def scheme (F : Family.{uScalar, uGroup}) :
    Scheme
      Crypto.SecPar
      PublicParam.{uScalar, uGroup}
      PublicKey
      SecretKey
      Message
      Ciphertext where
  setup := F.setup
  keygen := keygenComputation
  encrypt := encryptComputation
  decrypt := decryptComputation

/-- Erasing key-generation costs recovers semantic ElGamal key generation. -/
@[simp] theorem keygenComputation_valueDist
    (pp : PublicParam.{uScalar, uGroup}) :
    RandCosted.valueDist (keygenComputation pp) =
      PMF.bind
        (Crypto.Infrastructure.Computation.Distribution.uniformPMF pp.Scalar)
        (fun secretKey => PMF.pure (secretKey • pp.generator, secretKey)) := by
  simp only [keygenComputation, Program.valueDist_runCosted]
  simp [keygenProgram, Program.bindSample, Program.bindCarrier,
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
  simp only [encryptComputation, RandCosted.valueDist_map,
    Program.valueDist_runCosted]
  simp [encryptProgram, Program.bindSample, Program.bindCarrier,
    Function.comp_def, PMF.map_bind, PMF.pure_map]

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

/-- Cost erasure at the scheme boundary recovers ordinary ElGamal key generation. -/
@[simp] theorem scheme_keygenDist
    (F : Family.{uScalar, uGroup}) (pp : PublicParam.{uScalar, uGroup}) :
    (scheme F).keygenDist pp =
      PMF.bind
        (Crypto.Infrastructure.Computation.Distribution.uniformPMF pp.Scalar)
        (fun secretKey => PMF.pure (secretKey • pp.generator, secretKey)) := by
  simp [Scheme.keygenDist, scheme]

/-- Cost erasure at the scheme boundary recovers ordinary ElGamal encryption. -/
@[simp] theorem scheme_encryptDist
    (F : Family.{uScalar, uGroup}) (pp : PublicParam.{uScalar, uGroup})
    (publicKey message : pp.Carrier) :
    (scheme F).encryptDist pp publicKey message =
      PMF.bind
        (Crypto.Infrastructure.Computation.Distribution.uniformPMF pp.Scalar)
        (fun nonce =>
          PMF.pure (nonce • pp.generator, message + nonce • publicKey)) := by
  simp [Scheme.encryptDist, scheme]

/-- Cost erasure at the scheme boundary recovers ordinary ElGamal decryption. -/
@[simp] theorem scheme_decryptValue
    (F : Family.{uScalar, uGroup}) (pp : PublicParam.{uScalar, uGroup})
    (secretKey : pp.Scalar) (ciphertext : pp.Carrier × pp.Carrier) :
    (scheme F).decryptValue pp secretKey ciphertext =
      ciphertext.2 - secretKey • ciphertext.1 := by
  simp [Scheme.decryptValue, scheme]

/-- The key-generation syntax has its advertised sample-plus-smul budget. -/
theorem keygenProgram_costBound
    (pp : PublicParam.{uScalar, uGroup})
    (certificate :
      Crypto.Assumption.DL.DDH.ParamEfficiencyCertificate pp) :
    Program.CostBound
      (keygenProgram pp) (keygenBudget pp certificate) := by
  exact (keygenBoundedProgram pp certificate).sound

/-- The encryption syntax has its advertised sample-plus-two-smul-plus-add budget. -/
theorem encryptProgram_costBound
    (pp : PublicParam.{uScalar, uGroup})
    (certificate :
      Crypto.Assumption.DL.DDH.ParamEfficiencyCertificate pp)
    (publicKey message : pp.Carrier) :
    Program.CostBound
      (encryptProgram pp publicKey message)
      (encryptBudget pp certificate) := by
  exact
    (encryptBoundedProgram pp certificate publicKey message).sound

/-- The decryption syntax has its advertised smul-plus-sub budget. -/
theorem decryptProgram_costBound
    (pp : PublicParam.{uScalar, uGroup})
    (certificate :
      Crypto.Assumption.DL.DDH.ParamEfficiencyCertificate pp)
    (secretKey : pp.Scalar) (ciphertext : pp.Carrier × pp.Carrier) :
    Program.CostBound
      (decryptProgram pp secretKey ciphertext)
      (decryptBudget pp certificate) := by
  exact
    (decryptBoundedProgram pp certificate secretKey ciphertext).sound

/-- Every costed key-generation path satisfies the static budget. -/
theorem keygenComputation_costBound
    (pp : PublicParam.{uScalar, uGroup})
    (certificate :
      Crypto.Assumption.DL.DDH.ParamEfficiencyCertificate pp) :
    ∀ result, result ∈ (keygenComputation pp).support →
      result.cost ≤ keygenBudget pp certificate :=
  keygenProgram_costBound pp certificate

/-- Every costed encryption path satisfies the static budget. -/
theorem encryptComputation_costBound
    (pp : PublicParam.{uScalar, uGroup})
    (certificate :
      Crypto.Assumption.DL.DDH.ParamEfficiencyCertificate pp)
    (publicKey message : pp.Carrier) :
    ∀ result, result ∈ (encryptComputation pp publicKey message).support →
      result.cost ≤ encryptBudget pp certificate := by
  intro result hresult
  simp only [encryptComputation, RandCosted.map] at hresult
  rw [PMF.mem_support_map_iff] at hresult
  rcases hresult with ⟨liftedResult, hliftedResult, hresult⟩
  subst result
  exact
    encryptProgram_costBound
      pp certificate publicKey message liftedResult hliftedResult

/-- Deterministic costed decryption satisfies the static budget. -/
theorem decryptComputation_cost_le
    (pp : PublicParam.{uScalar, uGroup})
    (certificate :
      Crypto.Assumption.DL.DDH.ParamEfficiencyCertificate pp)
    (secretKey : pp.Scalar) (ciphertext : pp.Carrier × pp.Carrier) :
    (decryptComputation pp secretKey ciphertext).cost ≤
      decryptBudget pp certificate :=
  Nat.add_le_add
    (certificate.additiveBounds.smulCost_le secretKey ciphertext.1)
    (certificate.additiveBounds.subCost_le ciphertext.2
      (pp.backend.smul secretKey ciphertext.1).val)

/-- ElGamal encryption at a fixed public parameter as a sound timed machine. -/
noncomputable def encryptTimedMachine
    (pp : PublicParam.{uScalar, uGroup})
    (certificate :
      Crypto.Assumption.DL.DDH.ParamEfficiencyCertificate pp) :
    TimedMachine (pp.Carrier × pp.Carrier) (pp.Carrier × pp.Carrier) :=
  TimedMachine.ofMappedBoundedProgram
    pp.backend
    pp.scalarSampler
    (fun _sec => encryptBudget pp certificate)
    ULift.down
    (fun _sec input =>
      encryptBoundedProgram pp certificate input.1 input.2)

/-- The timed encryption machine has exactly the semantic ElGamal distribution. -/
@[simp] theorem encryptTimedMachine_runDist
    (F : Family.{uScalar, uGroup}) (pp : PublicParam.{uScalar, uGroup})
    (certificate :
      Crypto.Assumption.DL.DDH.ParamEfficiencyCertificate pp)
    (sec : Crypto.SecPar) (input : pp.Carrier × pp.Carrier) :
    (encryptTimedMachine pp certificate).runDist sec input =
      (scheme F).encryptDist pp input.1 input.2 :=
  rfl

end Crypto.Primitive.Encryption.AsymmetricEncryption.Instantiations.ElGamal

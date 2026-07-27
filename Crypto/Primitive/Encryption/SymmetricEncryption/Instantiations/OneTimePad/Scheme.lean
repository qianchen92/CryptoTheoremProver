import Crypto.Infrastructure.Complexity.ProgramMachine
import Crypto.Primitive.Encryption.SymmetricEncryption.Instantiations.OneTimePad.Construction
import Crypto.Primitive.Encryption.SymmetricEncryption.Syntax

namespace Crypto.Primitive.Encryption.SymmetricEncryption.Instantiations.OneTimePad

open Crypto.Infrastructure.Complexity
open Crypto.Infrastructure.Computation
open Crypto.Infrastructure.Computation.Algebra
open Crypto.Infrastructure.Computation.Cost
open Crypto.Primitive.Encryption.SymmetricEncryption

universe uGroup

/-- Static key-generation budget: one native uniform key sample. -/
def keygenBudget (pp : PublicParam.{uGroup}) : Cost :=
  pp.keySampler.sampleBudget

/-- Static encryption budget: one group addition. -/
def encryptBudget
    (pp : PublicParam.{uGroup})
    (certificate : ParamEfficiencyCertificate pp) : Cost :=
  certificate.additiveBounds.addBudget

/-- Static decryption budget: one negation followed by one addition. -/
def decryptBudget
    (pp : PublicParam.{uGroup})
    (certificate : ParamEfficiencyCertificate pp) : Cost :=
  certificate.additiveBounds.negBudget +
    certificate.additiveBounds.addBudget

/-- Uniform key-sampling syntax, independent of efficiency certificates. -/
def keygenProgram
    (pp : PublicParam.{uGroup}) :
    Program UnusedScalar pp.Carrier pp.Carrier
      pp.backend pp.keySampler
      (ULift.{uGroup} pp.Carrier) :=
  Program.sample

/-- Single-addition encryption syntax, independent of efficiency certificates. -/
def encryptProgram
    (pp : PublicParam.{uGroup})
    (key message : pp.Carrier) :
    Program UnusedScalar pp.Carrier pp.Carrier
      pp.backend pp.keySampler
      (ULift.{uGroup} pp.Carrier) :=
  Program.add key message

/--
Negation-then-addition decryption syntax, independent of efficiency
certificates.
-/
def decryptProgram
    (pp : PublicParam.{uGroup})
    (key ciphertext : pp.Carrier) :
    Program UnusedScalar pp.Carrier pp.Carrier
      pp.backend pp.keySampler
      (ULift.{uGroup} pp.Carrier) :=
  Program.bindCarrier
    (Program.neg
      (backend := pp.backend)
      (sampler := pp.keySampler)
      key)
    (fun negatedKey =>
      Program.add
        (backend := pp.backend)
        (sampler := pp.keySampler)
        negatedKey ciphertext)

/-- Statically bounded uniform key generation. -/
def keygenBoundedProgram
    (pp : PublicParam.{uGroup}) :
    Program.BoundedProgram
      (backend := pp.backend)
      (sampler := pp.keySampler)
      (keygenBudget pp)
      (ULift.{uGroup} pp.Carrier) :=
  Program.BoundedProgram.sample

/-- Statically bounded single-addition encryption. -/
def encryptBoundedProgram
    (pp : PublicParam.{uGroup})
    (certificate : ParamEfficiencyCertificate pp)
    (key message : pp.Carrier) :
    Program.BoundedProgram
      (backend := pp.backend)
      (sampler := pp.keySampler)
      (encryptBudget pp certificate)
      (ULift.{uGroup} pp.Carrier) :=
  Program.BoundedProgram.add
    certificate.additiveBounds key message

/-- Statically bounded negation-then-addition decryption. -/
def decryptBoundedProgram
    (pp : PublicParam.{uGroup})
    (certificate : ParamEfficiencyCertificate pp)
    (key ciphertext : pp.Carrier) :
    Program.BoundedProgram
      (backend := pp.backend)
      (sampler := pp.keySampler)
      (decryptBudget pp certificate)
      (ULift.{uGroup} pp.Carrier) :=
  Program.BoundedProgram.bindCarrier
    (Program.BoundedProgram.neg
      certificate.additiveBounds key)
    (fun negatedKey =>
      Program.BoundedProgram.add
        certificate.additiveBounds negatedKey ciphertext)

/-- Interpret key generation and remove the universe lift from its result. -/
noncomputable def keygenComputation
    (pp : PublicParam.{uGroup}) :
    RandCosted pp.Carrier :=
  Program.runCostedSample (keygenProgram pp)

/-- Interpret encryption and remove the universe lift from its result. -/
noncomputable def encryptComputation
    (pp : PublicParam.{uGroup})
    (key message : pp.Carrier) :
    RandCosted pp.Carrier :=
  Program.runCostedCarrier (encryptProgram pp key message)

/-- The deterministic costed OTP decryption result. -/
def decryptComputation
    (pp : PublicParam.{uGroup})
    (key ciphertext : pp.Carrier) :
    Costed pp.Carrier :=
  Costed.bind (pp.backend.neg key) fun negatedKey =>
    pp.backend.add negatedKey ciphertext

/-- The deterministic decryption writer is exactly the program interpretation. -/
@[simp] theorem decryptProgram_runCosted
    (pp : PublicParam.{uGroup})
    (key ciphertext : pp.Carrier) :
    Program.runCosted (decryptProgram pp key ciphertext) =
      RandCosted.map ULift.up
        (RandCosted.liftCosted
          (decryptComputation pp key ciphertext)) := by
  simp [decryptProgram, Program.bindCarrier, Program.runCosted,
    RandCosted.bind, RandCosted.liftCosted, RandCosted.map,
    PMF.pure_map, Costed.bind, Costed.map, decryptComputation]

/-- The native costed one-time-pad scheme. -/
noncomputable def scheme
    (F : Family.{uGroup}) :
    Scheme
      Crypto.SecPar
      PublicParam.{uGroup}
      (fun pp => pp.Carrier)
      (fun pp => pp.Carrier)
      (fun pp => pp.Carrier) where
  setup := F.setup
  keygen := keygenComputation
  encrypt := encryptComputation
  decrypt := decryptComputation

/-- Erasing key-generation costs recovers uniform key generation. -/
@[simp] theorem keygenComputation_valueDist
    (pp : PublicParam.{uGroup}) :
    RandCosted.valueDist (keygenComputation pp) =
      Crypto.Infrastructure.Computation.Distribution.uniformPMF pp.Carrier := by
  simp only [keygenComputation, keygenProgram,
    Program.runCostedSample, RandCosted.valueDist_map,
    Program.valueDist_runCosted, Program.valueDist_sample]
  rw [PMF.map_comp]
  simpa [Function.comp_def] using
    PMF.map_id
      (Crypto.Infrastructure.Computation.Distribution.uniformPMF pp.Carrier)

/-- Erasing encryption costs recovers ordinary OTP addition. -/
@[simp] theorem encryptComputation_valueDist
    (pp : PublicParam.{uGroup})
    (key message : pp.Carrier) :
    RandCosted.valueDist (encryptComputation pp key message) =
      PMF.pure (key + message) := by
  simp [encryptComputation, encryptProgram,
    Program.runCostedCarrier, Program.runCosted, PMF.pure_map]

/-- The deterministic costed decryption has the ordinary OTP value. -/
@[simp] theorem decryptComputation_value
    (pp : PublicParam.{uGroup})
    (key ciphertext : pp.Carrier) :
    (decryptComputation pp key ciphertext).val =
      -key + ciphertext := by
  simp [decryptComputation]

/-- Cost erasure at the scheme boundary recovers native OTP setup. -/
@[simp] theorem scheme_setupDist
    (F : Family.{uGroup}) (sec : Crypto.SecPar) :
    (scheme F).setupDist sec = F.setupDist sec := by
  simp [Scheme.setupDist, scheme, Family.setupDist]

/-- Cost erasure at the scheme boundary recovers uniform key generation. -/
@[simp] theorem scheme_keygenDist
    (F : Family.{uGroup}) (pp : PublicParam.{uGroup}) :
    (scheme F).keygenDist pp =
      Crypto.Infrastructure.Computation.Distribution.uniformPMF
        pp.Carrier := by
  simp [Scheme.keygenDist, scheme]

/-- Cost erasure at the scheme boundary recovers ordinary OTP encryption. -/
@[simp] theorem scheme_encryptDist
    (F : Family.{uGroup}) (pp : PublicParam.{uGroup})
    (key message : pp.Carrier) :
    (scheme F).encryptDist pp key message =
      PMF.pure (key + message) := by
  simp [Scheme.encryptDist, scheme]

/-- Cost erasure at the scheme boundary recovers ordinary OTP decryption. -/
@[simp] theorem scheme_decryptValue
    (F : Family.{uGroup}) (pp : PublicParam.{uGroup})
    (key ciphertext : pp.Carrier) :
    (scheme F).decryptValue pp key ciphertext =
      -key + ciphertext := by
  simp [Scheme.decryptValue, scheme]

/-- Key-generation syntax satisfies the supplied local efficiency certificate. -/
theorem keygenProgram_costBound
    (pp : PublicParam.{uGroup}) :
    Program.CostBound
      (keygenProgram pp) (keygenBudget pp) := by
  exact (keygenBoundedProgram pp).sound

/-- Encryption syntax satisfies the supplied local efficiency certificate. -/
theorem encryptProgram_costBound
    (pp : PublicParam.{uGroup})
    (certificate : ParamEfficiencyCertificate pp)
    (key message : pp.Carrier) :
    Program.CostBound
      (encryptProgram pp key message)
      (encryptBudget pp certificate) := by
  exact
    (encryptBoundedProgram pp certificate key message).sound

/-- Decryption syntax satisfies the supplied local efficiency certificate. -/
theorem decryptProgram_costBound
    (pp : PublicParam.{uGroup})
    (certificate : ParamEfficiencyCertificate pp)
    (key ciphertext : pp.Carrier) :
    Program.CostBound
      (decryptProgram pp key ciphertext)
      (decryptBudget pp certificate) := by
  exact
    (decryptBoundedProgram pp certificate key ciphertext).sound

/-- Every interpreted key-generation path satisfies its local budget. -/
theorem keygenComputation_costBound
    (pp : PublicParam.{uGroup}) :
    ∀ result, result ∈ (keygenComputation pp).support →
      result.cost ≤ keygenBudget pp := by
  intro result hresult
  simp only [keygenComputation,
    Program.runCostedSample, RandCosted.map] at hresult
  rw [PMF.mem_support_map_iff] at hresult
  rcases hresult with ⟨liftedResult, hliftedResult, rfl⟩
  exact
    keygenProgram_costBound
      pp liftedResult hliftedResult

/-- Every interpreted encryption path satisfies its local budget. -/
theorem encryptComputation_costBound
    (pp : PublicParam.{uGroup})
    (certificate : ParamEfficiencyCertificate pp)
    (key message : pp.Carrier) :
    ∀ result, result ∈ (encryptComputation pp key message).support →
      result.cost ≤ encryptBudget pp certificate := by
  intro result hresult
  simp only [encryptComputation,
    Program.runCostedCarrier, RandCosted.map] at hresult
  rw [PMF.mem_support_map_iff] at hresult
  rcases hresult with ⟨liftedResult, hliftedResult, rfl⟩
  exact
    encryptProgram_costBound
      pp certificate key message liftedResult hliftedResult

/-- Deterministic decryption satisfies its compositional local budget. -/
theorem decryptComputation_cost_le
    (pp : PublicParam.{uGroup})
    (certificate : ParamEfficiencyCertificate pp)
    (key ciphertext : pp.Carrier) :
    (decryptComputation pp key ciphertext).cost ≤
      decryptBudget pp certificate :=
  Nat.add_le_add
    (certificate.additiveBounds.negCost_le key)
    (certificate.additiveBounds.addCost_le
      (pp.backend.neg key).val ciphertext)

/-- Encryption at a fixed public parameter as a sound timed machine. -/
noncomputable def encryptTimedMachine
    (pp : PublicParam.{uGroup})
    (certificate : ParamEfficiencyCertificate pp) :
    TimedMachine (pp.Carrier × pp.Carrier) pp.Carrier :=
  TimedMachine.ofBoundedCarrierProgram
    pp.backend
    pp.keySampler
    (fun _sec => encryptBudget pp certificate)
    (fun _sec input =>
      encryptBoundedProgram
        pp certificate input.1 input.2)

/-- Timed encryption has exactly the scheme's cost-erased distribution. -/
@[simp] theorem encryptTimedMachine_runDist
    (F : Family.{uGroup}) (pp : PublicParam.{uGroup})
    (certificate : ParamEfficiencyCertificate pp)
    (sec : Crypto.SecPar)
    (input : pp.Carrier × pp.Carrier) :
    (encryptTimedMachine pp certificate).runDist sec input =
      (scheme F).encryptDist pp input.1 input.2 :=
  rfl

end Crypto.Primitive.Encryption.SymmetricEncryption.Instantiations.OneTimePad

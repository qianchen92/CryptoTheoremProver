import Crypto.Infrastructure.Complexity.ProgramMachine
import Crypto.Primitive.Encryption.SymmetricEncryption.Instantiations.OneTimePad.Construction
import Crypto.Primitive.Encryption.SymmetricEncryption.Syntax

namespace Crypto.Primitive.Encryption.SymmetricEncryption.Instantiations.OneTimePad

open Crypto.Infrastructure.Complexity
open Crypto.Infrastructure.Computation
open Crypto.Infrastructure.Computation.Algebra
open Crypto.Infrastructure.Computation.Cost
open Crypto.Primitive.Encryption.SymmetricEncryption
open scoped OneTimePadParameter

universe uGroup

/-- Static key-generation budget: one native uniform key sample. -/
def keygenBudget
    (pp : PublicParam.{uGroup})
    (certificate : ParamEfficiencyCertificate pp) : Cost :=
  certificate.keySamplerBounds.sampleBudget

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
    Program (costedAlgebra pp) Unit pp.Carrier where
  body := fun _input => .call (.sampleKey)

/-- Single-addition encryption syntax, independent of efficiency certificates. -/
def encryptProgram
    (pp : PublicParam.{uGroup}) :
    Program (costedAlgebra pp)
      (pp.Carrier × pp.Carrier) pp.Carrier where
  body := fun input => .call (.add input.1 input.2)

/--
Negation-then-addition decryption syntax, independent of efficiency
certificates.
-/
def decryptProgram
    (pp : PublicParam.{uGroup}) :
    Program (costedAlgebra pp)
      (pp.Carrier × pp.Carrier) pp.Carrier where
  body := fun input =>
    .bind (.call (.neg input.1)) fun negatedKey =>
      .call (.add negatedKey input.2)

/-- Statically bounded uniform key generation. -/
def keygenBoundedProgram
    (pp : PublicParam.{uGroup})
    (certificate : ParamEfficiencyCertificate pp) :
    Program.BoundedProgram
      (Output := pp.Carrier)
      (operationBounds pp certificate)
      (fun _input : Unit => keygenBudget pp certificate) where
  program := keygenProgram pp
  certificate := by
    intro input
    simpa [keygenProgram, keygenBudget, operationBounds] using
      (Program.Code.Bound.call
        (bounds := operationBounds pp certificate)
        (Operation.sampleKey (Carrier := pp.Carrier)))

/-- Statically bounded single-addition encryption. -/
def encryptBoundedProgram
    (pp : PublicParam.{uGroup})
    (certificate : ParamEfficiencyCertificate pp) :
    Program.BoundedProgram
      (Output := pp.Carrier)
      (operationBounds pp certificate)
      (fun _input : pp.Carrier × pp.Carrier =>
        encryptBudget pp certificate) where
  program := encryptProgram pp
  certificate := by
    intro input
    simpa [encryptProgram, encryptBudget, operationBounds] using
      (Program.Code.Bound.call
        (bounds := operationBounds pp certificate)
        (Operation.add input.1 input.2))

/-- Statically bounded negation-then-addition decryption. -/
def decryptBoundedProgram
    (pp : PublicParam.{uGroup})
    (certificate : ParamEfficiencyCertificate pp) :
    Program.BoundedProgram
      (Output := pp.Carrier)
      (operationBounds pp certificate)
      (fun _input : pp.Carrier × pp.Carrier =>
        decryptBudget pp certificate) where
  program := decryptProgram pp
  certificate := by
    intro input
    simpa [decryptProgram, decryptBudget, operationBounds] using
      (Program.Code.Bound.bind
        (bounds := operationBounds pp certificate)
        (Program.Code.Bound.call
          (bounds := operationBounds pp certificate)
          (Operation.neg input.1))
        (fun negatedKey =>
          Program.Code.Bound.call
            (bounds := operationBounds pp certificate)
            (Operation.add negatedKey input.2)))

/-- Interpret the input-parameterized key-generation program. -/
noncomputable def keygenComputation
    (pp : PublicParam.{uGroup}) :
    RandCosted pp.Carrier :=
  Program.runCosted (keygenProgram pp) ()

/-- Interpret the input-parameterized encryption program. -/
noncomputable def encryptComputation
    (pp : PublicParam.{uGroup})
    (key message : pp.Carrier) :
    RandCosted pp.Carrier :=
  Program.runCosted (encryptProgram pp) (key, message)

/--
The deterministic adapter required by the legacy symmetric-scheme boundary.

`decryptProgram_runCosted` below proves that this adapter is exactly the
interpretation of the single public decryption program.
-/
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
    Program.runCosted (decryptProgram pp) (key, ciphertext) =
      RandCosted.liftCosted
        (decryptComputation pp key ciphertext) := by
  simp only [decryptProgram, Program.runCosted, Program.Code.runCosted,
    costedAlgebra, RandCostedT.bind, RandCosted.liftCosted,
    PMF.pure_bind, PMF.pure_map, decryptComputation]
  rfl

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
  exact (algebraLaws pp).exec_spec Operation.sampleKey

/-- Erasing encryption costs recovers ordinary OTP addition. -/
@[simp] theorem encryptComputation_valueDist
    (pp : PublicParam.{uGroup})
    (key message : pp.Carrier) :
    RandCosted.valueDist (encryptComputation pp key message) =
      PMF.pure (key + message) := by
  exact (algebraLaws pp).exec_spec (Operation.add key message)

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
    (pp : PublicParam.{uGroup})
    (certificate : ParamEfficiencyCertificate pp) :
    Program.CostBound
      (keygenProgram pp)
      (fun _input => keygenBudget pp certificate) :=
  (keygenBoundedProgram pp certificate).costBound

/-- Encryption syntax satisfies the supplied local efficiency certificate. -/
theorem encryptProgram_costBound
    (pp : PublicParam.{uGroup})
    (certificate : ParamEfficiencyCertificate pp) :
    Program.CostBound
      (encryptProgram pp)
      (fun _input => encryptBudget pp certificate) :=
  (encryptBoundedProgram pp certificate).costBound

/-- Decryption syntax satisfies the supplied local efficiency certificate. -/
theorem decryptProgram_costBound
    (pp : PublicParam.{uGroup})
    (certificate : ParamEfficiencyCertificate pp) :
    Program.CostBound
      (decryptProgram pp)
      (fun _input => decryptBudget pp certificate) :=
  (decryptBoundedProgram pp certificate).costBound

/-- Every interpreted key-generation path satisfies its local budget. -/
theorem keygenComputation_costBound
    (pp : PublicParam.{uGroup})
    (certificate : ParamEfficiencyCertificate pp) :
    ∀ result, result ∈ (keygenComputation pp).support →
      result.cost ≤ keygenBudget pp certificate := by
  exact
    (keygenBoundedProgram pp certificate).cost_le_budget_of_mem_support ()

/-- Every interpreted encryption path satisfies its local budget. -/
theorem encryptComputation_costBound
    (pp : PublicParam.{uGroup})
    (certificate : ParamEfficiencyCertificate pp)
    (key message : pp.Carrier) :
    ∀ result, result ∈ (encryptComputation pp key message).support →
      result.cost ≤ encryptBudget pp certificate := by
  exact
    (encryptBoundedProgram pp certificate).cost_le_budget_of_mem_support
      (key, message)

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
  TimedMachine.ofNatBoundedProgram
    (fun _sec => costedAlgebra pp)
    (fun _sec => operationBounds pp certificate)
    (fun _sec => encryptBudget pp certificate)
    (fun _sec => encryptBoundedProgram pp certificate)

/-- Timed encryption has exactly the scheme's cost-erased distribution. -/
@[simp] theorem encryptTimedMachine_runDist
    (F : Family.{uGroup}) (pp : PublicParam.{uGroup})
    (certificate : ParamEfficiencyCertificate pp)
    (sec : Crypto.SecPar)
    (input : pp.Carrier × pp.Carrier) :
    (encryptTimedMachine pp certificate).runDist sec input =
      (scheme F).encryptDist pp input.1 input.2 :=
  by
    simp [ProbabilisticMachine.runDist, RandomizedComputation.valueDist,
      encryptTimedMachine, TimedMachine.ofNatBoundedProgram,
      TimedMachine.ofBoundedProgram, Scheme.encryptDist, scheme,
      encryptComputation, encryptBoundedProgram]

end Crypto.Primitive.Encryption.SymmetricEncryption.Instantiations.OneTimePad

import Crypto.Infrastructure.Complexity.ProgramMachine
import Crypto.Infrastructure.Probability.Uniform
import Crypto.Primitive.Encryption.SymmetricEncryption.Instantiations.OneTimePad.Construction
import Crypto.Primitive.Encryption.SymmetricEncryption.Syntax

namespace Crypto.Primitive.Encryption.SymmetricEncryption.Instantiations.OneTimePad

open Crypto.Infrastructure.Complexity
open Crypto.Infrastructure.Computation
open Crypto.Infrastructure.Computation.Algebra
open Crypto.Infrastructure.Computation.Cost
open Crypto.Primitive.Encryption.SymmetricEncryption
open scoped OneTimePadParameter

universe uCost uGroup

variable {M : CostModel.{uCost}}

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

/-- Uniform key generation over the parameter's sole exact algebra. -/
def keygenProgram (pp : PublicParam M) :
    Program pp.algebra Unit pp.Carrier where
  body _input := .call .sampleKey

/-- One-addition OTP encryption over the parameter's sole exact algebra. -/
def encryptProgram (pp : PublicParam M) :
    Program pp.algebra (pp.Carrier × pp.Carrier) pp.Carrier where
  body input := .call (.add input.1 input.2)

/-- Negation-then-addition OTP decryption. -/
def decryptProgram (pp : PublicParam M) :
    Program pp.algebra (pp.Carrier × pp.Carrier) pp.Carrier where
  body input :=
    .bind (.call (.neg input.1)) fun negatedKey =>
      .call (.add negatedKey input.2)

/-- Statically bounded key generation, indexing the same program body. -/
def keygenBoundedProgram
    (pp : PublicParam M) (certificate : ParamEfficiencyCertificate pp) :
    Program.BoundedProgram (Output := pp.Carrier) certificate.bounds
      (fun _input : Unit => keygenBudget pp certificate) where
  program := keygenProgram pp
  certificate := by
    intro input
    exact Program.Code.Bound.weaken
      (Program.Code.Bound.call
        (bounds := certificate.bounds)
        (Operation.sampleKey (math := pp.toAdditiveGroupParam)))
      certificate.sampleKeyBudget_sound

/-- Statically bounded encryption, indexing the same program body. -/
def encryptBoundedProgram
    (pp : PublicParam M) (certificate : ParamEfficiencyCertificate pp) :
    Program.BoundedProgram (Output := pp.Carrier) certificate.bounds
      (fun _input : pp.Carrier × pp.Carrier => encryptBudget pp certificate) where
  program := encryptProgram pp
  certificate := by
    intro input
    exact Program.Code.Bound.weaken
      (Program.Code.Bound.call
        (bounds := certificate.bounds) (Operation.add input.1 input.2))
      (certificate.addBudget_sound input.1 input.2)

/-- Statically bounded decryption, indexing the same program body. -/
def decryptBoundedProgram
    (pp : PublicParam M) (certificate : ParamEfficiencyCertificate pp) :
    Program.BoundedProgram (Output := pp.Carrier) certificate.bounds
      (fun _input : pp.Carrier × pp.Carrier => decryptBudget pp certificate) where
  program := decryptProgram pp
  certificate := by
    intro input
    exact Program.Code.Bound.bind
      (Program.Code.Bound.weaken
        (Program.Code.Bound.call
          (bounds := certificate.bounds) (Operation.neg input.1))
        (certificate.negBudget_sound input.1))
      (fun negatedKey =>
        Program.Code.Bound.weaken
          (Program.Code.Bound.call
            (bounds := certificate.bounds) (Operation.add negatedKey input.2))
          (certificate.addBudget_sound negatedKey input.2))

/-- The OTP scheme executes setup and its three parameter operations only through Programs. -/
noncomputable def scheme (F : Family M) :
    Scheme M Crypto.SecPar (PublicParam M)
      (fun pp => pp.Carrier) (fun pp => pp.Carrier) (fun pp => pp.Carrier) where
  setup := fun sec => Program.runCosted (setupProgram F) sec
  keygen := fun pp => Program.runCosted (keygenProgram pp) ()
  encrypt := fun pp key message =>
    Program.runCosted (encryptProgram pp) (key, message)
  decrypt := fun pp key ciphertext =>
    Program.runCosted (decryptProgram pp) (key, ciphertext)

/-- Cost erasure of key generation is uniform sampling. -/
@[simp] theorem keygenProgram_valueDist (pp : PublicParam M) :
    Program.valueDist (keygenProgram pp) () =
      Crypto.Infrastructure.Probability.uniformPMF pp.Carrier := by
  exact (algebraLaws pp).exec_spec Operation.sampleKey

/-- Cost erasure of encryption is mathematical addition. -/
@[simp] theorem encryptProgram_valueDist
    (pp : PublicParam M) (key message : pp.Carrier) :
    Program.valueDist (encryptProgram pp) (key, message) =
      PMF.pure (key + message) := by
  exact (algebraLaws pp).exec_spec (Operation.add key message)

/-- Cost erasure of decryption is mathematical negation followed by addition. -/
@[simp] theorem decryptProgram_valueDist
    (pp : PublicParam M) (key ciphertext : pp.Carrier) :
    Program.valueDist (decryptProgram pp) (key, ciphertext) =
      PMF.pure (-key + ciphertext) := by
  simp only [Program.valueDist, Program.runCosted, decryptProgram,
    Program.Code.runCosted, RandCosted.valueDist_bind]
  rw [(algebraLaws pp).exec_spec (Operation.neg key)]
  change
    PMF.bind (PMF.pure (-key))
        (fun value => RandCosted.valueDist
          (pp.algebra.exec (Operation.add value ciphertext))) =
      PMF.pure (-key + ciphertext)
  rw [PMF.pure_bind]
  exact (algebraLaws pp).exec_spec (Operation.add (-key) ciphertext)

@[simp] theorem scheme_setupDist (F : Family M) (sec : Crypto.SecPar) :
    (scheme F).setupDist sec = F.setupDist sec := by
  rfl

@[simp] theorem scheme_keygenDist (F : Family M) (pp : PublicParam M) :
    (scheme F).keygenDist pp =
      Crypto.Infrastructure.Probability.uniformPMF pp.Carrier :=
  keygenProgram_valueDist pp

@[simp] theorem scheme_encryptDist
    (F : Family M) (pp : PublicParam M) (key message : pp.Carrier) :
    (scheme F).encryptDist pp key message = PMF.pure (key + message) :=
  encryptProgram_valueDist pp key message

@[simp] theorem scheme_decryptDist
    (F : Family M) (pp : PublicParam M) (key ciphertext : pp.Carrier) :
    (scheme F).decryptDist pp key ciphertext = PMF.pure (-key + ciphertext) :=
  decryptProgram_valueDist pp key ciphertext

theorem keygenProgram_costBound
    (pp : PublicParam M) (certificate : ParamEfficiencyCertificate pp) :
    Program.CostBound (keygenProgram pp)
      (fun _input => keygenBudget pp certificate) :=
  (keygenBoundedProgram pp certificate).costBound

theorem encryptProgram_costBound
    (pp : PublicParam M) (certificate : ParamEfficiencyCertificate pp) :
    Program.CostBound (encryptProgram pp)
      (fun _input => encryptBudget pp certificate) :=
  (encryptBoundedProgram pp certificate).costBound

theorem decryptProgram_costBound
    (pp : PublicParam M) (certificate : ParamEfficiencyCertificate pp) :
    Program.CostBound (decryptProgram pp)
      (fun _input => decryptBudget pp certificate) :=
  (decryptBoundedProgram pp certificate).costBound

/-- Fixed-parameter encryption with an explicit natural-number runtime observation. -/
noncomputable def encryptTimedMachine
    (measure : NatMeasure M)
    (pp : PublicParam M) (certificate : ParamEfficiencyCertificate pp) :
    TimedMachine M measure
      (fun _sec => pp.Carrier × pp.Carrier)
      (fun _sec _input => pp.Carrier) :=
  TimedMachine.ofBoundedProgram measure
    (fun _sec => pp.algebra)
    (fun _sec => certificate.bounds)
    (fun _sec _input => encryptBudget pp certificate)
    (fun _sec => measure (encryptBudget pp certificate))
    (fun _sec => encryptBoundedProgram pp certificate)
    (by
      intro sec input
      exact Nat.le_refl _)

@[simp] theorem encryptTimedMachine_runDist
    (measure : NatMeasure M)
    (F : Family M) (pp : PublicParam M)
    (certificate : ParamEfficiencyCertificate pp)
    (sec : Crypto.SecPar) (input : pp.Carrier × pp.Carrier) :
    (encryptTimedMachine measure pp certificate).runDist sec input =
      (scheme F).encryptDist pp input.1 input.2 := by
  rfl

end Crypto.Primitive.Encryption.SymmetricEncryption.Instantiations.OneTimePad

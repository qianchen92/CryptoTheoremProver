import Crypto.Infrastructure.Probability.Uniform
import CryptoConstruction.Primitive.Encryption.SymmetricEncryption.OneTimePad.Scheme

namespace CryptoConstruction.Primitive.Encryption.SymmetricEncryption.OneTimePad

open Crypto.Infrastructure.Computation
open Crypto.Infrastructure.Computation.Algebra
open Crypto.Infrastructure.Computation.Cost
open Crypto.Primitive.Encryption.SymmetricEncryption
open scoped OneTimePadParameter

universe uCost uGroup

variable {M : CostModel.{uCost}}

/-- The family-level setup program delegates to the unique exact setup primitive. -/
@[simp] theorem setupProgram_runCosted
    (F : Family.{uCost, uGroup} M) (sec : Crypto.SecPar) :
    Program.runCosted (setupProgram F) sec = F.setup sec :=
  rfl

/-- Cost erasure of key generation is uniform sampling. -/
@[simp] theorem keygenProgram_valueDist (pp : PublicParam M) :
    FirstOrder.Program.valueDist
        (Language.algebra pp) (keygenProgram pp) (ULift.up ()) =
      Crypto.Infrastructure.Probability.uniformPMF pp.Carrier := by
  simp [FirstOrder.Program.valueDist, FirstOrder.Program.runCosted,
    keygenProgram, FirstOrder.Code.runCosted, Language.algebra,
    (algebraLaws pp).exec_spec, algebraLaws,
    FirstOrder.Expr.eval, FirstOrder.Env.get]

/-- Cost erasure of encryption is mathematical addition. -/
@[simp] theorem encryptProgram_valueDist
    (pp : PublicParam M) (key message : pp.Carrier) :
    FirstOrder.Program.valueDist
        (Language.algebra pp) (encryptProgram pp) (key, message) =
      PMF.pure (key + message) := by
  simp [FirstOrder.Program.valueDist, FirstOrder.Program.runCosted,
    encryptProgram, FirstOrder.Code.runCosted, Language.algebra,
    (algebraLaws pp).exec_spec, algebraLaws,
    FirstOrder.Expr.eval, FirstOrder.Env.get]

/-- Cost erasure of decryption is mathematical negation followed by addition. -/
@[simp] theorem decryptProgram_valueDist
    (pp : PublicParam M) (key ciphertext : pp.Carrier) :
    FirstOrder.Program.valueDist
        (Language.algebra pp) (decryptProgram pp) (key, ciphertext) =
      PMF.pure (-key + ciphertext) := by
  simp only [FirstOrder.Program.valueDist, FirstOrder.Program.runCosted,
    Language.algebra, decryptProgram, FirstOrder.Code.runCosted,
    FirstOrder.Expr.eval, FirstOrder.Env.get, RandCosted.bind_pure,
    RandCosted.valueDist_bind, (algebraLaws pp).exec_spec, algebraLaws]
  change PMF.bind (PMF.pure (-key))
    (fun value => PMF.pure (value + ciphertext)) = _
  rw [PMF.pure_bind]

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

end CryptoConstruction.Primitive.Encryption.SymmetricEncryption.OneTimePad

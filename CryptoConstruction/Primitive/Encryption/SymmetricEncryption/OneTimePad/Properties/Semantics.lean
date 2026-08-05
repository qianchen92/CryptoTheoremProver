import Crypto.Infrastructure.Probability.Uniform
import CryptoConstruction.Primitive.Encryption.SymmetricEncryption.OneTimePad.Scheme

namespace CryptoConstruction.Primitive.Encryption.SymmetricEncryption.OneTimePad

open Crypto.Infrastructure.Computation
open Crypto.Infrastructure.Computation.Cost
open Crypto.Primitive.Encryption.SymmetricEncryption
open scoped OneTimePadParameter

universe uCost uGroup

variable
    {M : CostModel.{uCost}}
    (F : Family.{uCost, uGroup} M)
    (pp : PublicParam.{uCost, uGroup} M)

/-- The family-level setup program delegates to the unique exact setup primitive. -/
@[simp] theorem setupProgram_runCosted
    (sec : Crypto.SecPar) :
    Program.runCosted (setupProgram F) sec = F.setup sec :=
  rfl

/-- Cost erasure of key generation is uniform sampling. -/
@[simp] theorem keygenProgram_valueDist :
    CryptoFirstOrder.Program.valueDist
        (Language.algebra pp) (keygenProgram pp) (ULift.up ()) =
      Crypto.Infrastructure.Probability.uniformPMF pp.Carrier := by
  simp only [CryptoFirstOrder.Program.valueDist, CryptoFirstOrder.Program.runCosted,
    keygenProgram, CryptoFirstOrder.Builder.SmartCode.unifSamp,
    CryptoFirstOrder.SmartOperation.unifSamp, CryptoFirstOrder.Signature.inject,
    CryptoFirstOrder.Code.runCosted, Language.algebra, Language.handler,
    CryptoFirstOrder.Algebra.AdditiveGroup.algebra,
    CryptoFirstOrder.Expr.eval, CryptoFirstOrder.Env.get]
  rw [RandCosted.bind_pure]
  exact pp.laws.sampleKey

/-- Cost erasure of encryption is mathematical addition. -/
@[simp] theorem encryptProgram_valueDist
    (key message : pp.Carrier) :
    CryptoFirstOrder.Program.valueDist
        (Language.algebra pp) (encryptProgram pp) (key, message) =
      PMF.pure (key + message) := by
  simp only [CryptoFirstOrder.Program.valueDist, CryptoFirstOrder.Program.runCosted,
    encryptProgram, CryptoFirstOrder.Builder.SmartCode.add,
    CryptoFirstOrder.SmartOperation.add, CryptoFirstOrder.Signature.inject,
    CryptoFirstOrder.Code.runCosted, Language.algebra, Language.handler,
    CryptoFirstOrder.Algebra.AdditiveGroup.algebra,
    CryptoFirstOrder.Expr.eval, CryptoFirstOrder.Env.get]
  rw [RandCosted.bind_pure]
  exact pp.laws.add key message

/-- Cost erasure of decryption is mathematical negation followed by addition. -/
@[simp] theorem decryptProgram_valueDist
    (key ciphertext : pp.Carrier) :
    CryptoFirstOrder.Program.valueDist
        (Language.algebra pp) (decryptProgram pp) (key, ciphertext) =
      PMF.pure (-key + ciphertext) := by
  simp only [CryptoFirstOrder.Program.valueDist, CryptoFirstOrder.Program.runCosted,
    Language.algebra, Language.handler,
    CryptoFirstOrder.Algebra.AdditiveGroup.algebra,
    decryptProgram, CryptoFirstOrder.Builder.SmartCode.neg,
    CryptoFirstOrder.Builder.SmartCode.add, CryptoFirstOrder.Code.runCosted,
    CryptoFirstOrder.SmartOperation.neg, CryptoFirstOrder.SmartOperation.add,
    CryptoFirstOrder.Signature.inject,
    CryptoFirstOrder.Expr.eval, CryptoFirstOrder.Env.get, RandCosted.bind_pure,
    RandCosted.valueDist_bind]
  calc
    _ = PMF.bind (PMF.pure (-key))
        (fun value =>
          RandCosted.valueDist
            (pp.algebra.exec (Operation.add value ciphertext))) := by
      exact congrArg
        (fun dist => PMF.bind dist
          (fun value =>
            RandCosted.valueDist
              (pp.algebra.exec (Operation.add value ciphertext))))
        (pp.laws.neg key)
    _ = RandCosted.valueDist
          (pp.algebra.exec (Operation.add (-key) ciphertext)) := by
      rw [PMF.pure_bind]
    _ = PMF.pure (-key + ciphertext) := pp.laws.add (-key) ciphertext

@[simp] theorem scheme_setupDist (sec : Crypto.SecPar) :
    (scheme F).setupDist sec = F.setupDist sec := by
  rfl

@[simp] theorem scheme_keygenDist :
    (scheme F).keygenDist pp =
      Crypto.Infrastructure.Probability.uniformPMF pp.Carrier :=
  keygenProgram_valueDist pp

@[simp] theorem scheme_encryptDist
    (key message : pp.Carrier) :
    (scheme F).encryptDist pp key message = PMF.pure (key + message) :=
  encryptProgram_valueDist pp key message

@[simp] theorem scheme_decryptDist
    (key ciphertext : pp.Carrier) :
    (scheme F).decryptDist pp key ciphertext = PMF.pure (-key + ciphertext) :=
  decryptProgram_valueDist pp key ciphertext

end CryptoConstruction.Primitive.Encryption.SymmetricEncryption.OneTimePad

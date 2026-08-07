import CryptoLib.Core.Infrastructure.Probability.Uniform
import CryptoLib.Instantiation.Primitive.Encryption.SymmetricEncryption.OneTimePad.Scheme

namespace CryptoLib.Instantiation.Primitive.Encryption.SymmetricEncryption.OneTimePad

open CryptoLib.Core.Infrastructure.Computation
open CryptoLib.Core.Infrastructure.Computation.Cost
open CryptoLib.Core.Primitive.Encryption.SymmetricEncryption
open scoped OneTimePadParameter

universe uCost uGroup

variable
    {M : CostModel.{uCost}}
    (F : Family.{uCost, uGroup} M)
    (pp : PublicParam.{uCost, uGroup} M)

/-- The family-level setup program delegates to the unique exact setup primitive. -/
@[simp] theorem setupProgram_runCosted
    (sec : CryptoLib.Core.SecPar) :
    Program.runCosted (setupProgram F) sec = F.setup sec :=
  rfl

/-- Cost erasure of key generation is uniform sampling. -/
@[simp] theorem keygenProgram_valueDist :
    CryptoLib.Program.Procedure.valueDist
        (Language.algebra pp) (keygenProgram pp) (ULift.up ()) =
      CryptoLib.Core.Infrastructure.Probability.uniformPMF pp.Carrier := by
  simp only [CryptoLib.Program.Procedure.valueDist, CryptoLib.Program.Procedure.runCosted,
    keygenProgram, CryptoLib.Program.Builder.SmartCode.unifSamp,
    CryptoLib.Program.SmartOperation.unifSamp, CryptoLib.Program.Signature.inject,
    CryptoLib.Program.Code.runCosted, Language.algebra, Language.handler,
    CryptoLib.Program.Algebra.AdditiveGroup.algebra,
    CryptoLib.Program.Expr.eval, CryptoLib.Program.Env.get]
  rw [RandCosted.bind_pure]
  exact pp.laws.sampleKey

/-- Cost erasure of encryption is mathematical addition. -/
@[simp] theorem encryptProgram_valueDist
    (key message : pp.Carrier) :
    CryptoLib.Program.Procedure.valueDist
        (Language.algebra pp) (encryptProgram pp) (key, message) =
      PMF.pure (key + message) := by
  simp only [CryptoLib.Program.Procedure.valueDist, CryptoLib.Program.Procedure.runCosted,
    encryptProgram, CryptoLib.Program.Builder.SmartCode.add,
    CryptoLib.Program.SmartOperation.add, CryptoLib.Program.Signature.inject,
    CryptoLib.Program.Code.runCosted, Language.algebra, Language.handler,
    CryptoLib.Program.Algebra.AdditiveGroup.algebra,
    CryptoLib.Program.Expr.eval, CryptoLib.Program.Env.get]
  rw [RandCosted.bind_pure]
  exact pp.laws.add key message

/-- Cost erasure of decryption is mathematical negation followed by addition. -/
@[simp] theorem decryptProgram_valueDist
    (key ciphertext : pp.Carrier) :
    CryptoLib.Program.Procedure.valueDist
        (Language.algebra pp) (decryptProgram pp) (key, ciphertext) =
      PMF.pure (-key + ciphertext) := by
  simp only [CryptoLib.Program.Procedure.valueDist, CryptoLib.Program.Procedure.runCosted,
    Language.algebra, Language.handler,
    CryptoLib.Program.Algebra.AdditiveGroup.algebra,
    decryptProgram, CryptoLib.Program.Builder.SmartCode.neg,
    CryptoLib.Program.Builder.SmartCode.add, CryptoLib.Program.Code.runCosted,
    CryptoLib.Program.SmartOperation.neg, CryptoLib.Program.SmartOperation.add,
    CryptoLib.Program.Signature.inject,
    CryptoLib.Program.Expr.eval, CryptoLib.Program.Env.get, RandCosted.bind_pure,
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

@[simp] theorem scheme_setupDist (sec : CryptoLib.Core.SecPar) :
    (scheme F).setupDist sec = F.setupDist sec := by
  rfl

@[simp] theorem scheme_keygenDist :
    (scheme F).keygenDist pp =
      CryptoLib.Core.Infrastructure.Probability.uniformPMF pp.Carrier :=
  keygenProgram_valueDist pp

@[simp] theorem scheme_encryptDist
    (key message : pp.Carrier) :
    (scheme F).encryptDist pp key message = PMF.pure (key + message) :=
  encryptProgram_valueDist pp key message

@[simp] theorem scheme_decryptDist
    (key ciphertext : pp.Carrier) :
    (scheme F).decryptDist pp key ciphertext = PMF.pure (-key + ciphertext) :=
  decryptProgram_valueDist pp key ciphertext

end CryptoLib.Instantiation.Primitive.Encryption.SymmetricEncryption.OneTimePad

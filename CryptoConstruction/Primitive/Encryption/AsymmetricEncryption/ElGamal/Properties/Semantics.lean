import Crypto.Infrastructure.Probability.Uniform
import CryptoConstruction.Primitive.Encryption.AsymmetricEncryption.ElGamal.Scheme

namespace CryptoConstruction.Primitive.Encryption.AsymmetricEncryption.ElGamal

open Crypto.Infrastructure.Computation
open Crypto.Infrastructure.Computation.Cost
open Crypto.Primitive.Encryption.AsymmetricEncryption
open scoped DDHParameter

universe uCost uScalar uGroup

variable
    {M : CostModel.{uCost}}
    (F : Family.{uCost, uScalar, uGroup} M)
    (pp : PublicParam.{uCost, uScalar, uGroup} M)

@[simp] theorem setupProgram_runCosted
    (sec : Crypto.SecPar) :
    Program.runCosted (setupProgram F) sec = F.setup sec :=
  rfl

@[simp] theorem scheme_setup_eq_family_setup
    (sec : Crypto.SecPar) :
    (scheme F).setup sec = F.setup sec :=
  rfl

/-- Erasing key-generation costs recovers ordinary ElGamal key generation. -/
@[simp] theorem keygenProgram_valueDist
    : PMF.map (Language.keyPairDown pp)
        (CryptoFirstOrder.Program.valueDist
          (Language.algebra pp) (keygenProgram pp) (ULift.up ())) =
      PMF.bind
        (Crypto.Infrastructure.Probability.uniformPMF pp.Scalar)
        (fun sk => PMF.pure (sk • pp.generator, sk)) := by
  change PMF.map (Language.keyPairDown pp)
    (CryptoFirstOrder.Code.valueDist (Language.algebra pp) (keygenProgram pp).body
      (.cons (ULift.up ()) .nil)) = _
  simp only [keygenProgram, CryptoFirstOrder.Builder.SmartCode.unifSamp,
    CryptoFirstOrder.Builder.SmartCode.smul, CryptoFirstOrder.SmartOperation.unifSamp,
    CryptoFirstOrder.SmartOperation.smul, CryptoFirstOrder.Signature.inject,
    CryptoFirstOrder.Signature.Embedding.inject,
    CryptoFirstOrder.Code.valueDist_call,
    CryptoFirstOrder.Expr.eval,
    CryptoFirstOrder.Assumption.DL.DDH.valueDist_exec_sampleScalar,
    CryptoFirstOrder.Env.get,
    CryptoFirstOrder.Assumption.DL.DDH.valueDist_exec_smul,
    CryptoFirstOrder.Code.valueDist_ret]
  change
    PMF.map (Language.keyPairDown pp)
      (PMF.bind
        (PMF.map ULift.up
          (Crypto.Infrastructure.Probability.uniformPMF pp.Scalar))
        (fun sk =>
          PMF.bind (PMF.pure (ULift.up (sk.down • pp.generator)))
            (fun pk => PMF.pure (pk, sk)))) = _
  rw [PMF.map_bind, PMF.bind_map]
  simp only [PMF.pure_bind, PMF.pure_map]
  rfl

/-- Erasing encryption costs recovers ordinary ElGamal encryption. -/
@[simp] theorem encryptProgram_valueDist
    (pk message : pp.Carrier) :
    PMF.map (Language.carrierPairDown pp)
        (CryptoFirstOrder.Program.valueDist
          (Language.algebra pp) (encryptProgram pp)
          (Language.liftCarrier pp pk,
            Language.liftCarrier pp message)) =
      PMF.bind
        (Crypto.Infrastructure.Probability.uniformPMF pp.Scalar)
        (fun r =>
          PMF.pure (r • pp.generator, message + r • pk)) := by
  change PMF.map (Language.carrierPairDown pp)
    (CryptoFirstOrder.Code.valueDist (Language.algebra pp) (encryptProgram pp).body
      (.cons
        (Language.liftCarrier pp pk,
          Language.liftCarrier pp message) .nil)) = _
  simp only [encryptProgram, CryptoFirstOrder.Builder.SmartCode.unifSamp,
    CryptoFirstOrder.Builder.SmartCode.smul, CryptoFirstOrder.Builder.SmartCode.add,
    CryptoFirstOrder.SmartOperation.unifSamp, CryptoFirstOrder.SmartOperation.smul,
    CryptoFirstOrder.SmartOperation.add, CryptoFirstOrder.Signature.inject,
    CryptoFirstOrder.Signature.Embedding.inject,
    CryptoFirstOrder.Code.valueDist_call,
    CryptoFirstOrder.Expr.eval,
    CryptoFirstOrder.Assumption.DL.DDH.valueDist_exec_sampleScalar,
    CryptoFirstOrder.Env.get,
    CryptoFirstOrder.Assumption.DL.DDH.valueDist_exec_smul,
    CryptoFirstOrder.Assumption.DL.DDH.valueDist_exec_add,
    CryptoFirstOrder.Code.valueDist_ret]
  change
    PMF.map (Language.carrierPairDown pp)
      (PMF.bind
        (PMF.map ULift.up
          (Crypto.Infrastructure.Probability.uniformPMF pp.Scalar))
        (fun r =>
          PMF.bind (PMF.pure (ULift.up (r.down • pp.generator)))
            (fun firstComponent =>
              PMF.bind (PMF.pure (ULift.up (r.down • pk)))
                (fun shared =>
                  PMF.bind (PMF.pure (ULift.up (message + shared.down)))
                    (fun secondComponent =>
                      PMF.pure (firstComponent, secondComponent)))))) = _
  rw [PMF.map_bind, PMF.bind_map]
  simp only [PMF.pure_bind, PMF.pure_map]
  rfl

/-- Erasing decryption costs recovers ordinary ElGamal decryption. -/
@[simp] theorem decryptProgram_valueDist
    (sk : pp.Scalar) (ciphertext : pp.Carrier × pp.Carrier) :
    PMF.map ULift.down
        (CryptoFirstOrder.Program.valueDist
          (Language.algebra pp) (decryptProgram pp)
          (Language.liftScalar pp sk,
            (Language.liftCarrier pp ciphertext.1,
              Language.liftCarrier pp ciphertext.2))) =
      PMF.pure (ciphertext.2 - sk • ciphertext.1) := by
  change PMF.map ULift.down
    (CryptoFirstOrder.Code.valueDist (Language.algebra pp) (decryptProgram pp).body
      (.cons
        (Language.liftScalar pp sk,
          (Language.liftCarrier pp ciphertext.1,
            Language.liftCarrier pp ciphertext.2)) .nil)) = _
  simp only [decryptProgram, CryptoFirstOrder.Builder.SmartCode.smul,
    CryptoFirstOrder.Builder.SmartCode.sub, CryptoFirstOrder.SmartOperation.smul,
    CryptoFirstOrder.SmartOperation.sub, CryptoFirstOrder.Signature.inject,
    CryptoFirstOrder.Signature.Embedding.inject,
    CryptoFirstOrder.Code.valueDist_call,
    CryptoFirstOrder.Expr.eval, CryptoFirstOrder.Env.get,
    CryptoFirstOrder.Assumption.DL.DDH.valueDist_exec_smul,
    CryptoFirstOrder.Assumption.DL.DDH.valueDist_exec_sub,
    CryptoFirstOrder.Code.valueDist_ret, PMF.bind_pure]
  change
    PMF.map ULift.down
      (PMF.bind (PMF.pure (ULift.up (sk • ciphertext.1)))
        (fun shared => PMF.pure (ULift.up (ciphertext.2 - shared.down)))) = _
  rw [PMF.map_bind, PMF.pure_bind, PMF.pure_map]

@[simp] theorem scheme_setupDist
    (sec : Crypto.SecPar) :
    (scheme F).setupDist sec = F.setupDist sec :=
  rfl

@[simp] theorem scheme_keygenDist
    : (scheme F).keygenDist pp =
      PMF.bind
        (Crypto.Infrastructure.Probability.uniformPMF pp.Scalar)
        (fun sk => PMF.pure (sk • pp.generator, sk)) := by
  unfold Scheme.keygenDist scheme CryptoFirstOrder.Builder.runCosted
  rw [RandCosted.valueDist_map]
  exact keygenProgram_valueDist pp

@[simp] theorem scheme_encryptDist
    (pk message : pp.Carrier) :
    (scheme F).encryptDist pp pk message =
      PMF.bind
        (Crypto.Infrastructure.Probability.uniformPMF pp.Scalar)
        (fun r =>
          PMF.pure (r • pp.generator, message + r • pk)) := by
  unfold Scheme.encryptDist scheme CryptoFirstOrder.Builder.runCosted
  rw [RandCosted.valueDist_map]
  exact encryptProgram_valueDist pp pk message

@[simp] theorem scheme_decryptDist
    (sk : pp.Scalar) (ciphertext : pp.Carrier × pp.Carrier) :
    (scheme F).decryptDist pp sk ciphertext =
      PMF.pure (ciphertext.2 - sk • ciphertext.1) := by
  unfold Scheme.decryptDist scheme CryptoFirstOrder.Builder.runCosted
  rw [RandCosted.valueDist_map]
  exact decryptProgram_valueDist pp sk ciphertext

end CryptoConstruction.Primitive.Encryption.AsymmetricEncryption.ElGamal

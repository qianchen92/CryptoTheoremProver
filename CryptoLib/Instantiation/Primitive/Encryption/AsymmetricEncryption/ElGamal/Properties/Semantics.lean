import CryptoLib.Core.Infrastructure.Probability.Uniform
import CryptoLib.Instantiation.Primitive.Encryption.AsymmetricEncryption.ElGamal.Scheme

namespace CryptoLib.Instantiation.Primitive.Encryption.AsymmetricEncryption.ElGamal

open CryptoLib.Core.Infrastructure.Computation
open CryptoLib.Core.Infrastructure.Computation.Cost
open CryptoLib.Core.Primitive.Encryption.AsymmetricEncryption
open scoped DDHParameter

universe uCost uParameter uScalar uGroup

variable
    {M : CostModel.{uCost}}
    {Parameter : Type uParameter}
    {Scalar : Type uScalar}
    {Carrier : Type uGroup}
    (F : Family M Parameter Scalar Carrier)
    (pp : PublicParam.{uCost, uScalar, uGroup} M Scalar Carrier)

@[simp] theorem setupProgram_runCosted
    (sec : CryptoLib.Core.SecPar) :
    Program.runCosted (setupProgram F) sec = RandCosted.map ULift.up (F.setup sec) :=
  rfl

@[simp] theorem scheme_setup_eq_family_setup
    (sec : CryptoLib.Core.SecPar) :
    (scheme F).setup sec = F.setup sec :=
  by
    change RandCosted.map ULift.down
      (Program.runCosted (setupProgram F) sec) = F.setup sec
    rw [setupProgram_runCosted]
    change PMF.map (Costed.map ULift.down)
      (PMF.map (Costed.map ULift.up) (F.setup sec)) = F.setup sec
    rw [PMF.map_comp]
    have mapIdentity :
        (Costed.map (M := M)
            (ULift.down : ULift.{max uScalar uGroup} Parameter → Parameter)) ∘
          (Costed.map (M := M)
            (ULift.up : Parameter → ULift.{max uScalar uGroup} Parameter)) =
          (id : Costed M Parameter → Costed M Parameter) := by
      funext result
      cases result
      rfl
    rw [mapIdentity, PMF.map_id]

/-- Erasing key-generation costs recovers ordinary ElGamal key generation. -/
@[simp] theorem keygenProgram_valueDist
    : PMF.map (Language.keyPairDown pp)
        (CryptoLib.Program.Procedure.valueDist
          (Language.algebra pp) (keygenProgram pp) (ULift.up ())) =
      PMF.bind
        (CryptoLib.Core.Infrastructure.Probability.uniformPMF pp.Scalar)
        (fun sk => PMF.pure (sk • pp.generator, sk)) := by
  change PMF.map (Language.keyPairDown pp)
    (CryptoLib.Program.Code.valueDist (Language.algebra pp) (keygenProgram pp).body
      (.cons (ULift.up ()) .nil)) = _
  simp only [keygenProgram, CryptoLib.Program.Builder.SmartCode.unifSamp,
    CryptoLib.Program.Builder.SmartCode.smul, CryptoLib.Program.SmartOperation.unifSamp,
    CryptoLib.Program.SmartOperation.smul, CryptoLib.Program.Signature.inject,
    CryptoLib.Program.Signature.Embedding.inject,
    CryptoLib.Program.Code.valueDist_call,
    CryptoLib.Program.Expr.eval,
    CryptoLib.Program.Assumption.DL.DDH.valueDist_exec_sampleScalar,
    CryptoLib.Program.Env.get,
    CryptoLib.Program.Assumption.DL.DDH.valueDist_exec_smul,
    CryptoLib.Program.Code.valueDist_ret]
  change
    PMF.map (Language.keyPairDown pp)
      (PMF.bind
        (PMF.map ULift.up
          (CryptoLib.Core.Infrastructure.Probability.uniformPMF pp.Scalar))
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
        (CryptoLib.Program.Procedure.valueDist
          (Language.algebra pp) (encryptProgram pp)
          (Language.liftCarrier pp pk,
            Language.liftCarrier pp message)) =
      PMF.bind
        (CryptoLib.Core.Infrastructure.Probability.uniformPMF pp.Scalar)
        (fun r =>
          PMF.pure (r • pp.generator, message + r • pk)) := by
  change PMF.map (Language.carrierPairDown pp)
    (CryptoLib.Program.Code.valueDist (Language.algebra pp) (encryptProgram pp).body
      (.cons
        (Language.liftCarrier pp pk,
          Language.liftCarrier pp message) .nil)) = _
  simp only [encryptProgram, CryptoLib.Program.Builder.SmartCode.unifSamp,
    CryptoLib.Program.Builder.SmartCode.smul, CryptoLib.Program.Builder.SmartCode.add,
    CryptoLib.Program.SmartOperation.unifSamp, CryptoLib.Program.SmartOperation.smul,
    CryptoLib.Program.SmartOperation.add, CryptoLib.Program.Signature.inject,
    CryptoLib.Program.Signature.Embedding.inject,
    CryptoLib.Program.Code.valueDist_call,
    CryptoLib.Program.Expr.eval,
    CryptoLib.Program.Assumption.DL.DDH.valueDist_exec_sampleScalar,
    CryptoLib.Program.Env.get,
    CryptoLib.Program.Assumption.DL.DDH.valueDist_exec_smul,
    CryptoLib.Program.Assumption.DL.DDH.valueDist_exec_add,
    CryptoLib.Program.Code.valueDist_ret]
  change
    PMF.map (Language.carrierPairDown pp)
      (PMF.bind
        (PMF.map ULift.up
          (CryptoLib.Core.Infrastructure.Probability.uniformPMF pp.Scalar))
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
        (CryptoLib.Program.Procedure.valueDist
          (Language.algebra pp) (decryptProgram pp)
          (Language.liftScalar pp sk,
            (Language.liftCarrier pp ciphertext.1,
              Language.liftCarrier pp ciphertext.2))) =
      PMF.pure (ciphertext.2 - sk • ciphertext.1) := by
  change PMF.map ULift.down
    (CryptoLib.Program.Code.valueDist (Language.algebra pp) (decryptProgram pp).body
      (.cons
        (Language.liftScalar pp sk,
          (Language.liftCarrier pp ciphertext.1,
            Language.liftCarrier pp ciphertext.2)) .nil)) = _
  simp only [decryptProgram, CryptoLib.Program.Builder.SmartCode.smul,
    CryptoLib.Program.Builder.SmartCode.sub, CryptoLib.Program.SmartOperation.smul,
    CryptoLib.Program.SmartOperation.sub, CryptoLib.Program.Signature.inject,
    CryptoLib.Program.Signature.Embedding.inject,
    CryptoLib.Program.Code.valueDist_call,
    CryptoLib.Program.Expr.eval, CryptoLib.Program.Env.get,
    CryptoLib.Program.Assumption.DL.DDH.valueDist_exec_smul,
    CryptoLib.Program.Assumption.DL.DDH.valueDist_exec_sub,
    CryptoLib.Program.Code.valueDist_ret, PMF.bind_pure]
  change
    PMF.map ULift.down
      (PMF.bind (PMF.pure (ULift.up (sk • ciphertext.1)))
        (fun shared => PMF.pure (ULift.up (ciphertext.2 - shared.down)))) = _
  rw [PMF.map_bind, PMF.pure_bind, PMF.pure_map]

@[simp] theorem scheme_setupDist
    (sec : CryptoLib.Core.SecPar) :
    (scheme F).setupDist sec = F.setupDist sec :=
  by
    unfold Scheme.setupDist
    rw [scheme_setup_eq_family_setup]
    rfl

@[simp] theorem scheme_keygenDist
    (parameter : Parameter) :
    (scheme F).keygenDist parameter =
      PMF.bind
        (@CryptoLib.Core.Infrastructure.Probability.uniformPMF
          Scalar (F.publicParam parameter).fintypeScalar
          ⟨(F.publicParam parameter).commMonoidScalar.one⟩)
        (fun sk =>
          PMF.pure
            ((F.publicParam parameter).smul.smul sk
              (F.publicParam parameter).generator, sk)) := by
  unfold Scheme.keygenDist scheme CryptoLib.Program.Builder.runCosted
  rw [RandCosted.valueDist_map]
  exact keygenProgram_valueDist (F.publicParam parameter)

@[simp] theorem scheme_encryptDist
    (parameter : Parameter) (pk message : Carrier) :
    (scheme F).encryptDist parameter pk message =
      PMF.bind
        (@CryptoLib.Core.Infrastructure.Probability.uniformPMF
          Scalar (F.publicParam parameter).fintypeScalar
          ⟨(F.publicParam parameter).commMonoidScalar.one⟩)
        (fun r =>
          PMF.pure
            ((F.publicParam parameter).smul.smul r
                (F.publicParam parameter).generator,
              (F.publicParam parameter).addGroup.add message
                ((F.publicParam parameter).smul.smul r pk))) := by
  unfold Scheme.encryptDist scheme CryptoLib.Program.Builder.runCosted
  rw [RandCosted.valueDist_map]
  exact encryptProgram_valueDist (F.publicParam parameter) pk message

@[simp] theorem scheme_decryptDist
    (parameter : Parameter) (sk : Scalar) (ciphertext : Carrier × Carrier) :
    (scheme F).decryptDist parameter sk ciphertext =
      PMF.pure
        ((F.publicParam parameter).addGroup.sub ciphertext.2
          ((F.publicParam parameter).smul.smul sk ciphertext.1)) := by
  unfold Scheme.decryptDist scheme CryptoLib.Program.Builder.runCosted
  rw [RandCosted.valueDist_map]
  exact decryptProgram_valueDist (F.publicParam parameter) sk ciphertext

end CryptoLib.Instantiation.Primitive.Encryption.AsymmetricEncryption.ElGamal

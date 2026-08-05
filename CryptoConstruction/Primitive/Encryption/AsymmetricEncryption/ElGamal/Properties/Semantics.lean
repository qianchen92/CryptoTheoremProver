import Crypto.Infrastructure.Probability.Uniform
import CryptoConstruction.Primitive.Encryption.AsymmetricEncryption.ElGamal.Scheme

namespace CryptoConstruction.Primitive.Encryption.AsymmetricEncryption.ElGamal

open Crypto.Infrastructure.Computation
open Crypto.Infrastructure.Computation.Cost
open Crypto.Primitive.Encryption.AsymmetricEncryption
open scoped DDHParameter

universe uCost uScalar uGroup

variable {M : CostModel.{uCost}}

namespace Language

@[simp] theorem valueDist_exec_sampleScalar
    (pp : PublicParam.{uCost, uScalar, uGroup} M)
    (args : FirstOrder.Ty.denote (interpret pp) .unit) :
    RandCosted.valueDist ((algebra pp).exec Operation.sampleScalar args) =
      PMF.map ULift.up
        (Crypto.Infrastructure.Probability.uniformPMF pp.Scalar) :=
  (Crypto.Assumption.DL.DDH.algebraLaws pp).exec_spec
    Crypto.Assumption.DL.DDH.Op.sampleScalar

@[simp] theorem valueDist_exec_smul
    (pp : PublicParam.{uCost, uScalar, uGroup} M)
    (args : FirstOrder.Ty.denote (interpret pp)
      (.prod scalarTy carrierTy)) :
    RandCosted.valueDist ((algebra pp).exec Operation.smul args) =
      PMF.pure (ULift.up (args.1.down • args.2.down)) :=
  (Crypto.Assumption.DL.DDH.algebraLaws pp).exec_spec
    (Crypto.Assumption.DL.DDH.Op.smul args.1.down args.2.down)

@[simp] theorem valueDist_exec_add
    (pp : PublicParam.{uCost, uScalar, uGroup} M)
    (args : FirstOrder.Ty.denote (interpret pp)
      (.prod carrierTy carrierTy)) :
    RandCosted.valueDist ((algebra pp).exec Operation.add args) =
      PMF.pure (ULift.up (args.1.down + args.2.down)) :=
  (Crypto.Assumption.DL.DDH.algebraLaws pp).exec_spec
    (Crypto.Assumption.DL.DDH.Op.add args.1.down args.2.down)

@[simp] theorem valueDist_exec_sub
    (pp : PublicParam.{uCost, uScalar, uGroup} M)
    (args : FirstOrder.Ty.denote (interpret pp)
      (.prod carrierTy carrierTy)) :
    RandCosted.valueDist ((algebra pp).exec Operation.sub args) =
      PMF.pure (ULift.up (args.1.down - args.2.down)) :=
  (Crypto.Assumption.DL.DDH.algebraLaws pp).exec_spec
    (Crypto.Assumption.DL.DDH.Op.sub args.1.down args.2.down)

end Language

@[simp] theorem scheme_setup_eq_family_setup
    (F : Family.{uCost, uScalar, uGroup} M) (sec : Crypto.SecPar) :
    (scheme F).setup sec = F.setup sec :=
  rfl

/-- Erasing key-generation costs recovers ordinary ElGamal key generation. -/
@[simp] theorem keygenProgram_valueDist
    (pp : PublicParam.{uCost, uScalar, uGroup} M) :
    PMF.map (Language.keyPairDown pp)
        (FirstOrder.Program.valueDist
          (Language.algebra pp) (keygenProgram pp) (ULift.up ())) =
      PMF.bind
        (Crypto.Infrastructure.Probability.uniformPMF pp.Scalar)
        (fun secretKey => PMF.pure (secretKey • pp.generator, secretKey)) := by
  change PMF.map (Language.keyPairDown pp)
    (FirstOrder.Code.valueDist (Language.algebra pp) (keygenProgram pp).body
      (.cons (ULift.up ()) .nil)) = _
  simp only [keygenProgram, FirstOrder.Code.valueDist_call,
    FirstOrder.Expr.eval, Language.valueDist_exec_sampleScalar,
    FirstOrder.Env.get, Language.valueDist_exec_smul,
    FirstOrder.Code.valueDist_ret]
  change
    PMF.map (Language.keyPairDown pp)
      (PMF.bind
        (PMF.map ULift.up
          (Crypto.Infrastructure.Probability.uniformPMF pp.Scalar))
        (fun secretKey =>
          PMF.bind (PMF.pure (ULift.up (secretKey.down • pp.generator)))
            (fun publicKey => PMF.pure (publicKey, secretKey)))) = _
  rw [PMF.map_bind, PMF.bind_map]
  simp only [PMF.pure_bind, PMF.pure_map]
  rfl

/-- Erasing encryption costs recovers ordinary ElGamal encryption. -/
@[simp] theorem encryptProgram_valueDist
    (pp : PublicParam.{uCost, uScalar, uGroup} M)
    (publicKey message : pp.Carrier) :
    PMF.map (Language.carrierPairDown pp)
        (FirstOrder.Program.valueDist
          (Language.algebra pp) (encryptProgram pp)
          (Language.liftCarrier pp publicKey,
            Language.liftCarrier pp message)) =
      PMF.bind
        (Crypto.Infrastructure.Probability.uniformPMF pp.Scalar)
        (fun nonce =>
          PMF.pure (nonce • pp.generator, message + nonce • publicKey)) := by
  change PMF.map (Language.carrierPairDown pp)
    (FirstOrder.Code.valueDist (Language.algebra pp) (encryptProgram pp).body
      (.cons
        (Language.liftCarrier pp publicKey,
          Language.liftCarrier pp message) .nil)) = _
  simp only [encryptProgram, FirstOrder.Code.valueDist_call,
    FirstOrder.Expr.eval, Language.valueDist_exec_sampleScalar,
    FirstOrder.Env.get, Language.valueDist_exec_smul,
    Language.valueDist_exec_add, FirstOrder.Code.valueDist_ret]
  change
    PMF.map (Language.carrierPairDown pp)
      (PMF.bind
        (PMF.map ULift.up
          (Crypto.Infrastructure.Probability.uniformPMF pp.Scalar))
        (fun nonce =>
          PMF.bind (PMF.pure (ULift.up (nonce.down • pp.generator)))
            (fun firstComponent =>
              PMF.bind (PMF.pure (ULift.up (nonce.down • publicKey)))
                (fun shared =>
                  PMF.bind (PMF.pure (ULift.up (message + shared.down)))
                    (fun secondComponent =>
                      PMF.pure (firstComponent, secondComponent)))))) = _
  rw [PMF.map_bind, PMF.bind_map]
  simp only [PMF.pure_bind, PMF.pure_map]
  rfl

/-- Erasing decryption costs recovers ordinary ElGamal decryption. -/
@[simp] theorem decryptProgram_valueDist
    (pp : PublicParam.{uCost, uScalar, uGroup} M)
    (secretKey : pp.Scalar) (ciphertext : pp.Carrier × pp.Carrier) :
    PMF.map ULift.down
        (FirstOrder.Program.valueDist
          (Language.algebra pp) (decryptProgram pp)
          (Language.liftScalar pp secretKey,
            (Language.liftCarrier pp ciphertext.1,
              Language.liftCarrier pp ciphertext.2))) =
      PMF.pure (ciphertext.2 - secretKey • ciphertext.1) := by
  change PMF.map ULift.down
    (FirstOrder.Code.valueDist (Language.algebra pp) (decryptProgram pp).body
      (.cons
        (Language.liftScalar pp secretKey,
          (Language.liftCarrier pp ciphertext.1,
            Language.liftCarrier pp ciphertext.2)) .nil)) = _
  simp only [decryptProgram, FirstOrder.Code.valueDist_call,
    FirstOrder.Expr.eval, FirstOrder.Env.get,
    Language.valueDist_exec_smul, Language.valueDist_exec_sub,
    FirstOrder.Code.valueDist_ret, PMF.bind_pure]
  change
    PMF.map ULift.down
      (PMF.bind (PMF.pure (ULift.up (secretKey • ciphertext.1)))
        (fun shared => PMF.pure (ULift.up (ciphertext.2 - shared.down)))) = _
  rw [PMF.map_bind, PMF.pure_bind, PMF.pure_map]

@[simp] theorem scheme_setupDist
    (F : Family.{uCost, uScalar, uGroup} M) (sec : Crypto.SecPar) :
    (scheme F).setupDist sec = F.setupDist sec :=
  rfl

@[simp] theorem scheme_keygenDist
    (F : Family.{uCost, uScalar, uGroup} M)
    (pp : PublicParam.{uCost, uScalar, uGroup} M) :
    (scheme F).keygenDist pp =
      PMF.bind
        (Crypto.Infrastructure.Probability.uniformPMF pp.Scalar)
        (fun secretKey => PMF.pure (secretKey • pp.generator, secretKey)) := by
  unfold Scheme.keygenDist scheme
  rw [RandCosted.valueDist_map]
  exact keygenProgram_valueDist pp

@[simp] theorem scheme_encryptDist
    (F : Family.{uCost, uScalar, uGroup} M)
    (pp : PublicParam.{uCost, uScalar, uGroup} M)
    (publicKey message : pp.Carrier) :
    (scheme F).encryptDist pp publicKey message =
      PMF.bind
        (Crypto.Infrastructure.Probability.uniformPMF pp.Scalar)
        (fun nonce =>
          PMF.pure (nonce • pp.generator, message + nonce • publicKey)) := by
  unfold Scheme.encryptDist scheme
  rw [RandCosted.valueDist_map]
  exact encryptProgram_valueDist pp publicKey message

@[simp] theorem scheme_decryptDist
    (F : Family.{uCost, uScalar, uGroup} M)
    (pp : PublicParam.{uCost, uScalar, uGroup} M)
    (secretKey : pp.Scalar) (ciphertext : pp.Carrier × pp.Carrier) :
    (scheme F).decryptDist pp secretKey ciphertext =
      PMF.pure (ciphertext.2 - secretKey • ciphertext.1) := by
  unfold Scheme.decryptDist scheme
  rw [RandCosted.valueDist_map]
  exact decryptProgram_valueDist pp secretKey ciphertext

end CryptoConstruction.Primitive.Encryption.AsymmetricEncryption.ElGamal

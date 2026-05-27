import Crypto.Primitive.Encryption.AsymmetricEncryption.Instantiations.ElGamal.Construction
import Crypto.Primitive.Encryption.AsymmetricEncryption.Properties.Correctness

namespace Crypto.Primitive.Encryption.AsymmetricEncryption.Instantiations.ElGamal

universe uScalar uGroup

open Crypto.Primitive.Encryption.AsymmetricEncryption

/-- The scalar action condition needed for ElGamal decryption to reconstruct the shared secret. -/
def CompatibleScalarAction : Prop :=
  ∀ (pp : PublicParam.{uScalar, uGroup}) (secretKey nonce : pp.Scalar),
    secretKey • (nonce • pp.generator) = nonce • (secretKey • pp.generator)

/-- Correctness of ElGamal under the compatible scalar action condition. -/
theorem correct
    (F : Crypto.Assumption.DL.DDH.Family.{uScalar, uGroup})
    (hCompatible : CompatibleScalarAction.{uScalar, uGroup}) :
    Correct (scheme F) := by
  intro _sec pp publicKey secretKey message _hpp hkey
  change (publicKey, secretKey) ∈
    (PMF.bind (Crypto.Infrastructure.Computation.Distribution.uniformPMF pp.Scalar) fun secretKey =>
      PMF.pure (secretKey • pp.generator, secretKey)).support at hkey
  have hkey' := (PMF.mem_support_bind_iff
    (p := Crypto.Infrastructure.Computation.Distribution.uniformPMF pp.Scalar)
    (f := fun secretKey => PMF.pure (secretKey • pp.generator, secretKey))
    (b := (publicKey, secretKey))).mp hkey
  rcases hkey' with ⟨sampledSecretKey, _hsampled, hkeys⟩
  rw [PMF.mem_support_pure_iff] at hkeys
  injection hkeys with hpublicKey hsecretKey
  subst publicKey
  subst secretKey
  change
    (PMF.bind
      (PMF.bind (Crypto.Infrastructure.Computation.Distribution.uniformPMF pp.Scalar) fun nonce =>
        PMF.pure
          (nonce • pp.generator,
            message + nonce • (sampledSecretKey • pp.generator)))
      fun ciphertext =>
        PMF.pure (ciphertext.2 - sampledSecretKey • ciphertext.1)) =
    PMF.pure message
  rw [PMF.bind_bind]
  simp [hCompatible pp sampledSecretKey]

end Crypto.Primitive.Encryption.AsymmetricEncryption.Instantiations.ElGamal

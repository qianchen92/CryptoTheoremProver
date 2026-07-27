import Crypto.Primitive.Encryption.AsymmetricEncryption.Instantiations.ElGamal.Scheme
import Crypto.Primitive.Encryption.AsymmetricEncryption.Properties.Correctness

namespace Crypto.Primitive.Encryption.AsymmetricEncryption.Instantiations.ElGamal

universe uScalar uGroup

open Crypto.Primitive.Encryption.AsymmetricEncryption

/-- Correctness of ElGamal under the scalar action law carried by public parameters. -/
theorem correct
    (F : Crypto.Assumption.DL.DDH.Family.{uScalar, uGroup}) :
    Correct (scheme F) := by
  intro _sec pp publicKey secretKey message _hpp hkey
  rw [scheme_keygenDist] at hkey
  have hkey' := (PMF.mem_support_bind_iff
    (p := Crypto.Infrastructure.Computation.Distribution.uniformPMF pp.Scalar)
    (f := fun secretKey => PMF.pure (secretKey • pp.generator, secretKey))
    (b := (publicKey, secretKey))).mp hkey
  rcases hkey' with ⟨sampledSecretKey, _hsampled, hkeys⟩
  rw [PMF.mem_support_pure_iff] at hkeys
  injection hkeys with hpublicKey hsecretKey
  subst publicKey
  subst secretKey
  rw [scheme_encryptDist]
  simp_rw [scheme_decryptValue]
  rw [PMF.bind_bind]
  simp [pp.compatibleScalarAction sampledSecretKey]

end Crypto.Primitive.Encryption.AsymmetricEncryption.Instantiations.ElGamal

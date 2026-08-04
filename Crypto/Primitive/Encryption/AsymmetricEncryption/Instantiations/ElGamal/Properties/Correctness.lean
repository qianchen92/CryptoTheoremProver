import Crypto.Primitive.Encryption.AsymmetricEncryption.Instantiations.ElGamal.Scheme
import Crypto.Primitive.Encryption.AsymmetricEncryption.Properties.Correctness
import Crypto.Infrastructure.Probability.Uniform

namespace Crypto.Primitive.Encryption.AsymmetricEncryption.Instantiations.ElGamal

universe uCost uScalar uGroup

open Crypto.Infrastructure.Computation.Cost
open Crypto.Primitive.Encryption.AsymmetricEncryption
open scoped DDHParameter

/-- Correctness of ElGamal under the scalar action law carried by public parameters. -/
theorem correct
    {M : CostModel.{uCost}}
    (F : Crypto.Assumption.DL.DDH.Family.{uCost, uScalar, uGroup} M) :
    Correct (scheme F) := by
  intro _sec pp publicKey secretKey message _hpp hkey
  rw [scheme_keygenDist] at hkey
  have hkey' := (PMF.mem_support_bind_iff
    (p := Crypto.Infrastructure.Probability.uniformPMF pp.Scalar)
    (f := fun secretKey => PMF.pure (secretKey • pp.generator, secretKey))
    (b := (publicKey, secretKey))).mp hkey
  rcases hkey' with ⟨sampledSecretKey, _hsampled, hkeys⟩
  rw [PMF.mem_support_pure_iff] at hkeys
  injection hkeys with hpublicKey hsecretKey
  subst publicKey
  subst secretKey
  rw [scheme_encryptDist]
  simp_rw [scheme_decryptDist]
  rw [PMF.bind_bind]
  simp [pp.scalarAction_commutes sampledSecretKey]

end Crypto.Primitive.Encryption.AsymmetricEncryption.Instantiations.ElGamal

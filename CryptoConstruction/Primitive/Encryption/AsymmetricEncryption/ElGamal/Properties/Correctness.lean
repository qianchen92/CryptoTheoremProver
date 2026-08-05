import CryptoConstruction.Primitive.Encryption.AsymmetricEncryption.ElGamal.Properties.Semantics
import Crypto.Primitive.Encryption.AsymmetricEncryption.Properties.Correctness
import Crypto.Infrastructure.Probability.Uniform

namespace CryptoConstruction.Primitive.Encryption.AsymmetricEncryption.ElGamal

universe uCost uScalar uGroup

open scoped DDHParameter

variable
    {M : Crypto.Infrastructure.Computation.Cost.CostModel.{uCost}}
    (F : Family.{uCost, uScalar, uGroup} M)

/-- Correctness of ElGamal under the scalar action law carried by public parameters. -/
theorem correct :
    Crypto.Primitive.Encryption.AsymmetricEncryption.Correct (scheme F) := by
  intro _sec pp pk sk message _hpp hkey
  rw [scheme_keygenDist] at hkey
  have hkey' := (PMF.mem_support_bind_iff
    (p := Crypto.Infrastructure.Probability.uniformPMF pp.Scalar)
    (f := fun sk => PMF.pure (sk • pp.generator, sk))
    (b := (pk, sk))).mp hkey
  rcases hkey' with ⟨sampledSk, _hsampled, hkeys⟩
  rw [PMF.mem_support_pure_iff] at hkeys
  injection hkeys with hpk hsk
  subst pk
  subst sk
  rw [scheme_encryptDist]
  simp_rw [scheme_decryptDist]
  rw [PMF.bind_bind]
  simp [pp.scalarAction_commutes sampledSk]

end CryptoConstruction.Primitive.Encryption.AsymmetricEncryption.ElGamal

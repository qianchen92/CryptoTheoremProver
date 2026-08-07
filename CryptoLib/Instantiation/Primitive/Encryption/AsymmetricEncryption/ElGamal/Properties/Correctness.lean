import CryptoLib.Instantiation.Primitive.Encryption.AsymmetricEncryption.ElGamal.Properties.Semantics
import CryptoLib.Core.Primitive.Encryption.AsymmetricEncryption.Properties.Correctness
import CryptoLib.Core.Infrastructure.Probability.Uniform

namespace CryptoLib.Instantiation.Primitive.Encryption.AsymmetricEncryption.ElGamal

universe uCost uParameter uScalar uGroup

open scoped DDHParameter

variable
    {M : CryptoLib.Core.Infrastructure.Computation.Cost.CostModel.{uCost}}
    {Parameter : Type uParameter}
    {Scalar : Type uScalar}
    {Carrier : Type uGroup}
    (F : Family M Parameter Scalar Carrier)

/-- Correctness of ElGamal under the scalar action law carried by public parameters. -/
theorem correct :
    CryptoLib.Core.Primitive.Encryption.AsymmetricEncryption.Correct (scheme F) := by
  intro _sec pp pk sk message _hpp hkey
  let backend := F.publicParam pp
  letI : AddGroup Carrier := backend.addGroup
  letI : SMul Scalar Carrier := backend.smul
  letI : CommMonoid Scalar := backend.commMonoidScalar
  rw [scheme_keygenDist] at hkey
  have hkey' := (PMF.mem_support_bind_iff
    (p := @CryptoLib.Core.Infrastructure.Probability.uniformPMF
      Scalar backend.fintypeScalar ⟨backend.commMonoidScalar.one⟩)
    (f := fun sk => PMF.pure (sk • backend.generator, sk))
    (b := (pk, sk))).mp hkey
  rcases hkey' with ⟨sampledSk, _hsampled, hkeys⟩
  rw [PMF.mem_support_pure_iff] at hkeys
  injection hkeys with hpk hsk
  subst pk
  subst sk
  rw [scheme_encryptDist]
  simp_rw [scheme_decryptDist]
  rw [PMF.bind_bind]
  simp only [PMF.pure_bind]
  change PMF.bind _ (fun (a : Scalar) => PMF.pure
    ((message + a • (sampledSk • backend.generator)) -
      sampledSk • (a • backend.generator))) = PMF.pure message
  have hpoint (a : Scalar) :
      (message + a • (sampledSk • backend.generator)) -
          sampledSk • (a • backend.generator) = message := by
    rw [backend.scalarAction_commutes sampledSk a]
    exact add_sub_cancel_right message _
  simp_rw [hpoint]
  exact PMF.bind_const _ _

end CryptoLib.Instantiation.Primitive.Encryption.AsymmetricEncryption.ElGamal

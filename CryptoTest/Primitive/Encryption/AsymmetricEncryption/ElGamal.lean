import CryptoTest.Assumption.DL.DDH
import Crypto.Primitive.Encryption.AsymmetricEncryption.Instantiations.ElGamal.Basic

namespace CryptoTest.Primitive.Encryption.AsymmetricEncryption.ElGamal

open Crypto.Infrastructure.Computation.Algebra
open Crypto.Infrastructure.Computation.Cost
open Crypto.Primitive.Encryption.AsymmetricEncryption
open Crypto.Primitive.Encryption.AsymmetricEncryption.Instantiations.ElGamal
open CryptoTest.Assumption.DL
open scoped DDHParameter

/-- The derived encryption budget is sample plus two scalar actions plus addition. -/
example :
    encryptBudget DDH.testPublicParam DDH.testParamEfficiency = 29 :=
  rfl

/-- The derived decryption budget is one scalar action plus subtraction. -/
example :
    decryptBudget DDH.testPublicParam DDH.testParamEfficiency = 17 :=
  rfl

/-- Every concrete encryption path has the exact four-operation cost 2+11+11+5. -/
example
    (publicKey message : DDH.testPublicParam.Carrier)
    (result : Costed
      (DDH.testPublicParam.Carrier × DDH.testPublicParam.Carrier))
    (hresult : result ∈
      (encryptComputation DDH.testPublicParam publicKey message).support) :
    result.cost = 29 := by
  rcases encryptComputation_exactCost
      DDH.testPublicParam publicKey message result hresult with
    ⟨sampleResult, hsampleResult, _hvalue, hcost⟩
  have hsampleCost : sampleResult.cost = 2 := by
    change sampleResult ∈
      (UniformSampler.ofConstantCost
        (Sample := DDH.testPublicParam.Scalar) 2).sample.support at hsampleResult
    simp only [UniformSampler.ofConstantCost, UniformSampler.ofCost,
      RandCosted.sampleWithCost, RandCostedT.sampleWithCost] at hsampleResult
    rw [PMF.mem_support_map_iff] at hsampleResult
    rcases hsampleResult with ⟨sampleValue, _hsampleValue, hsampleResult⟩
    subst sampleResult
    rfl
  rw [hcost, hsampleCost]
  rfl

/-- The scheme boundary erases setup costs without changing the DDH distribution. -/
example (sec : Crypto.SecPar) :
    (scheme DDH.testFamily).setupDist sec =
      DDH.testFamily.setupDist sec :=
  scheme_setupDist DDH.testFamily sec

/-- ElGamal executes setup through the typed DDH family program exactly. -/
example (sec : Crypto.SecPar) :
    (scheme DDH.testFamily).setup sec =
      Crypto.Infrastructure.Computation.Program.runCosted
        (Crypto.Assumption.DL.DDH.setupProgram DDH.testFamily) sec :=
  rfl

/-- Typed setup dispatch preserves the native setup computation path-for-path. -/
example (sec : Crypto.SecPar) :
    (scheme DDH.testFamily).setup sec = DDH.testFamily.setup sec :=
  scheme_setup_eq_family_setup DDH.testFamily sec

/-- The scheme boundary exposes the cost-erased ElGamal key distribution. -/
example :
    (scheme DDH.testFamily).keygenDist DDH.testPublicParam =
      PMF.bind
        (Crypto.Infrastructure.Computation.Distribution.uniformPMF
          DDH.testPublicParam.Scalar)
        (fun secretKey =>
          PMF.pure
            (secretKey • DDH.testPublicParam.generator, secretKey)) :=
  scheme_keygenDist DDH.testFamily DDH.testPublicParam

/-- The scheme boundary erases decryption costs without changing its value. -/
example
    (secretKey : DDH.testPublicParam.Scalar)
    (ciphertext :
      DDH.testPublicParam.Carrier × DDH.testPublicParam.Carrier) :
    (scheme DDH.testFamily).decryptValue
        DDH.testPublicParam secretKey ciphertext =
      ciphertext.2 - secretKey • ciphertext.1 :=
  scheme_decryptValue DDH.testFamily DDH.testPublicParam secretKey ciphertext

/-- Concrete ElGamal decryption derives its cost from scalar action and subtraction. -/
example
    (secretKey : DDH.testPublicParam.Scalar)
    (ciphertext :
      DDH.testPublicParam.Carrier × DDH.testPublicParam.Carrier) :
    ((scheme DDH.testFamily).decrypt
        DDH.testPublicParam secretKey ciphertext).cost = 17 :=
  rfl

/-- The timed encryption machine exposes the original ElGamal distribution. -/
example
    (sec : Crypto.SecPar)
    (input :
      DDH.testPublicParam.Carrier × DDH.testPublicParam.Carrier) :
    (encryptTimedMachine
        DDH.testPublicParam DDH.testParamEfficiency).runDist sec input =
      (scheme DDH.testFamily).encryptDist
        DDH.testPublicParam input.1 input.2 :=
  encryptTimedMachine_runDist
    DDH.testFamily DDH.testPublicParam DDH.testParamEfficiency sec input

/-- The concrete costed scheme satisfies the generic correctness interface. -/
example :
    Correct (scheme DDH.testFamily) :=
  correct DDH.testFamily

end CryptoTest.Primitive.Encryption.AsymmetricEncryption.ElGamal

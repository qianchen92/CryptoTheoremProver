import CryptoTest.Assumption.DL.DDH
import Crypto.Primitive.Encryption.AsymmetricEncryption.Instantiations.ElGamal.Basic
import Crypto.Infrastructure.Probability.Uniform

namespace CryptoTest.Primitive.Encryption.AsymmetricEncryption.ElGamal

open Crypto.Infrastructure.Computation
open Crypto.Infrastructure.Computation.Cost
open Crypto.Primitive.Encryption.AsymmetricEncryption
open Crypto.Primitive.Encryption.AsymmetricEncryption.Instantiations.ElGamal
open CryptoTest.Assumption.DL
open scoped DDHParameter

/-- The encryption budget is sample plus two scalar actions plus addition. -/
example :
    encryptBudget DDH.testPublicParam DDH.testParamEfficiency = 29 :=
  rfl

/-- The decryption budget is one scalar action plus subtraction. -/
example :
    decryptBudget DDH.testPublicParam DDH.testParamEfficiency = 17 :=
  rfl

/-- Every concrete encryption path has exact cost `2 + 11 + 11 + 5`. -/
example
    (publicKey message : DDH.testPublicParam.Carrier)
    (result : Costed CostModel.nat
      (ULift (DDH.testPublicParam.Carrier × DDH.testPublicParam.Carrier)))
    (hresult : result ∈
      (Program.runCosted
        (encryptProgram DDH.testPublicParam) (publicKey, message)).support) :
    result.cost = 29 := by
  rcases encryptProgram_exactCost
      DDH.testPublicParam publicKey message result hresult with
    ⟨sampleResult, hsample, firstResult, hfirst,
      sharedResult, hshared, additionResult, haddition, _hvalue, hcost⟩
  have hsampleCost : sampleResult.cost = 2 := by
    simp only [DDH.testPublicParam, DDH.testAlgebra,
      RandCosted.sampleWithCost] at hsample
    rw [PMF.support_map] at hsample
    rcases hsample with ⟨sampleValue, _hsampleValue, hsample⟩
    subst sampleResult
    rfl
  have hfirstCost : firstResult.cost = 11 := by
    simp only [DDH.testPublicParam, DDH.testAlgebra,
      RandCosted.liftCosted] at hfirst
    rw [PMF.support_pure] at hfirst
    exact congrArg Costed.cost (show firstResult = _ from hfirst)
  have hsharedCost : sharedResult.cost = 11 := by
    simp only [DDH.testPublicParam, DDH.testAlgebra,
      RandCosted.liftCosted] at hshared
    rw [PMF.support_pure] at hshared
    exact congrArg Costed.cost (show sharedResult = _ from hshared)
  have hadditionCost : additionResult.cost = 5 := by
    simp only [DDH.testPublicParam, DDH.testAlgebra,
      RandCosted.liftCosted] at haddition
    rw [PMF.support_pure] at haddition
    exact congrArg Costed.cost (show additionResult = _ from haddition)
  rw [hcost, hsampleCost, hfirstCost, hsharedCost, hadditionCost]
  rfl

/-- The scheme erases setup costs without changing the DDH distribution. -/
example (sec : Crypto.SecPar) :
    (scheme DDH.testFamily).setupDist sec =
      DDH.testFamily.setupDist sec :=
  scheme_setupDist DDH.testFamily sec

/-- Setup is the authoritative family computation path-for-path. -/
example (sec : Crypto.SecPar) :
    (scheme DDH.testFamily).setup sec = DDH.testFamily.setup sec :=
  scheme_setup_eq_family_setup DDH.testFamily sec

/-- The scheme boundary exposes ordinary ElGamal key generation. -/
example :
    (scheme DDH.testFamily).keygenDist DDH.testPublicParam =
      PMF.bind
        (Crypto.Infrastructure.Probability.uniformPMF
          DDH.testPublicParam.Scalar)
        (fun secretKey =>
          PMF.pure
            (secretKey • DDH.testPublicParam.generator, secretKey)) :=
  scheme_keygenDist DDH.testFamily DDH.testPublicParam

/-- Cost erasure of decryption gives the ordinary ElGamal plaintext. -/
example
    (secretKey : DDH.testPublicParam.Scalar)
    (ciphertext :
      DDH.testPublicParam.Carrier × DDH.testPublicParam.Carrier) :
    (scheme DDH.testFamily).decryptDist
        DDH.testPublicParam secretKey ciphertext =
      PMF.pure (ciphertext.2 - secretKey • ciphertext.1) :=
  scheme_decryptDist DDH.testFamily DDH.testPublicParam secretKey ciphertext

/-- Concrete decryption has exact scalar-action-plus-subtraction cost. -/
example
    (secretKey : DDH.testPublicParam.Scalar)
    (ciphertext :
      DDH.testPublicParam.Carrier × DDH.testPublicParam.Carrier) :
    Program.runCosted (decryptProgram DDH.testPublicParam)
        (secretKey, ciphertext) =
      PMF.pure
        (⟨ULift.up (ciphertext.2 - secretKey • ciphertext.1), 17⟩ :
          Costed CostModel.nat (ULift DDH.testPublicParam.Carrier)) := by
  change
    Program.runCosted (decryptProgram DDH.testPublicParam)
        (secretKey, ciphertext) =
      PMF.pure
        (⟨ULift.up
            (DDH.testMath.addGroup.sub ciphertext.2
              (DDH.testMath.smul.smul secretKey ciphertext.1)), 17⟩ :
          Costed CostModel.nat (ULift DDH.testMath.Carrier))
  simp [Program.runCosted, decryptProgram, Program.Code.runCosted,
    DDH.testPublicParam, DDH.testAlgebra, RandCosted.bind,
    RandCosted.liftCosted, PMF.pure_map, Costed.bind]

/-- The timed adapter preserves the ordinary ElGamal encryption distribution. -/
example
    (sec : Crypto.SecPar)
    (input :
      DDH.testPublicParam.Carrier × DDH.testPublicParam.Carrier) :
    (encryptTimedMachine NatMeasure.nat
        DDH.testPublicParam DDH.testParamEfficiency).runDist sec input =
      (scheme DDH.testFamily).encryptDist
        DDH.testPublicParam input.1 input.2 :=
  encryptTimedMachine_runDist NatMeasure.nat
    DDH.testFamily DDH.testPublicParam DDH.testParamEfficiency sec input

/-- The cost-aware scheme retains the generic correctness theorem. -/
example :
    Correct (scheme DDH.testFamily) :=
  correct DDH.testFamily

end CryptoTest.Primitive.Encryption.AsymmetricEncryption.ElGamal

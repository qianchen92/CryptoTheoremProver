import Crypto.Primitive.Encryption.SymmetricEncryption.Instantiations.OneTimePad.Basic
import Mathlib.Data.ZMod.Basic

namespace CryptoTest.Primitive.Encryption.SymmetricEncryption.OneTimePad

open Crypto.Infrastructure.Computation.Algebra
open Crypto.Primitive.Encryption.SymmetricEncryption
open Crypto.Primitive.Encryption.SymmetricEncryption.Instantiations.OneTimePad

/-- A concrete two-element OTP parameter with native exact-cost operations. -/
noncomputable def testPublicParam : PublicParam where
  Carrier := ZMod 2
  addGroup := inferInstance
  fintypeCarrier := inferInstance
  backend := AdditiveBackend.ofConstantCosts 1 1 1 0
  keySampler := UniformSampler.ofConstantCost 2

/-- Local additive-operation bounds certified once for the test parameter. -/
noncomputable def testParamEfficiency :
    ParamEfficiencyCertificate testPublicParam where
  additiveBounds := AdditiveCostBounds.ofConstantCosts 1 1 1 0

/-- A fixed native costed OTP family with a three-unit setup path. -/
noncomputable def testFamily : Family :=
  Family.ofFixed testPublicParam 3

/-- Global setup efficiency for `testFamily`. -/
noncomputable def testEfficiency : EfficiencyCertificate testFamily :=
  EfficiencyCertificate.ofFixed testPublicParam 3

/-- The scheme exposes the expected cost-erased encryption distribution. -/
example
    (key message : testPublicParam.Carrier) :
    (scheme testFamily).encryptDist testPublicParam key message =
      PMF.pure (key + message) :=
  scheme_encryptDist testFamily testPublicParam key message

/-- The scheme boundary erases setup costs without changing its distribution. -/
example (sec : Crypto.SecPar) :
    (scheme testFamily).setupDist sec =
      testFamily.setupDist sec :=
  scheme_setupDist testFamily sec

/-- The scheme boundary exposes the intended uniform key distribution. -/
example :
    (scheme testFamily).keygenDist testPublicParam =
      Crypto.Infrastructure.Computation.Distribution.uniformPMF
        testPublicParam.Carrier :=
  scheme_keygenDist testFamily testPublicParam

/-- The scheme boundary erases decryption costs without changing its value. -/
example
    (key ciphertext : testPublicParam.Carrier) :
    (scheme testFamily).decryptValue
        testPublicParam key ciphertext =
      -key + ciphertext :=
  scheme_decryptValue testFamily testPublicParam key ciphertext

/-- Concrete OTP decryption derives its two-unit cost from negation and addition. -/
example
    (key ciphertext : testPublicParam.Carrier) :
    ((scheme testFamily).decrypt
        testPublicParam key ciphertext).cost = 2 :=
  rfl

/-- The native setup path satisfies its separate global efficiency certificate. -/
example :
    Crypto.Infrastructure.Computation.RandomizedComputation.CostBound
      (fun sec (_input : Unit) => testFamily.setup sec)
      (fun _sec => 3) :=
  setup_costBound testFamily testEfficiency

/-- Fixed-parameter encryption exposes the scheme distribution as a timed machine. -/
example
    (sec : Crypto.SecPar)
    (input :
      testPublicParam.Carrier × testPublicParam.Carrier) :
    (encryptTimedMachine
        testPublicParam testParamEfficiency).runDist sec input =
      (scheme testFamily).encryptDist
        testPublicParam input.1 input.2 :=
  encryptTimedMachine_runDist
    testFamily testPublicParam testParamEfficiency sec input

/-- The concrete native costed scheme satisfies the generic correctness interface. -/
example :
    Correct (scheme testFamily) :=
  correct testFamily

end CryptoTest.Primitive.Encryption.SymmetricEncryption.OneTimePad

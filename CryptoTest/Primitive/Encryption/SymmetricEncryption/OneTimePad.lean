import Crypto.Primitive.Encryption.SymmetricEncryption.Instantiations.OneTimePad.Basic
import Mathlib.Data.ZMod.Basic

namespace CryptoTest.Primitive.Encryption.SymmetricEncryption.OneTimePad

open Crypto.Infrastructure.Computation.Algebra
open Crypto.Primitive.Encryption.SymmetricEncryption
open Crypto.Primitive.Encryption.SymmetricEncryption.Instantiations.OneTimePad
open scoped OneTimePadParameter

/-- A concrete two-element OTP parameter with native exact-cost operations. -/
noncomputable def testPublicParam : PublicParam where
  Carrier := ZMod 2
  addGroup := inferInstance
  fintypeCarrier := inferInstance
  nonemptyCarrier := inferInstance
  backend := Backend.ofConstantCosts 1 1
  keySampler := UniformSampler.ofConstantCost 2
  keySamplerLaws := UniformSamplerLaws.ofConstantCost 2

/-- Local sampler and additive-operation bounds for the test parameter. -/
noncomputable def testParamEfficiency :
  ParamEfficiencyCertificate testPublicParam where
  keySamplerBounds := UniformSamplerBounds.ofConstantCost 2
  additiveBounds := BackendBounds.ofConstantCosts 1 1

/-- A fixed native costed OTP family with a three-unit setup path. -/
noncomputable def testFamily : Family :=
  Family.ofFixed testPublicParam 3

/-- Global setup efficiency for `testFamily`. -/
noncomputable def testEfficiency : EfficiencyCertificate testFamily :=
  EfficiencyCertificate.ofFixed testPublicParam 3

/-- The bounded wrapper indexes the same encryption program rather than copying it. -/
example :
    (encryptBoundedProgram testPublicParam testParamEfficiency).program =
      encryptProgram testPublicParam :=
  rfl

/-- One exact encryption call carries the backend's one-unit addition cost. -/
example
    (key message : testPublicParam.Carrier) :
    Crypto.Infrastructure.Computation.Program.runCosted
        (encryptProgram testPublicParam) (key, message) =
      Crypto.Infrastructure.Computation.Cost.RandCosted.liftCosted
        ⟨key + message, 1⟩ :=
  rfl

/-- The structural encryption certificate bounds every exact execution path. -/
example
    (key message : testPublicParam.Carrier)
    (result : Crypto.Infrastructure.Computation.Cost.Costed testPublicParam.Carrier)
    (hresult :
      result ∈
        (Crypto.Infrastructure.Computation.Program.runCosted
          (encryptProgram testPublicParam) (key, message)).support) :
    result.cost ≤ 1 :=
  encryptComputation_costBound
    testPublicParam testParamEfficiency key message result hresult

/-- Key sampling retains its exact two-unit path bound after program interpretation. -/
example
    (result : Crypto.Infrastructure.Computation.Cost.Costed testPublicParam.Carrier)
    (hresult : result ∈ (keygenComputation testPublicParam).support) :
    result.cost ≤ 2 :=
  keygenComputation_costBound
    testPublicParam testParamEfficiency result hresult

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

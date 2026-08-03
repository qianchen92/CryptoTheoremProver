import Crypto.Primitive.Encryption.SymmetricEncryption.Instantiations.OneTimePad.Basic
import Mathlib.Data.ZMod.Basic

namespace CryptoTest.Primitive.Encryption.SymmetricEncryption.OneTimePad

open Crypto.Infrastructure.Computation
open Crypto.Infrastructure.Computation.Algebra
open Crypto.Infrastructure.Computation.Cost
open Crypto.Primitive.Encryption.SymmetricEncryption
open Crypto.Primitive.Encryption.SymmetricEncryption.Instantiations.OneTimePad
open scoped AdditiveGroupParam
open scoped OneTimePadParameter

/-- The finite additive group used by the concrete two-element OTP fixture. -/
noncomputable def testMathematicalParam : MathematicalParam where
  Carrier := ZMod 2
  addGroup := inferInstance
  fintypeCarrier := inferInstance
  nonemptyCarrier := inferInstance

/-- One authoritative exact handler for every primitive used by the test OTP. -/
noncomputable def testAlgebra :
    CostedAlgebra CostModel.nat (signature testMathematicalParam) where
  exec operation :=
    match operation with
    | .sampleKey =>
        RandCostedT.sampleWithCost
          (Crypto.Infrastructure.Computation.Distribution.uniformPMF (ZMod 2))
          (fun _key => 2)
    | .add left right =>
        RandCostedT.liftCosted
          (⟨left + right, 1⟩ : CostedT CostModel.nat (ZMod 2))
    | .neg value =>
        RandCostedT.liftCosted
          (⟨-value, 1⟩ : CostedT CostModel.nat (ZMod 2))

/-- Cost erasure of the exact handler yields only the mathematical operations. -/
noncomputable def testExactLaws : ExactLaws testAlgebra where
  sampleKey := RandCostedT.valueDist_sampleWithCost _ _
  add left right := by
    simp [testAlgebra]
  neg value := by
    simp [testAlgebra]

/-- Independent upper bounds for the exact test handler. -/
noncomputable def testOperationBounds : OperationBounds testAlgebra where
  budget operation :=
    match operation with
    | .sampleKey => 2
    | .add _ _ => 1
    | .neg _ => 1
  cost_le operation result hresult := by
    cases operation with
    | sampleKey =>
        simp only [testAlgebra, RandCostedT.sampleWithCost] at hresult
        rw [PMF.mem_support_map_iff] at hresult
        rcases hresult with ⟨key, _hkey, rfl⟩
        exact Nat.le_refl 2
    | add left right =>
        simp only [testAlgebra, RandCostedT.liftCosted,
          PMF.mem_support_pure_iff] at hresult
        subst result
        exact Nat.le_refl 1
    | neg value =>
        simp only [testAlgebra, RandCostedT.liftCosted,
          PMF.mem_support_pure_iff] at hresult
        subst result
        exact Nat.le_refl 1

/-- A concrete two-element OTP parameter with no backend or sampler wrapper. -/
noncomputable def testPublicParam : PublicParam CostModel.nat where
  toAdditiveGroupParam := testMathematicalParam
  algebra := testAlgebra
  laws := testExactLaws

/-- Uniform primitive budgets, separate from exact execution. -/
noncomputable def testParamEfficiency :
    ParamEfficiencyCertificate testPublicParam where
  bounds := testOperationBounds
  sampleKeyBudget := 2
  sampleKeyBudget_sound := Nat.le_refl 2
  addBudget := 1
  addBudget_sound := fun _left _right => Nat.le_refl 1
  negBudget := 1
  negBudget_sound := fun _value => Nat.le_refl 1

/-- A fixed exact-cost OTP family with a three-unit setup path. -/
noncomputable def testFamily : Family CostModel.nat :=
  Family.ofFixed testPublicParam 3

/-- Global setup efficiency for `testFamily`. -/
noncomputable def testEfficiency : EfficiencyCertificate testFamily :=
  EfficiencyCertificate.ofFixed testPublicParam 3

/-- The bounded wrapper indexes the same encryption program rather than copying it. -/
example :
    (encryptBoundedProgram testPublicParam testParamEfficiency).program =
      encryptProgram testPublicParam :=
  rfl

/-- One exact encryption call carries the algebra's one-unit addition cost. -/
example
    (key message : testPublicParam.Carrier) :
    Program.runCosted (encryptProgram testPublicParam) (key, message) =
      RandCostedT.liftCosted
        (⟨key + message, 1⟩ :
          CostedT CostModel.nat testPublicParam.Carrier) :=
  rfl

/-- The structural encryption certificate bounds every exact execution path. -/
example
    (key message : testPublicParam.Carrier)
    (result : CostedT CostModel.nat testPublicParam.Carrier)
    (hresult :
      result ∈
        (Program.runCosted
          (encryptProgram testPublicParam) (key, message)).support) :
    result.cost ≤ 1 :=
  encryptProgram_costBound testPublicParam testParamEfficiency
    (key, message) result hresult

/-- Key sampling retains its exact two-unit path bound after interpretation. -/
example
    (result : CostedT CostModel.nat testPublicParam.Carrier)
    (hresult :
      result ∈
        (Program.runCosted (keygenProgram testPublicParam) ()).support) :
    result.cost ≤ 2 :=
  keygenProgram_costBound testPublicParam testParamEfficiency () result hresult

/-- The scheme exposes the expected cost-erased encryption distribution. -/
example
    (key message : testPublicParam.Carrier) :
    (scheme testFamily).encryptDist testPublicParam key message =
      PMF.pure (key + message) :=
  scheme_encryptDist testFamily testPublicParam key message

/-- The scheme boundary erases setup costs without changing its distribution. -/
example (sec : Crypto.SecPar) :
    (scheme testFamily).setupDist sec = testFamily.setupDist sec :=
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
    (scheme testFamily).decryptDist testPublicParam key ciphertext =
      PMF.pure (-key + ciphertext) :=
  scheme_decryptDist testFamily testPublicParam key ciphertext

/-- Concrete OTP decryption derives its two-unit cost from negation and addition. -/
example
    (key ciphertext : testPublicParam.Carrier) :
    (scheme testFamily).decrypt testPublicParam key ciphertext =
      RandCostedT.liftCosted
        (⟨-key + ciphertext, 2⟩ :
          CostedT CostModel.nat testPublicParam.Carrier) :=
  by
    simp only [scheme, decryptProgram, Program.runCosted, Program.Code.runCosted,
      testPublicParam, testAlgebra, RandCostedT.bind, RandCostedT.liftCosted,
      CostedT.bind, PMF.pure_bind, PMF.pure_map]
    rfl

/-- The exact setup path satisfies its separate global efficiency certificate. -/
example :
    RandomizedComputationT.CostBound
      (fun sec (_input : Unit) => testFamily.setup sec)
      (fun _sec => 3) :=
  setup_costBound testFamily testEfficiency

/-- Fixed-parameter encryption exposes its distribution after explicit projection. -/
example
    (sec : Crypto.SecPar)
    (input : testPublicParam.Carrier × testPublicParam.Carrier) :
    (encryptTimedMachine NatMeasure.nat
        testPublicParam testParamEfficiency).runDist sec input =
      (scheme testFamily).encryptDist
        testPublicParam input.1 input.2 :=
  encryptTimedMachine_runDist
    NatMeasure.nat testFamily testPublicParam testParamEfficiency sec input

/-- The concrete exact-cost scheme satisfies the generic correctness interface. -/
example : Correct (scheme testFamily) :=
  correct testFamily

end CryptoTest.Primitive.Encryption.SymmetricEncryption.OneTimePad

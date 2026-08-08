import CryptoLib.Test.Assumption.DL.DDH
import CryptoLib.Test.Infrastructure.Computation.TraceCost
import CryptoLib.Instantiation.Primitive.Encryption.AsymmetricEncryption.ElGamal.Basic
import CryptoLib.Core.Infrastructure.Probability.Uniform

namespace CryptoLib.Test.Primitive.Encryption.AsymmetricEncryption.ElGamal

open CryptoLib.Core.Infrastructure.Computation
open CryptoLib.Core.Infrastructure.Computation.Cost
open CryptoLib.Oracle
open CryptoLib.Oracle.Complexity
open CryptoLib.Core.Infrastructure.Asymptotic
open CryptoLib.Core.Infrastructure.Complexity
open CryptoLib.Primitive.Encryption.AsymmetricEncryption
open CryptoLib.Instantiation.Primitive.Encryption.AsymmetricEncryption.ElGamal
open CryptoLib.Program.Adapter.OneShotChoiceAdd
open CryptoLib.Test.Assumption.DL
open scoped DDHParameter

/-- A concrete polynomial certificate for exercising the closed reduction. -/
noncomputable def testReductionEfficiency :
    ReductionEfficiencyCertificate NatMeasure.nat DDH.testFamily where
  prepareCost := 1
  rejectCost := 2
  queryPrefixCost := 3
  querySuffixCost := 4
  repeatQueryCost := 5
  prepareRuntime := fun _sec => 1
  rejectRuntime := fun _sec => 2
  addRuntime := fun _sec => 5
  queryRuntime := fun _sec => 12
  queryBudget := fun _sec => 12
  prepareCost_le_runtime := by intro sec; rfl
  rejectCost_le_runtime := by intro sec; rfl
  addBudget_le_runtime := by intro sec; rfl
  firstQuery_le_budget := by
    intro parameter
    change (3 + (5 + (4 + 0)) : Nat) ≤ 12
    clear parameter
    decide
  repeatQuery_le_budget := by intro sec; decide
  queryBudget_le_runtime := by intro sec; rfl
  prepareRuntime_isPoly := IsPolyBounded.const 1
  rejectRuntime_isPoly := IsPolyBounded.const 2
  addRuntime_isPoly := IsPolyBounded.const 5
  queryRuntime_isPoly := IsPolyBounded.const 12
  repeatBudgetMono := by
    intro sec first second hle
    exact Oracle.Program.repeatCost_nat_mono 12 hle
  exchange := Oracle.Program.costExchange_nat

/-- The first challenge query with `b = false` selects the left message. -/
example
    (parameter : CryptoLib.Core.SecPar)
    (right shared leftMessage rightMessage : ZMod 2) :
    CryptoLib.Program.Procedure.runCosted
        (algebra (reductionAdapter DDH.testFamily testReductionEfficiency))
        (queryProgram CryptoLib.Core.SecPar (ZMod 2) false)
        (queryInputValue parameter right shared false leftMessage rightMessage) =
      RandCosted.liftCosted
        (⟨(some (ULift.up right, ULift.up (leftMessage + shared)), ULift.up true),
            12⟩ : Costed CostModel.nat _) := by
  rw [runCosted_query_fresh]
  rfl

/-- The first challenge query with `b = true` selects the right message. -/
example
    (parameter : CryptoLib.Core.SecPar)
    (right shared leftMessage rightMessage : ZMod 2) :
    CryptoLib.Program.Procedure.runCosted
        (algebra (reductionAdapter DDH.testFamily testReductionEfficiency))
        (queryProgram CryptoLib.Core.SecPar (ZMod 2) true)
        (queryInputValue parameter right shared false leftMessage rightMessage) =
      RandCosted.liftCosted
        (⟨(some (ULift.up right, ULift.up (rightMessage + shared)), ULift.up true),
            12⟩ : Costed CostModel.nat _) := by
  rw [runCosted_query_fresh]
  rfl

/-- Every query after the first returns `none` and charges only the repeat path. -/
example
    (parameter : CryptoLib.Core.SecPar)
    (right shared leftMessage rightMessage : ZMod 2) :
    CryptoLib.Program.Procedure.runCosted
        (algebra (reductionAdapter DDH.testFamily testReductionEfficiency))
        (queryProgram CryptoLib.Core.SecPar (ZMod 2) false)
        (queryInputValue parameter right shared true leftMessage rightMessage) =
      RandCosted.liftCosted
        (⟨(none, ULift.up true), 5⟩ : Costed CostModel.nat _) := by
  rw [runCosted_query_used]
  rfl

/-- An adversary that makes no challenge query and performs no local work. -/
noncomputable def noQueryAdversary :
    OracleMachine CostModel.nat
      (PublicInput CryptoLib.Core.SecPar (PublicKey (Carrier := ZMod 2)))
      (fun _sec _input => Bool)
      (indCPAOracleSpec
        (Message (Carrier := ZMod 2)) (Ciphertext (Carrier := ZMod 2))) where
  issueCost := fun _sec _input _name _query => 0
  program := fun _sec _input => pure (ULift.up false)

/-- The ElGamal security proof uses four games and therefore three hops. -/
example : (gameSequence DDH.testFamily noQueryAdversary).length = 3 :=
  rfl

/-- `G₀` is definitionally the real IND-CPA game. -/
example :
    G₀ DDH.testFamily noQueryAdversary =
      indCPASecurityGame (scheme DDH.testFamily) noQueryAdversary false :=
  rfl

/-- `G₁` is definitionally the random IND-CPA game. -/
example :
    G₁ DDH.testFamily noQueryAdversary =
      indCPASecurityGame (scheme DDH.testFamily) noQueryAdversary true :=
  rfl

/-- The first intermediate game is `G₀`. -/
example :
    (gameSequence DDH.testFamily noQueryAdversary).securityGame
        (1 : Fin 4) =
      G₀ DDH.testFamily noQueryAdversary :=
  rfl

/-- The second intermediate game is `G₁`. -/
example :
    (gameSequence DDH.testFamily noQueryAdversary).securityGame
        (2 : Fin 4) =
      G₁ DDH.testFamily noQueryAdversary :=
  rfl

@[simp] theorem noQueryAdversary_runCosted
    (sec : CryptoLib.Core.SecPar)
    (input : PublicInput CryptoLib.Core.SecPar (PublicKey (Carrier := ZMod 2)) sec)
    (env : CostedOracleEnv CostModel.nat
      (indCPAOracleSpec
        (Message (Carrier := ZMod 2)) (Ciphertext (Carrier := ZMod 2))
        sec input)) :
    noQueryAdversary.runCosted sec input env =
      RandCosted.liftCosted
        (⟨false, 0⟩ : Costed CostModel.nat Bool) := by
  unfold OracleMachine.runCosted
  simp only [noQueryAdversary, Oracle.Program.runCosted,
    Oracle.Program.runExactFromInit, Oracle.Program.runExact]
  rw [PMF.pure_map]
  change PMF.map _ (PMF.pure _) = PMF.pure _
  rw [PMF.pure_map]
  rfl

def validReductionChallenge :
    CryptoLib.Assumption.DL.DDH.ChallengeInput DDH.testFamily where
  parameter := 7
  left := 0
  right := 1
  shared := 1

def invalidReductionChallenge :
    CryptoLib.Assumption.DL.DDH.ChallengeInput DDH.testFamily where
  parameter := 8
  left := 0
  right := 1
  shared := 1

/-- With zero oracle queries, the valid branch charges prepare and nothing else. -/
example :
    (concreteDDHReduction DDH.testFamily testReductionEfficiency
        noQueryAdversary false).run 7 validReductionChallenge =
      RandCosted.liftCosted
        (⟨false, 1⟩ : Costed CostModel.nat Bool) := by
  have htag : DDH.testFamily.parameterSec
      validReductionChallenge.parameter = 7 := by
    rfl
  simp only [concreteDDHReduction, htag, if_true,
    reductionPrepare_eq_liftCosted, noQueryAdversary_runCosted]
  rw [RandCosted.liftCosted_bind_liftCosted]
  rfl

/-- A mismatched setup tag takes the charged reject branch before the adversary. -/
example :
    (concreteDDHReduction DDH.testFamily testReductionEfficiency
        noQueryAdversary true).run 7 invalidReductionChallenge =
      RandCosted.liftCosted
        (⟨false, 2⟩ : Costed CostModel.nat Bool) := by
  have htag : DDH.testFamily.parameterSec
      invalidReductionChallenge.parameter ≠ 7 := by
    change 8 ≠ 7
    decide
  simp only [concreteDDHReduction, htag, if_false,
    reductionReject_eq_liftCosted]
  rfl

/-! ## Noncommutative reduction-order regression -/

inductive ReductionTraceEvent where
  | prepare
  | adversaryLocal
  | queryPrefix
  | groupAdd
  | querySuffix
  | repeatQuery
  | reject
deriving DecidableEq, Repr

abbrev ReductionTraceCost :=
  CryptoLib.Test.Infrastructure.Computation.TraceCost ReductionTraceEvent

abbrev reductionTraceCostModel :=
  CryptoLib.Test.Infrastructure.Computation.TraceCost.costModel
    ReductionTraceEvent

def reductionTraceCost (event : ReductionTraceEvent) : ReductionTraceCost :=
  CryptoLib.Test.Infrastructure.Computation.TraceCost.singleton event

def reductionTraceMeasure : NatMeasure reductionTraceCostModel :=
  CryptoLib.Test.Infrastructure.Computation.TraceCost.lengthMeasure
    ReductionTraceEvent

inductive ReductionTraceOracle where
  | challenge
deriving DecidableEq

def reductionTraceOracleSpec : OracleSpec where
  Name := ReductionTraceOracle
  Query
    | .challenge => Bool × Bool
  Response
    | .challenge => Option (Bool × Bool)

def reductionTraceCosts : Costs reductionTraceCostModel Unit where
  prepare := reductionTraceCost .prepare
  reject := reductionTraceCost .reject
  queryPrefix := reductionTraceCost .queryPrefix
  querySuffix := reductionTraceCost .querySuffix
  repeatQuery := reductionTraceCost .repeatQuery
  add := fun _parameter => reductionTraceCost .groupAdd

def reductionTraceAdapter : Adapter reductionTraceCostModel Unit Bool where
  add := fun _parameter _left _right => false
  costs := reductionTraceCosts

/-- A sealed adapter fixture whose runtime bounds observe trace length only. -/
noncomputable def reductionTraceOperationalAdapter (rightMessage : Bool) :
    FirstOrderOracleAdapter reductionTraceCostModel reductionTraceMeasure
      (fun _sec => Unit) (fun _sec => Unit) (fun _sec => Bool)
      (fun _sec _input => reductionTraceOracleSpec)
      (interpret Unit Bool) (algebra reductionTraceAdapter)
      (PrepareInputTy Unit Bool) (PrepareOutputTy Unit Bool)
      .unit .bool (QueryInputTy Unit Bool) (QueryOutputTy Unit Bool) where
  algebraValid := algebra_valid reductionTraceAdapter
  accepted := fun _sec _input => True
  acceptedDecidable := fun _sec _input => inferInstance
  prepareProgram := prepareProgram Unit Bool
  rejectProgram := rejectProgram Unit Bool
  queryProgram := queryProgram Unit Bool rightMessage
  prepareBudget := prepareBudget reductionTraceAdapter
  rejectBudget := rejectBudget reductionTraceAdapter
  queryBudget := queryExactBudget reductionTraceAdapter
  prepareCostBound := prepare_costBound reductionTraceAdapter
  rejectCostBound := reject_costBound reductionTraceAdapter
  queryCostBound := query_costBound reductionTraceAdapter rightMessage
  prepareInput := fun _sec _input => prepareInputValue () false
  prepareOutput := fun _sec _input _prepared => ()
  rejectInput := fun _sec _input => ULift.up ()
  rejectOutput := fun _sec _input rejected => rejected.down
  State := Bool
  init := fun _sec _input _callerInput => false
  queryInput := fun _sec _input _callerInput name _querySec used query => by
    cases name
    exact queryInputValue () false false used query.1 query.2
  queryOutput := fun _sec _input _callerInput name output => by
    cases name
    exact
      (output.1.map (fun ciphertext =>
        (ciphertext.1.down, ciphertext.2.down)), output.2.down)
  prepareRuntime := fun _sec => 1
  rejectRuntime := fun _sec => 1
  queryRuntime := fun _sec => 3
  prepareBudget_le_runtime := by intro sec input; rfl
  rejectBudget_le_runtime := by intro sec input; rfl
  queryBudget_le_runtime := by
    intro sec input callerInput name querySec state query _accepted
    cases name
    cases state with
    | false =>
        change 3 ≤ 3
        exact Nat.le_refl 3
    | true =>
        change 1 ≤ 3
        decide

noncomputable def reductionTraceIssueCost :
    (name : reductionTraceOracleSpec.Name) →
      reductionTraceOracleSpec.Query name → reductionTraceCostModel.Cost :=
  fun name _query =>
    match name with
    | .challenge => reductionTraceCost .adversaryLocal

/-- One admitted-caller-shaped program issuing exactly one challenge query. -/
noncomputable def reductionTraceCaller :
    OracleMachine reductionTraceCostModel
      (fun _sec => Unit) (fun _sec _input => Bool)
      (fun _sec _input => reductionTraceOracleSpec) where
  issueCost := fun _sec _input => reductionTraceIssueCost
  program := fun _sec _input => do
    let response ← Oracle.Program.query ReductionTraceOracle.challenge
      (false, true)
    pure (ULift.up response.down.isSome)

/--
The exact closed execution preserves the intended noncommutative order:
prepare, caller-local issue, query prefix, group addition, query suffix.
-/
example :
    (reductionTraceOperationalAdapter false).close reductionTraceCaller 0 () =
      RandCosted.liftCosted
        (⟨true,
          ⟨[.prepare, .adversaryLocal, .queryPrefix, .groupAdd, .querySuffix]⟩⟩ :
          Costed reductionTraceCostModel Bool) := by
  simp only [FirstOrderOracleAdapter.close, reductionTraceAdapter,
    reductionTraceCosts, reductionTraceCost, reductionTraceOperationalAdapter,
    ↓reduceIte, FirstOrderOracleAdapter.runPrepare, runCosted_prepare,
    OracleMachine.runCosted, Oracle.Program.runCosted,
    FirstOrderOracleAdapter.oracleEnv, Oracle.Program.runExactFromInit,
    reductionTraceCaller, reductionTraceIssueCost,
    Oracle.Program.runExact, runCosted_query_fresh, Costs.firstQuery,
    PMF.bind_map, PMF.pure_bind, Function.comp_apply, Costed.map_val,
    Option.map_some, Costed.map_cost, add_zero, Option.isSome_some]
  change PMF.map _ (PMF.map _ (PMF.map _ (PMF.pure _))) = PMF.pure _
  rw [PMF.pure_map, PMF.pure_map, PMF.pure_map]
  rfl

/-- The trace model distinguishes the execution order from a regrouped one. -/
example :
    (⟨[.prepare, .adversaryLocal, .queryPrefix, .groupAdd, .querySuffix]⟩ :
      ReductionTraceCost) ≠
      ⟨[.prepare, .queryPrefix, .groupAdd, .querySuffix, .adversaryLocal]⟩ := by
  decide

/-- The public efficiency lemma exposes polynomial runtime closure. -/
example
    (adversary : PPTOracleMachine CostModel.nat NatMeasure.nat
      (PublicInput CryptoLib.Core.SecPar (PublicKey (Carrier := ZMod 2)))
      (fun _sec _input => Bool)
      (indCPAOracleSpec
        (Message (Carrier := ZMod 2)) (Ciphertext (Carrier := ZMod 2)))) :
    IsPolyBounded
      (concreteReductionRuntime testReductionEfficiency
        adversary.toTimedOracleMachine) := by
  exact concreteReductionRuntime_isPoly DDH.testFamily
    testReductionEfficiency adversary

/-- The public closure lemma is obtained from explicit efficiency data. -/
example : DDHReductionPPTClosed NatMeasure.nat DDH.testFamily := by
  exact ddhReductionPPTClosed DDH.testFamily testReductionEfficiency

/-- The controlled compiler supplies closed PPT admission without a new premise. -/
example
    (adversary : PPTOracleMachine CostModel.nat NatMeasure.nat
      (PublicInput CryptoLib.Core.SecPar (PublicKey (Carrier := ZMod 2)))
      (fun _sec _input => Bool)
      (indCPAOracleSpec
        (Message (Carrier := ZMod 2)) (Ciphertext (Carrier := ZMod 2))))
    (rightMessage : Bool) :
    Nonempty
      (PPTMachine CostModel.nat NatMeasure.nat
        (fun _sec => CryptoLib.Assumption.DL.DDH.ChallengeInput DDH.testFamily)
        (fun _sec _challenge => Bool)) :=
  ⟨concreteDDHReductionPPT DDH.testFamily testReductionEfficiency
    adversary rightMessage⟩

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
      (Language.CarrierValue DDH.testPublicParam ×
        Language.CarrierValue DDH.testPublicParam))
    (hresult : result ∈
      (CryptoLib.Program.Procedure.runCosted
        (Language.algebra DDH.testPublicParam)
        (encryptProgram DDH.testPublicParam)
        (Language.liftCarrier DDH.testPublicParam publicKey,
          Language.liftCarrier DDH.testPublicParam message)).support) :
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
example (sec : CryptoLib.Core.SecPar) :
    (scheme DDH.testFamily).setupDist sec =
      DDH.testFamily.setupDist sec :=
  scheme_setupDist DDH.testFamily sec

/-- Setup is the authoritative family computation path-for-path. -/
example (sec : CryptoLib.Core.SecPar) :
    (scheme DDH.testFamily).setup sec = DDH.testFamily.setup sec :=
  scheme_setup_eq_family_setup DDH.testFamily sec

/-- The scheme boundary exposes ordinary ElGamal key generation. -/
example (sec : CryptoLib.Core.SecPar) :
    (scheme DDH.testFamily).keygenDist sec =
      PMF.bind
        (CryptoLib.Core.Infrastructure.Probability.uniformPMF
          DDH.testPublicParam.Scalar)
        (fun secretKey =>
          PMF.pure
            (secretKey • DDH.testPublicParam.generator, secretKey)) :=
  scheme_keygenDist DDH.testFamily sec

/-- Cost erasure of decryption gives the ordinary ElGamal plaintext. -/
example
    (secretKey : DDH.testPublicParam.Scalar)
    (ciphertext :
      DDH.testPublicParam.Carrier × DDH.testPublicParam.Carrier) :
    (scheme DDH.testFamily).decryptDist
        0 secretKey ciphertext =
      PMF.pure (ciphertext.2 - secretKey • ciphertext.1) :=
  scheme_decryptDist DDH.testFamily 0 secretKey ciphertext

/-- Concrete decryption has exact scalar-action-plus-subtraction cost. -/
example
    (secretKey : DDH.testPublicParam.Scalar)
    (ciphertext :
      DDH.testPublicParam.Carrier × DDH.testPublicParam.Carrier) :
    CryptoLib.Program.Procedure.runCosted
        (Language.algebra DDH.testPublicParam)
        (decryptProgram DDH.testPublicParam)
        (Language.liftScalar DDH.testPublicParam secretKey,
          (Language.liftCarrier DDH.testPublicParam ciphertext.1,
            Language.liftCarrier DDH.testPublicParam ciphertext.2)) =
      PMF.pure
        (⟨ULift.up (ciphertext.2 - secretKey • ciphertext.1), 17⟩ :
          Costed CostModel.nat (ULift DDH.testPublicParam.Carrier)) := by
  change
    CryptoLib.Program.Procedure.runCosted
        (Language.algebra DDH.testPublicParam)
        (decryptProgram DDH.testPublicParam)
        (Language.liftScalar DDH.testPublicParam secretKey,
          (Language.liftCarrier DDH.testPublicParam ciphertext.1,
            Language.liftCarrier DDH.testPublicParam ciphertext.2)) =
      PMF.pure
        (⟨ULift.up
            (DDH.testMath.addGroup.sub ciphertext.2
              (DDH.testMath.smul.smul secretKey ciphertext.1)), 17⟩ :
          Costed CostModel.nat (ULift DDH.testMath.Carrier))
  simp only [DDH.testPublicParam, DDH.testAlgebra,
    RandCosted.liftCosted, CryptoLib.Program.Procedure.runCosted,
    Language.algebra, decryptProgram, CryptoLib.Program.Builder.SmartCode.smul,
    CryptoLib.Program.Builder.SmartCode.sub, CryptoLib.Program.SmartOperation.smul,
    CryptoLib.Program.SmartOperation.sub, CryptoLib.Program.Signature.inject,
    CryptoLib.Program.Signature.Embedding.inject, CryptoLib.Program.Code.runCosted,
    RandCosted.bind, CryptoLib.Program.Expr.eval, CryptoLib.Program.Env.get,
    Costed.bind, RandCosted.pure, Costed.pure, PMF.pure_map]
  refine (PMF.pure_bind _ _).trans ?_
  change
    PMF.map
        (fun second : Costed CostModel.nat
            (Language.CarrierValue DDH.testPublicParam) =>
          (⟨second.val, 11 + second.cost⟩ :
            Costed CostModel.nat
              (Language.CarrierValue DDH.testPublicParam)))
        ((PMF.pure
            (⟨ULift.up
                (ciphertext.2 - secretKey • ciphertext.1), 6⟩ :
              Costed CostModel.nat
                (Language.CarrierValue DDH.testPublicParam))).bind
          (fun first => PMF.pure
            (⟨first.val, first.cost⟩ :
              Costed CostModel.nat
                (Language.CarrierValue DDH.testPublicParam)))) =
      PMF.pure
        (⟨ULift.up (ciphertext.2 - secretKey • ciphertext.1), 17⟩ :
          Costed CostModel.nat
            (Language.CarrierValue DDH.testPublicParam))
  have inner :
      (PMF.pure
        (⟨ULift.up (ciphertext.2 - secretKey • ciphertext.1), 6⟩ :
          Costed CostModel.nat
            (Language.CarrierValue DDH.testPublicParam))).bind
          (fun first => PMF.pure
            (⟨first.val, first.cost⟩ :
              Costed CostModel.nat
                (Language.CarrierValue DDH.testPublicParam))) =
        PMF.pure
          (⟨ULift.up (ciphertext.2 - secretKey • ciphertext.1), 6⟩ :
            Costed CostModel.nat
              (Language.CarrierValue DDH.testPublicParam)) :=
    PMF.pure_bind _ _
  rw [inner, PMF.pure_map]
  rfl

/-- The timed adapter preserves the ordinary ElGamal encryption distribution. -/
example
    (sec : CryptoLib.Core.SecPar)
    (input :
      DDH.testPublicParam.Carrier × DDH.testPublicParam.Carrier) :
    (encryptTimedMachine NatMeasure.nat
        DDH.testPublicParam DDH.testParamEfficiency).runDist sec input =
      (scheme DDH.testFamily).encryptDist
        sec input.1 input.2 :=
  encryptTimedMachine_runDist NatMeasure.nat
    DDH.testFamily sec DDH.testParamEfficiency sec input

/-- The cost-aware scheme retains the generic correctness theorem. -/
example :
    Correct (scheme DDH.testFamily) :=
  correct DDH.testFamily

end CryptoLib.Test.Primitive.Encryption.AsymmetricEncryption.ElGamal

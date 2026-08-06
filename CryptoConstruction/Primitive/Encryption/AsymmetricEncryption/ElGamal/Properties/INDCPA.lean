import Crypto.Infrastructure.GameBased.Hybrid
import Crypto.Infrastructure.Computation.Oracle.DeferredSampling
import CryptoFirstOrder.Adapter.OneShotChoiceAdd
import CryptoConstruction.Primitive.Encryption.AsymmetricEncryption.ElGamal.Properties.Semantics
import Crypto.Primitive.Encryption.AsymmetricEncryption.Properties.INDCPA

namespace CryptoConstruction.Primitive.Encryption.AsymmetricEncryption.ElGamal

open Crypto.Infrastructure.Computation.Cost
open Crypto.Infrastructure.Computation
open Crypto.Infrastructure.Computation.Oracle
open Crypto.Primitive.Encryption.AsymmetricEncryption
open CryptoFirstOrder.Adapter.OneShotChoiceAdd
open scoped DDHParameter

universe uCost uParameter uScalar uGroup

variable
    {M : CostModel.{uCost}}
    {measure : NatMeasure M}
    {Parameter : Type uParameter}
    {Scalar : Type uScalar}
    {Carrier : Type uGroup}

/-- The public ElGamal input exposed by one DDH challenge. -/
def reductionPublicInput
    (F : Family M Parameter Scalar Carrier)
    (sec : Crypto.SecPar)
    (challenge : Crypto.Assumption.DL.DDH.ChallengeInput F) :
    PublicInput Parameter (PublicKey (Carrier := Carrier)) sec where
  param := challenge.parameter
  publicKey := challenge.left

/--
Answer the single IND-CPA challenge from a DDH tuple. In the real DDH game the
answer is a genuine ElGamal encryption; in the random game the second component
is one-time padded by the independent random DDH component.
-/
noncomputable def reductionOracle
    (F : Family M Parameter Scalar Carrier)
    (sec : Crypto.SecPar)
    (challenge : Crypto.Assumption.DL.DDH.ChallengeInput F)
    (rightMessage : Bool) :
    OracleEnv
      (indCPAOracleSpec
        (Message (Carrier := Carrier)) (Ciphertext (Carrier := Carrier)) sec
        (reductionPublicInput F sec challenge)) where
  State := Bool
  init := false
  query
    | INDCPAOracle.challenge, _querySec, used, query =>
        if used then
          PMF.pure ((none : ChallengeResponse (Carrier × Carrier)), true)
        else
          let message : Carrier :=
            if rightMessage then query.2 else query.1
          let pp := F.publicParam challenge.parameter
          PMF.pure
            ((some (challenge.right, pp.addGroup.add message challenge.shared) :
              ChallengeResponse (Carrier × Carrier)), true)

/--
Explicit resource data for compiling the closed DDH reduction.  Structural
charges are fixed costs; the parameter-dependent group addition is bounded by
the family's `addBudget` at the parameter's security tag.
-/
structure ReductionEfficiencyCertificate
    (measure : NatMeasure M)
    (F : Family M Parameter Scalar Carrier) where
  prepareCost : M.Cost
  rejectCost : M.Cost
  queryPrefixCost : M.Cost
  querySuffixCost : M.Cost
  repeatQueryCost : M.Cost
  prepareRuntime : Crypto.SecPar → Nat
  rejectRuntime : Crypto.SecPar → Nat
  addRuntime : Crypto.SecPar → Nat
  queryRuntime : Crypto.SecPar → Nat
  queryBudget : Crypto.SecPar → M.Cost
  prepareCost_le_runtime : ∀ sec,
    measure (M.instAddMonoid.add prepareCost M.instAddMonoid.zero) ≤
      prepareRuntime sec
  rejectCost_le_runtime : ∀ sec,
    measure (M.instAddMonoid.add rejectCost M.instAddMonoid.zero) ≤
      rejectRuntime sec
  addBudget_le_runtime : ∀ sec,
    measure (F.addBudget sec) ≤ addRuntime sec
  firstQuery_le_budget : ∀ parameter,
    M.instPartialOrder.le
      (M.instAddMonoid.add queryPrefixCost
        (M.instAddMonoid.add (F.addCost parameter)
          (M.instAddMonoid.add querySuffixCost M.instAddMonoid.zero)))
      (queryBudget (F.parameterSec parameter))
  repeatQuery_le_budget : ∀ sec,
    M.instPartialOrder.le
      (M.instAddMonoid.add repeatQueryCost M.instAddMonoid.zero)
      (queryBudget sec)
  queryBudget_le_runtime : ∀ sec,
    measure (queryBudget sec) ≤ queryRuntime sec
  prepareRuntime_isPoly :
    Crypto.Infrastructure.Asymptotic.IsPolyBounded prepareRuntime
  rejectRuntime_isPoly :
    Crypto.Infrastructure.Asymptotic.IsPolyBounded rejectRuntime
  addRuntime_isPoly :
    Crypto.Infrastructure.Asymptotic.IsPolyBounded addRuntime
  queryRuntime_isPoly :
    Crypto.Infrastructure.Asymptotic.IsPolyBounded queryRuntime
  repeatBudgetMono : ∀ sec {first second : Nat}, first ≤ second →
    M.instPartialOrder.le
      (Oracle.Program.repeatCost M first (queryBudget sec))
      (Oracle.Program.repeatCost M second (queryBudget sec))
  exchange : Oracle.Program.CostExchange M

/-- The unique exact primitive algebra used by the executable reduction. -/
noncomputable def reductionAdapter
    (F : Family M Parameter Scalar Carrier)
    (efficiency : ReductionEfficiencyCertificate measure F) :
    Adapter M Parameter Carrier where
  add parameter := (F.publicParam parameter).addGroup.add
  costs :=
    { prepare := efficiency.prepareCost
      reject := efficiency.rejectCost
      queryPrefix := efficiency.queryPrefixCost
      querySuffix := efficiency.querySuffixCost
      repeatQuery := efficiency.repeatQueryCost
      add := F.addCost }

/-- Execute the adapter's represented prepare program and project its record. -/
noncomputable def reductionPrepare
    (F : Family M Parameter Scalar Carrier)
    (efficiency : ReductionEfficiencyCertificate measure F)
    (sec : Crypto.SecPar)
    (challenge : Crypto.Assumption.DL.DDH.ChallengeInput F) :
    RandCosted M
      (PublicInput Parameter (PublicKey (Carrier := Carrier)) sec) :=
  RandCosted.map
    (fun prepared =>
      { param := prepared.1.down
        publicKey := prepared.2.down })
    (CryptoFirstOrder.Program.runCosted (algebra (reductionAdapter F efficiency))
      (prepareProgram Parameter Carrier)
      (prepareInputValue challenge.parameter challenge.left))

/-- Execute the adapter's explicitly charged malformed-tag branch. -/
noncomputable def reductionReject
    (F : Family M Parameter Scalar Carrier)
    (efficiency : ReductionEfficiencyCertificate measure F) :
    RandCosted M Bool :=
  RandCosted.map ULift.down
    (CryptoFirstOrder.Program.runCosted (algebra (reductionAdapter F efficiency))
      (rejectProgram Parameter Carrier) (ULift.up ()))

/-- Exact one-shot challenge implementation backed by the query `Code`. -/
noncomputable def costedReductionOracle
    (F : Family M Parameter Scalar Carrier)
    (efficiency : ReductionEfficiencyCertificate measure F)
    (sec : Crypto.SecPar)
    (challenge : Crypto.Assumption.DL.DDH.ChallengeInput F)
    (rightMessage : Bool) :
    CostedOracleEnv M
      (indCPAOracleSpec
        (Message (Carrier := Carrier)) (Ciphertext (Carrier := Carrier)) sec
        (reductionPublicInput F sec challenge)) where
  State := Bool
  init := false
  query
    | INDCPAOracle.challenge, _querySec, used, query =>
        RandCosted.map
          (fun output =>
            (output.1.map (fun ciphertext =>
              (ciphertext.1.down, ciphertext.2.down)), output.2.down))
          (CryptoFirstOrder.Program.runCosted
            (algebra (reductionAdapter F efficiency))
            (queryProgram Parameter Carrier rightMessage)
            (queryInputValue challenge.parameter challenge.right
              challenge.shared used query.1 query.2))

/--
The executable reduction.  A valid tag executes prepare, the admitted caller,
and the exact query adapter in order; a malformed tag executes only reject.
-/
noncomputable def concreteDDHReduction
    (F : Family M Parameter Scalar Carrier)
    (efficiency : ReductionEfficiencyCertificate measure F)
    (adversary : Crypto.Infrastructure.Complexity.OracleMachine M
      (PublicInput Parameter (PublicKey (Carrier := Carrier)))
      (fun _sec _input => Bool)
      (indCPAOracleSpec
        (Message (Carrier := Carrier)) (Ciphertext (Carrier := Carrier))))
    (rightMessage : Bool) :
    Crypto.Infrastructure.Complexity.ProbabilisticMachine M
      (fun _sec => Crypto.Assumption.DL.DDH.ChallengeInput F)
      (fun _sec _challenge => Bool) where
  run := fun sec challenge =>
    if F.parameterSec challenge.parameter = sec then
      RandCosted.bind (reductionPrepare F efficiency sec challenge) fun prepared =>
        adversary.runCosted sec prepared
          (costedReductionOracle F efficiency sec challenge rightMessage)
    else
      reductionReject F efficiency

@[simp] theorem reductionPrepare_eq_liftCosted
    (F : Family M Parameter Scalar Carrier)
    (efficiency : ReductionEfficiencyCertificate measure F)
    (sec : Crypto.SecPar)
    (challenge : Crypto.Assumption.DL.DDH.ChallengeInput F) :
    reductionPrepare F efficiency sec challenge =
      RandCosted.liftCosted
        (⟨reductionPublicInput F sec challenge,
            M.instAddMonoid.add efficiency.prepareCost M.instAddMonoid.zero⟩ :
          Costed M _) := by
  unfold reductionPrepare
  rw [runCosted_prepare]
  unfold RandCosted.map RandCosted.liftCosted
  rw [PMF.pure_map]
  rfl

@[simp] theorem reductionReject_eq_liftCosted
    (F : Family M Parameter Scalar Carrier)
    (efficiency : ReductionEfficiencyCertificate measure F) :
    reductionReject F efficiency =
      RandCosted.liftCosted
        (⟨false,
            M.instAddMonoid.add efficiency.rejectCost M.instAddMonoid.zero⟩ :
          Costed M Bool) := by
  unfold reductionReject
  rw [runCosted_reject]
  unfold RandCosted.map RandCosted.liftCosted
  exact PMF.pure_map (Costed.map ULift.down)
    (⟨ULift.up false,
        M.instAddMonoid.add efficiency.rejectCost M.instAddMonoid.zero⟩ :
      Costed M (ULift Bool))

@[simp] theorem valueDist_reductionPrepare
    (F : Family M Parameter Scalar Carrier)
    (efficiency : ReductionEfficiencyCertificate measure F)
    (sec : Crypto.SecPar)
    (challenge : Crypto.Assumption.DL.DDH.ChallengeInput F) :
    RandCosted.valueDist (reductionPrepare F efficiency sec challenge) =
      PMF.pure (reductionPublicInput F sec challenge) := by
  unfold reductionPrepare
  rw [RandCosted.valueDist_map, runCosted_prepare]
  rw [RandCosted.valueDist_liftCosted, PMF.pure_map]
  rfl

@[simp] theorem valueDist_reductionReject
    (F : Family M Parameter Scalar Carrier)
    (efficiency : ReductionEfficiencyCertificate measure F) :
    RandCosted.valueDist (reductionReject F efficiency) =
      PMF.pure false := by
  unfold reductionReject
  rw [RandCosted.valueDist_map, runCosted_reject]
  change PMF.map ULift.down
      (RandCosted.valueDist
        (RandCosted.liftCosted
          (⟨ULift.up false,
              M.instAddMonoid.add efficiency.rejectCost M.instAddMonoid.zero⟩ :
            Costed M (ULift Bool)))) = PMF.pure false
  rw [RandCosted.valueDist_liftCosted]
  change PMF.map ULift.down (PMF.pure (ULift.up false)) = PMF.pure false
  exact PMF.pure_map (f := ULift.down) (ULift.up false)

/-- Cost erasure of the executable query code is the semantic oracle exactly. -/
@[simp] theorem erase_costedReductionOracle
    (F : Family M Parameter Scalar Carrier)
    (efficiency : ReductionEfficiencyCertificate measure F)
    (sec : Crypto.SecPar)
    (challenge : Crypto.Assumption.DL.DDH.ChallengeInput F)
    (rightMessage : Bool) :
    (costedReductionOracle F efficiency sec challenge rightMessage).erase =
      reductionOracle F sec challenge rightMessage := by
  let pp := F.publicParam challenge.parameter
  letI : AddGroup Carrier := pp.addGroup
  dsimp [costedReductionOracle, reductionOracle, CostedOracleEnv.erase]
  congr
  funext name querySec used query
  cases name
  cases used <;> cases rightMessage <;>
    simp [reductionAdapter, PMF.pure_map]

theorem costedReductionOracle_queryCostBoundAt
    (F : Family M Parameter Scalar Carrier)
    (efficiency : ReductionEfficiencyCertificate measure F)
    (sec : Crypto.SecPar)
    (challenge : Crypto.Assumption.DL.DDH.ChallengeInput F)
    (rightMessage : Bool)
    (htag : F.parameterSec challenge.parameter = sec) :
    (costedReductionOracle F efficiency sec challenge rightMessage).QueryCostBoundAt
      sec (efficiency.queryBudget sec) := by
  intro name state query result hresult
  cases name
  change Bool at state
  change Costed M (Option (Carrier × Carrier) × Bool) at result
  change result ∈
    (RandCosted.map
      (fun output =>
        (output.1.map (fun ciphertext =>
          (ciphertext.1.down, ciphertext.2.down)), output.2.down))
      (CryptoFirstOrder.Program.runCosted
        (algebra (reductionAdapter F efficiency))
        (queryProgram Parameter Carrier rightMessage)
        (queryInputValue challenge.parameter challenge.right challenge.shared
          state query.1 query.2))).support at hresult
  simp only [RandCosted.map] at hresult
  rw [PMF.mem_support_map_iff] at hresult
  rcases hresult with ⟨source, hsource, hresult⟩
  subst result
  have hexact := query_costBound (reductionAdapter F efficiency) rightMessage
    (queryInputValue challenge.parameter challenge.right challenge.shared
      state query.1 query.2) source hsource
  change M.instPartialOrder.le source.cost (efficiency.queryBudget sec)
  cases state with
  | false =>
      exact M.instPartialOrder.le_trans _ _ _ hexact (by
          simpa only [queryExactBudget, Bool.false_eq_true, ↓reduceIte,
            reductionAdapter] using
            (htag ▸ efficiency.firstQuery_le_budget challenge.parameter))
  | true =>
      exact M.instPartialOrder.le_trans _ _ _ hexact (by
          simpa only [queryExactBudget, ↓reduceIte, reductionAdapter] using
            efficiency.repeatQuery_le_budget sec)

@[simp] theorem concreteDDHReduction_runDist
    (F : Family M Parameter Scalar Carrier)
    (efficiency : ReductionEfficiencyCertificate measure F)
    (adversary : Crypto.Infrastructure.Complexity.OracleMachine M
      (PublicInput Parameter (PublicKey (Carrier := Carrier)))
      (fun _sec _input => Bool)
      (indCPAOracleSpec
        (Message (Carrier := Carrier)) (Ciphertext (Carrier := Carrier))))
    (rightMessage : Bool)
    (sec : Crypto.SecPar)
    (challenge : Crypto.Assumption.DL.DDH.ChallengeInput F) :
    (concreteDDHReduction F efficiency adversary rightMessage).runDist
        sec challenge =
      if F.parameterSec challenge.parameter = sec then
        adversary.runWithEnv sec (reductionPublicInput F sec challenge)
          (reductionOracle F sec challenge rightMessage)
      else
        PMF.pure false := by
  by_cases htag : F.parameterSec challenge.parameter = sec
  · simp only [Crypto.Infrastructure.Complexity.ProbabilisticMachine.runDist,
      RandomizedComputation.valueDist, concreteDDHReduction, htag, if_true,
      RandCosted.valueDist_bind, valueDist_reductionPrepare, PMF.pure_bind]
    rw [adversary.valueDist_runCosted]
    rw [erase_costedReductionOracle]
  · simp only [Crypto.Infrastructure.Complexity.ProbabilisticMachine.runDist,
      RandomizedComputation.valueDist, concreteDDHReduction, htag, if_false,
      valueDist_reductionReject]

/--
The pure PMF specification obtained by erasing the concrete reduction's costs
on a correctly tagged challenge. It is deliberately not packaged as a second
zero-cost machine.
-/
noncomputable def semanticDDHReduction
    (F : Family M Parameter Scalar Carrier)
    (adversary : Crypto.Infrastructure.Complexity.OracleMachine M
      (PublicInput Parameter (PublicKey (Carrier := Carrier)))
      (fun _sec _input => Bool)
      (indCPAOracleSpec
        (Message (Carrier := Carrier)) (Ciphertext (Carrier := Carrier))))
    (rightMessage : Bool)
    (sec : Crypto.SecPar)
    (challenge : Crypto.Assumption.DL.DDH.ChallengeInput F) : PMF Bool :=
  adversary.runWithEnv sec (reductionPublicInput F sec challenge)
    (reductionOracle F sec challenge rightMessage)

/-- The concrete costed machine is the unique source of reduction semantics. -/
theorem concreteDDHReduction_runDist_eq_semantic
    (F : Family M Parameter Scalar Carrier)
    (efficiency : ReductionEfficiencyCertificate measure F)
    (adversary : Crypto.Infrastructure.Complexity.OracleMachine M
      (PublicInput Parameter (PublicKey (Carrier := Carrier)))
      (fun _sec _input => Bool)
      (indCPAOracleSpec
        (Message (Carrier := Carrier)) (Ciphertext (Carrier := Carrier))))
    (rightMessage : Bool)
    (sec : Crypto.SecPar)
    (challenge : Crypto.Assumption.DL.DDH.ChallengeInput F)
    (htag : F.parameterSec challenge.parameter = sec) :
    (concreteDDHReduction F efficiency adversary rightMessage).runDist
        sec challenge =
      semanticDDHReduction F adversary rightMessage sec challenge := by
  rw [concreteDDHReduction_runDist]
  simp only [htag, if_true, semanticDDHReduction]

/-- Exact input-dependent budget of the closed reduction.  The cost expression
retains the operational order `prepare ; adversary-local ; oracle queries`. -/
def concreteReductionBudget
    (F : Family M Parameter Scalar Carrier)
    (efficiency : ReductionEfficiencyCertificate measure F)
    (adversary : Crypto.Infrastructure.Complexity.TimedOracleMachine
      M measure
      (PublicInput Parameter (PublicKey (Carrier := Carrier)))
      (fun _sec _input => Bool)
      (indCPAOracleSpec
        (Message (Carrier := Carrier)) (Ciphertext (Carrier := Carrier))))
    (sec : Crypto.SecPar)
    (challenge : Crypto.Assumption.DL.DDH.ChallengeInput F) : M.Cost :=
  if F.parameterSec challenge.parameter = sec then
    M.instAddMonoid.add
      (M.instAddMonoid.add efficiency.prepareCost M.instAddMonoid.zero)
      (M.instAddMonoid.add
        (adversary.localBudget sec (reductionPublicInput F sec challenge))
        (Oracle.Program.repeatCost M
          (adversary.totalQueryBudget sec (reductionPublicInput F sec challenge))
          (efficiency.queryBudget sec)))
  else
    M.instAddMonoid.add efficiency.rejectCost M.instAddMonoid.zero

/-- Uniform natural runtime of the closed reduction, including its reject
branch. -/
def concreteReductionRuntime
    (efficiency : ReductionEfficiencyCertificate measure F)
    (adversary : Crypto.Infrastructure.Complexity.TimedOracleMachine
      M measure
      (PublicInput Parameter (PublicKey (Carrier := Carrier)))
      (fun _sec _input => Bool)
      (indCPAOracleSpec
        (Message (Carrier := Carrier)) (Ciphertext (Carrier := Carrier)))) :
    Crypto.SecPar → Nat :=
  fun sec =>
    max (efficiency.rejectRuntime sec)
      (efficiency.prepareRuntime sec +
        (adversary.localRuntime sec +
          adversary.totalQueryRuntime sec * efficiency.queryRuntime sec))

/-- The concrete reduction is a timed machine without any operational
admission premise. -/
noncomputable def concreteDDHReductionTimed
    (F : Family M Parameter Scalar Carrier)
    (efficiency : ReductionEfficiencyCertificate measure F)
    (adversary : Crypto.Infrastructure.Complexity.TimedOracleMachine
      M measure
      (PublicInput Parameter (PublicKey (Carrier := Carrier)))
      (fun _sec _input => Bool)
      (indCPAOracleSpec
        (Message (Carrier := Carrier)) (Ciphertext (Carrier := Carrier))))
    (rightMessage : Bool) :
    Crypto.Infrastructure.Complexity.TimedMachine M measure
      (fun _sec => Crypto.Assumption.DL.DDH.ChallengeInput F)
      (fun _sec _challenge => Bool) where
  toProbabilisticMachine :=
    concreteDDHReduction F efficiency adversary.toOracleMachine rightMessage
  certificate :=
    { budget := concreteReductionBudget F efficiency adversary
      sound := by
        intro sec challenge result hresult
        by_cases htag : F.parameterSec challenge.parameter = sec
        · simp only [concreteDDHReduction, htag, if_true] at hresult
          simp only [concreteReductionBudget, htag, if_true]
          rw [reductionPrepare_eq_liftCosted] at hresult
          exact RandCosted.CostBound.bind_liftCosted
            (⟨reductionPublicInput F sec challenge,
                M.instAddMonoid.add efficiency.prepareCost
                  M.instAddMonoid.zero⟩ : Costed M _)
            (fun prepared => adversary.toOracleMachine.runCosted sec prepared
              (costedReductionOracle F efficiency sec challenge rightMessage))
            (by
              intro continuationResult hcontinuationResult
              exact adversary.runCosted_cost_le sec
                (reductionPublicInput F sec challenge)
                (costedReductionOracle F efficiency sec challenge rightMessage)
                (efficiency.queryBudget sec)
                (efficiency.repeatBudgetMono sec) efficiency.exchange
                (costedReductionOracle_queryCostBoundAt F efficiency sec
                  challenge rightMessage htag)
                continuationResult hcontinuationResult)
            result hresult
        · simp only [concreteDDHReduction, htag, if_false] at hresult
          simp only [concreteReductionBudget, htag, if_false]
          rw [reductionReject_eq_liftCosted] at hresult
          simp only [RandCosted.liftCosted, PMF.mem_support_pure_iff] at hresult
          subst result
          exact M.instPartialOrder.le_refl _
      runtime := concreteReductionRuntime efficiency adversary
      budget_le_runtime := by
        intro sec challenge
        by_cases htag : F.parameterSec challenge.parameter = sec
        · simp only [concreteReductionBudget, htag, if_true,
            concreteReductionRuntime]
          rw [NatMeasure.map_add, NatMeasure.map_add, NatMeasure.map_add]
          have repeatedCost :
              measure
                  (Oracle.Program.repeatCost M
                    (adversary.totalQueryBudget sec
                      (reductionPublicInput F sec challenge))
                    (efficiency.queryBudget sec)) =
                adversary.totalQueryBudget sec
                    (reductionPublicInput F sec challenge) *
                  measure (efficiency.queryBudget sec) := by
            simpa only [Oracle.Program.repeatCost, Nat.nsmul_eq_mul] using
              measure.map_nsmul
                (adversary.totalQueryBudget sec
                  (reductionPublicInput F sec challenge))
                (efficiency.queryBudget sec)
          rw [repeatedCost, NatMeasure.map_zero, Nat.add_zero]
          apply le_max_of_le_right
          exact Nat.add_le_add
            (by
              simpa only [NatMeasure.map_add, NatMeasure.map_zero] using
                efficiency.prepareCost_le_runtime sec)
            (Nat.add_le_add
              (adversary.localBudget_le_runtime sec
                (reductionPublicInput F sec challenge))
              (Nat.mul_le_mul
                (adversary.totalQueryBudget_le_runtime sec
                  (reductionPublicInput F sec challenge))
                (efficiency.queryBudget_le_runtime sec)))
        · simp only [concreteReductionBudget, htag, if_false,
            concreteReductionRuntime]
          exact (efficiency.rejectCost_le_runtime sec).trans
            (le_max_left _ _) }

@[simp] theorem concreteDDHReductionTimed_runtime
    (F : Family M Parameter Scalar Carrier)
    (efficiency : ReductionEfficiencyCertificate measure F)
    (adversary : Crypto.Infrastructure.Complexity.TimedOracleMachine
      M measure
      (PublicInput Parameter (PublicKey (Carrier := Carrier)))
      (fun _sec _input => Bool)
      (indCPAOracleSpec
        (Message (Carrier := Carrier)) (Ciphertext (Carrier := Carrier))))
    (rightMessage : Bool) :
    (concreteDDHReductionTimed F efficiency adversary rightMessage).runtime =
      concreteReductionRuntime efficiency adversary :=
  rfl

/-- Internally validated first-order adapter bundle used by the operational
compiler.  Its host boundary contains only the canonical representation maps;
all charged work is executed by the three stored programs. -/
noncomputable def reductionOperationalAdapter
    (F : Family M Parameter Scalar Carrier)
    (efficiency : ReductionEfficiencyCertificate measure F)
    (rightMessage : Bool) :
    Crypto.Infrastructure.Complexity.FirstOrderOracleAdapter M measure
      (fun _sec => Crypto.Assumption.DL.DDH.ChallengeInput F)
      (PublicInput Parameter (PublicKey (Carrier := Carrier)))
      (fun _sec => Bool)
      (indCPAOracleSpec
        (Message (Carrier := Carrier)) (Ciphertext (Carrier := Carrier)))
      (interpret Parameter Carrier)
      (algebra (reductionAdapter F efficiency))
      (PrepareInputTy Parameter Carrier) (PrepareOutputTy Parameter Carrier)
      .unit .bool (QueryInputTy Parameter Carrier) (QueryOutputTy Parameter Carrier) where
  algebraValid := algebra_valid (reductionAdapter F efficiency)
  accepted := fun sec challenge => F.parameterSec challenge.parameter = sec
  acceptedDecidable := fun _sec _challenge => inferInstance
  prepareProgram := prepareProgram Parameter Carrier
  rejectProgram := rejectProgram Parameter Carrier
  queryProgram := queryProgram Parameter Carrier rightMessage
  prepareBudget := prepareBudget (reductionAdapter F efficiency)
  rejectBudget := rejectBudget (reductionAdapter F efficiency)
  queryBudget := queryExactBudget (reductionAdapter F efficiency)
  prepareCostBound := prepare_costBound (reductionAdapter F efficiency)
  rejectCostBound := reject_costBound (reductionAdapter F efficiency)
  queryCostBound := query_costBound (reductionAdapter F efficiency) rightMessage
  prepareInput := fun _sec challenge =>
    prepareInputValue challenge.parameter challenge.left
  prepareOutput := fun _sec _challenge prepared =>
    { param := prepared.1.down
      publicKey := prepared.2.down }
  rejectInput := fun _sec _challenge => ULift.up ()
  rejectOutput := fun _sec _challenge rejected => rejected.down
  State := Bool
  init := fun _sec _challenge _callerInput => false
  queryInput := fun _sec challenge _callerInput name _querySec used query => by
    cases name
    exact queryInputValue challenge.parameter challenge.right challenge.shared
      used query.1 query.2
  queryOutput := fun _sec _challenge _callerInput name output => by
    cases name
    exact
      (output.1.map (fun ciphertext =>
        (ciphertext.1.down, ciphertext.2.down)), output.2.down)
  prepareRuntime := efficiency.prepareRuntime
  rejectRuntime := efficiency.rejectRuntime
  queryRuntime := efficiency.queryRuntime
  prepareBudget_le_runtime := by
    intro sec challenge
    simpa only [prepareBudget, reductionAdapter] using
      efficiency.prepareCost_le_runtime sec
  rejectBudget_le_runtime := by
    intro sec challenge
    simpa only [rejectBudget, reductionAdapter] using
      efficiency.rejectCost_le_runtime sec
  queryBudget_le_runtime := by
    intro sec challenge callerInput name querySec used query htag
    cases name
    cases used with
    | false =>
        apply (measure.monotone_toNat ?_).trans
          (efficiency.queryBudget_le_runtime sec)
        simpa only [queryExactBudget, Bool.false_eq_true, ↓reduceIte,
          reductionAdapter] using
          (htag ▸ efficiency.firstQuery_le_budget challenge.parameter)
    | true =>
        apply (measure.monotone_toNat ?_).trans
          (efficiency.queryBudget_le_runtime sec)
        simpa only [queryExactBudget, ↓reduceIte, reductionAdapter] using
          efficiency.repeatQuery_le_budget sec

/-- The generic controlled compiler produces exactly the concrete reduction
run, rather than a second semantic implementation. -/
theorem reductionOperationalAdapter_close
    (F : Family M Parameter Scalar Carrier)
    (efficiency : ReductionEfficiencyCertificate measure F)
    (adversary : Crypto.Infrastructure.Complexity.OracleMachine M
      (PublicInput Parameter (PublicKey (Carrier := Carrier)))
      (fun _sec _input => Bool)
      (indCPAOracleSpec
        (Message (Carrier := Carrier)) (Ciphertext (Carrier := Carrier))))
    (rightMessage : Bool) :
    (reductionOperationalAdapter F efficiency rightMessage).close adversary =
      (concreteDDHReduction F efficiency adversary rightMessage).run := by
  rfl

@[simp] theorem reductionOperationalAdapter_closedRuntime
    (F : Family M Parameter Scalar Carrier)
    (efficiency : ReductionEfficiencyCertificate measure F)
    (adversary : Crypto.Infrastructure.Complexity.TimedOracleMachine
      M measure
      (PublicInput Parameter (PublicKey (Carrier := Carrier)))
      (fun _sec _input => Bool)
      (indCPAOracleSpec
        (Message (Carrier := Carrier)) (Ciphertext (Carrier := Carrier))))
    (rightMessage : Bool) :
    (reductionOperationalAdapter F efficiency rightMessage).closedRuntime
        (adversary.localRuntime, adversary.totalQueryRuntime) =
      concreteReductionRuntime efficiency adversary :=
  rfl

/-- Polynomial closure of the exact concrete-reduction runtime expression. -/
theorem concreteReductionRuntime_isPoly
    (F : Family M Parameter Scalar Carrier)
    (efficiency : ReductionEfficiencyCertificate measure F)
    (adversary : Crypto.Infrastructure.Complexity.PPTOracleMachine
      M measure
      (PublicInput Parameter (PublicKey (Carrier := Carrier)))
      (fun _sec _input => Bool)
      (indCPAOracleSpec
        (Message (Carrier := Carrier)) (Ciphertext (Carrier := Carrier)))) :
    Crypto.Infrastructure.Asymptotic.IsPolyBounded
      (concreteReductionRuntime efficiency adversary.toTimedOracleMachine) := by
  exact Crypto.Infrastructure.Asymptotic.IsPolyBounded.max
    efficiency.rejectRuntime_isPoly
    (Crypto.Infrastructure.Asymptotic.IsPolyBounded.add
      efficiency.prepareRuntime_isPoly
      (Crypto.Infrastructure.Asymptotic.IsPolyBounded.add
        adversary.localRuntime_isPoly
        (Crypto.Infrastructure.Asymptotic.IsPolyBounded.mul
          adversary.totalQueryRuntime_isPoly
          efficiency.queryRuntime_isPoly)))

/-- Admission is generated solely from the admitted caller and the internally
validated adapter bundle. -/
theorem concreteDDHReduction_admission
    (F : Family M Parameter Scalar Carrier)
    (efficiency : ReductionEfficiencyCertificate measure F)
    (adversary : Crypto.Infrastructure.Complexity.PPTOracleMachine
      M measure
      (PublicInput Parameter (PublicKey (Carrier := Carrier)))
      (fun _sec _input => Bool)
      (indCPAOracleSpec
        (Message (Carrier := Carrier)) (Ciphertext (Carrier := Carrier))))
    (rightMessage : Bool) :
    Crypto.Infrastructure.Complexity.PPTAdmissible M measure
      (concreteDDHReductionTimed F efficiency adversary.toTimedOracleMachine
        rightMessage).run
      (concreteDDHReductionTimed F efficiency adversary.toTimedOracleMachine
        rightMessage).runtime := by
  simpa only [reductionOperationalAdapter_close,
      reductionOperationalAdapter_closedRuntime,
      concreteDDHReductionTimed_runtime] using
    (Crypto.Infrastructure.Complexity.PPTAdmissible.ofControlledOracleAdapter
      adversary.toOracleMachine
      (reductionOperationalAdapter F efficiency rightMessage)
      adversary.localRuntime adversary.totalQueryRuntime (by
        change Crypto.Infrastructure.Complexity.OperationalRealization
          adversary.toOracleMachine
          (adversary.localRuntime, adversary.totalQueryRuntime)
        exact adversary.admission))

/-- Concrete admitted DDH distinguisher for either IND-CPA challenge bit. -/
noncomputable def concreteDDHReductionPPT
    (F : Family M Parameter Scalar Carrier)
    (efficiency : ReductionEfficiencyCertificate measure F)
    (adversary : Crypto.Infrastructure.Complexity.PPTOracleMachine
      M measure
      (PublicInput Parameter (PublicKey (Carrier := Carrier)))
      (fun _sec _input => Bool)
      (indCPAOracleSpec
        (Message (Carrier := Carrier)) (Ciphertext (Carrier := Carrier))))
    (rightMessage : Bool) :
    Crypto.Infrastructure.Complexity.PPTMachine M measure
      (fun _sec => Crypto.Assumption.DL.DDH.ChallengeInput F)
      (fun _sec _challenge => Bool) :=
  Crypto.Infrastructure.Complexity.PPTMachine.ofAdmittedTimedMachine
    (concreteDDHReductionTimed F efficiency adversary.toTimedOracleMachine
      rightMessage)
    (concreteReductionRuntime_isPoly F efficiency adversary)
    (concreteDDHReduction_admission F efficiency adversary rightMessage)

/-- Compose the pure reduction specification with an arbitrary DDH sample. -/
noncomputable def semanticReductionGame
    (F : Family M Parameter Scalar Carrier)
    (sample : Crypto.SecPar → PMF
      (Crypto.Assumption.DL.DDH.ChallengeInput F))
    (adversary : Crypto.Infrastructure.Complexity.OracleMachine M
      (PublicInput Parameter (PublicKey (Carrier := Carrier)))
      (fun _sec _input => Bool)
      (indCPAOracleSpec
        (Message (Carrier := Carrier)) (Ciphertext (Carrier := Carrier))))
    (rightMessage : Bool) :
    Crypto.Infrastructure.Computation.Game Bool :=
  fun sec => PMF.bind (sample sec)
    (semanticDDHReduction F adversary rightMessage sec)

/-- Run the semantic reduction against genuine DDH tuples. -/
noncomputable def realReductionGame
    (F : Family M Parameter Scalar Carrier)
    (adversary : Crypto.Infrastructure.Complexity.OracleMachine M
      (PublicInput Parameter (PublicKey (Carrier := Carrier)))
      (fun _sec _input => Bool)
      (indCPAOracleSpec
        (Message (Carrier := Carrier)) (Ciphertext (Carrier := Carrier))))
    (rightMessage : Bool) :
    Crypto.Infrastructure.Computation.Game Bool :=
  semanticReductionGame F (Crypto.Assumption.DL.DDH.realSample F)
    adversary rightMessage

/-- Run the semantic reduction against random DDH tuples. -/
noncomputable def randomReductionGame
    (F : Family M Parameter Scalar Carrier)
    (adversary : Crypto.Infrastructure.Complexity.OracleMachine M
      (PublicInput Parameter (PublicKey (Carrier := Carrier)))
      (fun _sec _input => Bool)
      (indCPAOracleSpec
        (Message (Carrier := Carrier)) (Ciphertext (Carrier := Carrier))))
    (rightMessage : Bool) :
    Crypto.Infrastructure.Computation.Game Bool :=
  semanticReductionGame F (Crypto.Assumption.DL.DDH.randomSample F)
    adversary rightMessage

/-- PMF bind respects continuation equality on the support actually sampled. -/
private theorem pmf_bind_congr_on_support
    {α β : Type*} (sample : PMF α) (left right : α → PMF β)
    (heq : ∀ value, value ∈ sample.support → left value = right value) :
    PMF.bind sample left = PMF.bind sample right := by
  apply PMF.ext
  intro output
  simp only [PMF.bind_apply]
  apply tsum_congr
  intro value
  by_cases hvalue : value ∈ sample.support
  · rw [heq value hvalue]
  · have hzero : sample value = 0 := by
      simpa only [PMF.mem_support_iff, not_ne_iff] using hvalue
    simp only [hzero, zero_mul]

/-- On a sample whose setup tag is valid, the concrete compiled machine and
the semantic reduction induce exactly the same security game. -/
private theorem concreteSecurityGame_eq_semantic
    (F : Family M Parameter Scalar Carrier)
    (efficiency : ReductionEfficiencyCertificate measure F)
    (adversary : Crypto.Infrastructure.Complexity.PPTOracleMachine
      M measure
      (PublicInput Parameter (PublicKey (Carrier := Carrier)))
      (fun _sec _input => Bool)
      (indCPAOracleSpec
        (Message (Carrier := Carrier)) (Ciphertext (Carrier := Carrier))))
    (rightMessage : Bool)
    (sample : Crypto.SecPar → PMF
      (Crypto.Assumption.DL.DDH.ChallengeInput F))
    (htag : ∀ sec challenge, challenge ∈ (sample sec).support →
      F.parameterSec challenge.parameter = sec) :
    Crypto.Infrastructure.GameBased.Distinguishing.securityGame sample
        (concreteDDHReductionPPT F efficiency adversary
          rightMessage).toProbabilisticMachine =
      semanticReductionGame F sample adversary.toOracleMachine
        rightMessage := by
  funext sec
  unfold Crypto.Infrastructure.GameBased.Distinguishing.securityGame
    semanticReductionGame
  apply pmf_bind_congr_on_support
  intro challenge hchallenge
  exact concreteDDHReduction_runDist_eq_semantic F efficiency
    adversary.toOracleMachine rightMessage sec challenge
    (htag sec challenge hchallenge)

theorem concreteRealReductionGame_eq
    (F : Family M Parameter Scalar Carrier)
    (efficiency : ReductionEfficiencyCertificate measure F)
    (adversary : Crypto.Infrastructure.Complexity.PPTOracleMachine
      M measure
      (PublicInput Parameter (PublicKey (Carrier := Carrier)))
      (fun _sec _input => Bool)
      (indCPAOracleSpec
        (Message (Carrier := Carrier)) (Ciphertext (Carrier := Carrier))))
    (rightMessage : Bool) :
    Crypto.Infrastructure.GameBased.Distinguishing.securityGame
        (Crypto.Assumption.DL.DDH.realSample F)
        (concreteDDHReductionPPT F efficiency adversary
          rightMessage).toProbabilisticMachine =
      realReductionGame F adversary.toOracleMachine rightMessage := by
  exact concreteSecurityGame_eq_semantic F efficiency adversary rightMessage
    (Crypto.Assumption.DL.DDH.realSample F)
    (Crypto.Assumption.DL.DDH.parameterSec_eq_of_mem_support_realSample F)

theorem concreteRandomReductionGame_eq
    (F : Family M Parameter Scalar Carrier)
    (efficiency : ReductionEfficiencyCertificate measure F)
    (adversary : Crypto.Infrastructure.Complexity.PPTOracleMachine
      M measure
      (PublicInput Parameter (PublicKey (Carrier := Carrier)))
      (fun _sec _input => Bool)
      (indCPAOracleSpec
        (Message (Carrier := Carrier)) (Ciphertext (Carrier := Carrier))))
    (rightMessage : Bool) :
    Crypto.Infrastructure.GameBased.Distinguishing.securityGame
        (Crypto.Assumption.DL.DDH.randomSample F)
        (concreteDDHReductionPPT F efficiency adversary
          rightMessage).toProbabilisticMachine =
      randomReductionGame F adversary.toOracleMachine rightMessage := by
  exact concreteSecurityGame_eq_semantic F efficiency adversary rightMessage
    (Crypto.Assumption.DL.DDH.randomSample F)
    (Crypto.Assumption.DL.DDH.parameterSec_eq_of_mem_support_randomSample F)

/--
Compatibility certificate for the concrete compiler output.  Unlike the old
existential interface, it contains no arbitrary machine: both games are fixed
to `concreteDDHReductionPPT` built from its stored efficiency certificate.
-/
structure DDHReductionCertificate
    (F : Family M Parameter Scalar Carrier)
    (measure : NatMeasure M)
    (adversary : Crypto.Infrastructure.Complexity.PPTOracleMachine M measure
      (PublicInput Parameter (PublicKey (Carrier := Carrier)))
      (fun _sec _input => Bool)
      (indCPAOracleSpec
        (Message (Carrier := Carrier)) (Ciphertext (Carrier := Carrier))))
    (rightMessage : Bool) where
  efficiency : ReductionEfficiencyCertificate measure F
  realGame_eq :
    Crypto.Infrastructure.GameBased.Distinguishing.securityGame
        (Crypto.Assumption.DL.DDH.realSample F)
        (concreteDDHReductionPPT F efficiency adversary
          rightMessage).toProbabilisticMachine =
      realReductionGame F adversary.toOracleMachine rightMessage
  randomGame_eq :
    Crypto.Infrastructure.GameBased.Distinguishing.securityGame
        (Crypto.Assumption.DL.DDH.randomSample F)
        (concreteDDHReductionPPT F efficiency adversary
          rightMessage).toProbabilisticMachine =
      randomReductionGame F adversary.toOracleMachine rightMessage

/--
The operational closure obligation for the standard black-box reduction:
every admitted PPT IND-CPA oracle adversary can be compiled, for either
challenge message, to an admitted PPT DDH distinguisher with the semantic
distribution above.
-/
def DDHReductionPPTClosed
    (measure : NatMeasure M)
    (F : Family M Parameter Scalar Carrier) : Prop :=
  ∀ adversary : Crypto.Infrastructure.Complexity.PPTOracleMachine
      M measure
      (PublicInput Parameter (PublicKey (Carrier := Carrier)))
      (fun _sec _input => Bool)
      (indCPAOracleSpec
        (Message (Carrier := Carrier)) (Ciphertext (Carrier := Carrier))),
    ∀ rightMessage : Bool,
      Nonempty (DDHReductionCertificate F measure
        adversary rightMessage)

/-- Canonical certificate produced by the concrete compiler. -/
noncomputable def ddhReductionCertificate
    (F : Family M Parameter Scalar Carrier)
    (efficiency : ReductionEfficiencyCertificate measure F)
    (adversary : Crypto.Infrastructure.Complexity.PPTOracleMachine
      M measure
      (PublicInput Parameter (PublicKey (Carrier := Carrier)))
      (fun _sec _input => Bool)
      (indCPAOracleSpec
        (Message (Carrier := Carrier)) (Ciphertext (Carrier := Carrier))))
    (rightMessage : Bool) :
    DDHReductionCertificate F measure adversary rightMessage where
  efficiency := efficiency
  realGame_eq := concreteRealReductionGame_eq F efficiency adversary rightMessage
  randomGame_eq :=
    concreteRandomReductionGame_eq F efficiency adversary rightMessage

/-- Operational closure is now derived in the library; callers provide only
the explicit polynomial efficiency certificate. -/
theorem ddhReductionPPTClosed
    (F : Family M Parameter Scalar Carrier)
    (efficiency : ReductionEfficiencyCertificate measure F) :
    DDHReductionPPTClosed measure F := by
  intro adversary rightMessage
  exact ⟨ddhReductionCertificate F efficiency adversary rightMessage⟩

private def publicInput
    (_F : Family M Parameter Scalar Carrier)
    (sec : Crypto.SecPar)
    (parameter : Parameter) (pk : Carrier) :
    PublicInput Parameter (PublicKey (Carrier := Carrier)) sec where
  param := parameter
  publicKey := pk

private noncomputable def realSeedAnswer
    (F : Family M Parameter Scalar Carrier)
    (sec : Crypto.SecPar)
    (parameter : Parameter)
    (pk : Carrier) (rightMessage : Bool) (r : Scalar)
    (name : (indCPAOracleSpec (Message (Carrier := Carrier)) (Ciphertext (Carrier := Carrier)) sec
      (publicInput F sec parameter pk)).Name)
    (_querySec : Crypto.SecPar)
    (query : (indCPAOracleSpec (Message (Carrier := Carrier)) (Ciphertext (Carrier := Carrier)) sec
      (publicInput F sec parameter pk)).Query name) :
    PMF ((indCPAOracleSpec (Message (Carrier := Carrier)) (Ciphertext (Carrier := Carrier)) sec
      (publicInput F sec parameter pk)).Response name) := by
  cases name
  let pp := F.publicParam parameter
  change Carrier × Carrier at query
  change PMF (Option (Carrier × Carrier))
  exact PMF.pure
    (some (pp.smul.smul r pp.generator,
      pp.addGroup.add (if rightMessage then query.2 else query.1)
        (pp.smul.smul r pk)))

private noncomputable def afterChallenge
    (F : Family M Parameter Scalar Carrier)
    (sec : Crypto.SecPar)
    (parameter : Parameter) (pk : Carrier)
    (name : (indCPAOracleSpec (Message (Carrier := Carrier)) (Ciphertext (Carrier := Carrier)) sec
      (publicInput F sec parameter pk)).Name)
    (_querySec : Crypto.SecPar)
    (_query : (indCPAOracleSpec (Message (Carrier := Carrier)) (Ciphertext (Carrier := Carrier)) sec
      (publicInput F sec parameter pk)).Query name) :
    PMF ((indCPAOracleSpec (Message (Carrier := Carrier)) (Ciphertext (Carrier := Carrier)) sec
      (publicInput F sec parameter pk)).Response name) := by
  cases name
  exact PMF.pure none

private noncomputable def fixedRealOracle
    (F : Family M Parameter Scalar Carrier)
    (sec : Crypto.SecPar)
    (parameter : Parameter)
    (pk : Carrier) (rightMessage : Bool) (r : Scalar) :
    OracleEnv (indCPAOracleSpec (Message (Carrier := Carrier)) (Ciphertext (Carrier := Carrier)) sec
      (publicInput F sec parameter pk)) :=
  OracleEnv.withFixedOneShotSeed
    (realSeedAnswer F sec parameter pk rightMessage)
    (afterChallenge F sec parameter pk) r

private noncomputable def lazyRealOracle
    (F : Family M Parameter Scalar Carrier)
    (sec : Crypto.SecPar)
    (parameter : Parameter) (pk : Carrier) (rightMessage : Bool) :
    OracleEnv (indCPAOracleSpec (Message (Carrier := Carrier)) (Ciphertext (Carrier := Carrier)) sec
      (publicInput F sec parameter pk)) :=
  OracleEnv.withLazyOneShotSeed
    (@Crypto.Infrastructure.Probability.uniformPMF
      Scalar (F.publicParam parameter).fintypeScalar
      ⟨(F.publicParam parameter).commMonoidScalar.one⟩)
    (realSeedAnswer F sec parameter pk rightMessage)
    (afterChallenge F sec parameter pk)

private theorem indCPAEncryptionOracle_eq_lazyReal
    (F : Family M Parameter Scalar Carrier)
    (sec : Crypto.SecPar)
    (parameter : Parameter) (pk : Carrier) (rightMessage : Bool) :
    indCPAEncryptionOracle (scheme F) sec
        (publicInput F sec parameter pk) rightMessage =
      lazyRealOracle F sec parameter pk rightMessage := by
  let pp := F.publicParam parameter
  dsimp [indCPAEncryptionOracle, lazyRealOracle,
    OracleEnv.withLazyOneShotSeed]
  congr
  funext name querySec used query
  cases name
  change Carrier × Carrier at query
  cases used
  · simp only [Bool.false_eq_true, ↓reduceIte, scheme_encryptDist,
      PMF.bind_bind, PMF.pure_bind]
    congr 1
    funext seed
    symm
    exact PMF.pure_map _ _
  · simp only [↓reduceIte]
    symm
    exact PMF.pure_map _ _

private theorem runWithEnv_indCPAEncryptionOracle_eq_bind_fixedReal
    (F : Family M Parameter Scalar Carrier)
    (adversary : Crypto.Infrastructure.Complexity.OracleMachine M
      (PublicInput Parameter (PublicKey (Carrier := Carrier)))
      (fun _sec _input => Bool)
      (indCPAOracleSpec
        (Message (Carrier := Carrier)) (Ciphertext (Carrier := Carrier))))
    (sec : Crypto.SecPar)
    (parameter : Parameter) (pk : Carrier) (rightMessage : Bool) :
    adversary.runWithEnv sec (publicInput F sec parameter pk)
        (indCPAEncryptionOracle (scheme F) sec
          (publicInput F sec parameter pk) rightMessage) =
      PMF.bind
          (@Crypto.Infrastructure.Probability.uniformPMF
            Scalar (F.publicParam parameter).fintypeScalar
            ⟨(F.publicParam parameter).commMonoidScalar.one⟩) fun r =>
        adversary.runWithEnv sec (publicInput F sec parameter pk)
          (fixedRealOracle F sec parameter pk rightMessage r) := by
  let pp := F.publicParam parameter
  letI : Nonempty Scalar := ⟨pp.commMonoidScalar.one⟩
  rw [indCPAEncryptionOracle_eq_lazyReal F sec parameter pk rightMessage]
  unfold Crypto.Infrastructure.Complexity.OracleMachine.runWithEnv
  simp only [lazyRealOracle, fixedRealOracle]
  rw [OracleEnv.runWithEnv_withLazyOneShotSeed]
  rw [PMF.map_bind]

private theorem fixedRealOracle_eq_reductionOracle_realChallenge
    (F : Family M Parameter Scalar Carrier)
    (sec : Crypto.SecPar)
    (parameter : Parameter) (a b : Scalar) (rightMessage : Bool) :
    fixedRealOracle F sec parameter
        ((F.publicParam parameter).smul.smul a
          (F.publicParam parameter).generator) rightMessage b =
      reductionOracle F sec
        (Crypto.Assumption.DL.DDH.realChallenge F parameter a b)
        rightMessage := by
  let pp := F.publicParam parameter
  letI : AddGroup Carrier := pp.addGroup
  letI : SMul Scalar Carrier := pp.smul
  letI : CommMonoid Scalar := pp.commMonoidScalar
  have hshared : b • (a • pp.generator) = (a * b) • pp.generator := by
    calc
      b • (a • pp.generator) = a • (b • pp.generator) :=
        pp.scalarAction_commutes b a
      _ = (a * b) • pp.generator :=
        (pp.mulScalarAction a b).symm
  dsimp [fixedRealOracle, OracleEnv.withFixedOneShotSeed, reductionOracle,
    realSeedAnswer, afterChallenge]
  congr
  funext name querySec used query
  cases name
  change Carrier × Carrier at query
  cases used
  · simp only [Bool.false_eq_true, ↓reduceIte,
      Crypto.Assumption.DL.DDH.realChallenge]
    calc
      _ = PMF.pure ((some (b • pp.generator,
          (if rightMessage then query.2 else query.1) +
            b • (a • pp.generator)), true)) :=
        PMF.pure_map
          (fun response : Option (Carrier × Carrier) =>
            (response, true))
          (some (b • pp.generator,
            (if rightMessage then query.2 else query.1) +
              b • (a • pp.generator)))
      _ = _ := by
        rw [hshared]
        rfl
  · simp only [↓reduceIte]
    exact PMF.pure_map _ _

/-- In the real DDH game, the reduction perfectly simulates the selected
ElGamal IND-CPA challenge game. -/
theorem indCPASecurityGame_eq_realReductionGame
    (F : Family M Parameter Scalar Carrier)
    (adversary : Crypto.Infrastructure.Complexity.OracleMachine M
      (PublicInput Parameter (PublicKey (Carrier := Carrier)))
      (fun _sec _input => Bool)
      (indCPAOracleSpec
        (Message (Carrier := Carrier)) (Ciphertext (Carrier := Carrier))))
    (rightMessage : Bool) :
    indCPASecurityGame (scheme F) adversary rightMessage =
      realReductionGame F adversary rightMessage := by
  funext sec
  cases rightMessage <;>
    simp only [indCPASecurityGame, Bool.false_eq_true, if_false, if_true,
      Crypto.Infrastructure.GameBased.OracleDistinguishing.leftSecurityGame,
      Crypto.Infrastructure.GameBased.OracleDistinguishing.rightSecurityGame,
      Crypto.Infrastructure.GameBased.OracleDistinguishing.securityGame,
      indCPAProblem, realReductionGame, semanticReductionGame,
      Crypto.Assumption.DL.DDH.realSample_eq, scheme_setupDist,
      scheme_keygenDist, semanticDDHReduction,
      PMF.bind_bind, PMF.pure_bind]
  all_goals
    congr 1
    funext parameter
    let pp := F.publicParam parameter
    congr 1
    funext a
    change adversary.runWithEnv sec
        (publicInput F sec parameter (pp.smul.smul a pp.generator))
        (indCPAEncryptionOracle (scheme F) sec
          (publicInput F sec parameter (pp.smul.smul a pp.generator)) _) = _
    rw [runWithEnv_indCPAEncryptionOracle_eq_bind_fixedReal]
    congr 1
    funext b
    rw [fixedRealOracle_eq_reductionOracle_realChallenge F]
    rfl

private noncomputable def randomSeedDist
    (pp : PublicParam.{uCost, uScalar, uGroup} M Scalar Carrier) :
    PMF (Scalar × Carrier) :=
  PMF.bind
      (@Crypto.Infrastructure.Probability.uniformPMF
        Scalar pp.fintypeScalar ⟨pp.commMonoidScalar.one⟩) fun r =>
    PMF.bind
        (@Crypto.Infrastructure.Probability.uniformPMF
          Carrier pp.fintypeCarrier ⟨pp.addGroup.zero⟩) fun z =>
      PMF.pure (r, z)

private noncomputable def randomMaskAnswer
    (F : Family M Parameter Scalar Carrier)
    (sec : Crypto.SecPar)
    (parameter : Parameter) (pk : Carrier) (rightMessage : Bool)
    (seed : Scalar × Carrier)
    (name : (indCPAOracleSpec (Message (Carrier := Carrier)) (Ciphertext (Carrier := Carrier)) sec
      (publicInput F sec parameter pk)).Name)
    (_querySec : Crypto.SecPar)
    (query : (indCPAOracleSpec (Message (Carrier := Carrier)) (Ciphertext (Carrier := Carrier)) sec
      (publicInput F sec parameter pk)).Query name) :
    PMF ((indCPAOracleSpec (Message (Carrier := Carrier)) (Ciphertext (Carrier := Carrier)) sec
      (publicInput F sec parameter pk)).Response name) := by
  cases name
  let pp := F.publicParam parameter
  change Carrier × Carrier at query
  change PMF (Option (Carrier × Carrier))
  exact PMF.pure
    (some (pp.smul.smul seed.1 pp.generator,
      pp.addGroup.add (if rightMessage then query.2 else query.1) seed.2))

private noncomputable def uniformCiphertextAnswer
    (F : Family M Parameter Scalar Carrier)
    (sec : Crypto.SecPar)
    (parameter : Parameter) (pk : Carrier) (seed : Scalar × Carrier)
    (name : (indCPAOracleSpec (Message (Carrier := Carrier)) (Ciphertext (Carrier := Carrier)) sec
      (publicInput F sec parameter pk)).Name)
    (_querySec : Crypto.SecPar)
    (_query : (indCPAOracleSpec (Message (Carrier := Carrier)) (Ciphertext (Carrier := Carrier)) sec
      (publicInput F sec parameter pk)).Query name) :
    PMF ((indCPAOracleSpec (Message (Carrier := Carrier)) (Ciphertext (Carrier := Carrier)) sec
      (publicInput F sec parameter pk)).Response name) := by
  cases name
  exact PMF.pure
    (some ((F.publicParam parameter).smul.smul seed.1
      (F.publicParam parameter).generator, seed.2))

private noncomputable def fixedRandomMaskOracle
    (F : Family M Parameter Scalar Carrier)
    (sec : Crypto.SecPar)
    (parameter : Parameter) (pk : Carrier) (rightMessage : Bool)
    (seed : Scalar × Carrier) :
    OracleEnv (indCPAOracleSpec (Message (Carrier := Carrier)) (Ciphertext (Carrier := Carrier)) sec
      (publicInput F sec parameter pk)) :=
  OracleEnv.withFixedOneShotSeed
    (randomMaskAnswer F sec parameter pk rightMessage)
    (afterChallenge F sec parameter pk) seed

private noncomputable def lazyRandomMaskOracle
    (F : Family M Parameter Scalar Carrier)
    (sec : Crypto.SecPar)
    (parameter : Parameter) (pk : Carrier) (rightMessage : Bool) :
    OracleEnv (indCPAOracleSpec (Message (Carrier := Carrier)) (Ciphertext (Carrier := Carrier)) sec
      (publicInput F sec parameter pk)) :=
  OracleEnv.withLazyOneShotSeed (randomSeedDist (F.publicParam parameter))
    (randomMaskAnswer F sec parameter pk rightMessage)
    (afterChallenge F sec parameter pk)

private noncomputable def uniformCiphertextOracle
    (F : Family M Parameter Scalar Carrier)
    (sec : Crypto.SecPar)
    (parameter : Parameter) (pk : Carrier) :
    OracleEnv (indCPAOracleSpec (Message (Carrier := Carrier)) (Ciphertext (Carrier := Carrier)) sec
      (publicInput F sec parameter pk)) :=
  OracleEnv.withLazyOneShotSeed (randomSeedDist (F.publicParam parameter))
    (uniformCiphertextAnswer F sec parameter pk)
    (afterChallenge F sec parameter pk)

private theorem randomMaskResponse_eq_uniform
    (pp : PublicParam.{uCost, uScalar, uGroup} M Scalar Carrier)
    (firstComponent message : Carrier) :
    PMF.map (fun z => (some (firstComponent, pp.addGroup.add message z) :
        Option (Carrier × Carrier)))
        (@Crypto.Infrastructure.Probability.uniformPMF
          Carrier pp.fintypeCarrier ⟨pp.addGroup.zero⟩) =
      PMF.map (fun z => (some (firstComponent, z) :
        Option (Carrier × Carrier)))
        (@Crypto.Infrastructure.Probability.uniformPMF
          Carrier pp.fintypeCarrier ⟨pp.addGroup.zero⟩) := by
  letI : AddGroup Carrier := pp.addGroup
  letI : Fintype Carrier := pp.fintypeCarrier
  letI : Nonempty Carrier := ⟨pp.addGroup.zero⟩
  have hshift := Crypto.Infrastructure.Probability.map_add_left_uniformPMF
    pp.Carrier message
  have hmapped := congrArg
      (PMF.map (fun z => (some (firstComponent, z) :
      Option (Carrier × Carrier)))) hshift
  simpa only [PMF.map_comp, Function.comp_apply] using hmapped

private theorem lazyRandomMaskOracle_eq_uniformCiphertextOracle
    (F : Family M Parameter Scalar Carrier)
    (sec : Crypto.SecPar)
    (parameter : Parameter) (pk : Carrier) (rightMessage : Bool) :
    lazyRandomMaskOracle F sec parameter pk rightMessage =
      uniformCiphertextOracle F sec parameter pk := by
  let pp := F.publicParam parameter
  letI : AddGroup Carrier := pp.addGroup
  letI : SMul Scalar Carrier := pp.smul
  dsimp [lazyRandomMaskOracle, uniformCiphertextOracle,
    OracleEnv.withLazyOneShotSeed, randomMaskAnswer,
    uniformCiphertextAnswer, afterChallenge]
  congr
  funext name querySec used query
  cases name
  cases used
  · change Carrier × Carrier at query
    simp only [Bool.false_eq_true, if_false, randomSeedDist,
      PMF.bind_bind, PMF.pure_bind, PMF.pure_map]
    congr 1
    funext r
    have hresponse := randomMaskResponse_eq_uniform pp
      (r • pp.generator) (if rightMessage then query.2 else query.1)
    have hmapped := congrArg
      (PMF.map (fun response => (response, true))) hresponse
    calc
      PMF.bind (@Crypto.Infrastructure.Probability.uniformPMF
          Carrier pp.fintypeCarrier ⟨pp.addGroup.zero⟩)
          (fun z => PMF.map (fun response => (response, true))
            (PMF.pure (some (r • pp.generator,
              (if rightMessage then query.2 else query.1) + z)))) =
        PMF.map
          (fun z => ((some (r • pp.generator,
            (if rightMessage then query.2 else query.1) + z) :
              Option (Carrier × Carrier)), true))
          (@Crypto.Infrastructure.Probability.uniformPMF
            Carrier pp.fintypeCarrier ⟨pp.addGroup.zero⟩) := by
            rw [← PMF.bind_pure_comp]
            congr 1
            funext z
            exact PMF.pure_map _ _
      _ = PMF.map
          (fun z => ((some (r • pp.generator, z) :
            Option (Carrier × Carrier)), true))
          (@Crypto.Infrastructure.Probability.uniformPMF
            Carrier pp.fintypeCarrier ⟨pp.addGroup.zero⟩) := by
            simpa only [PMF.map_comp, Function.comp_apply] using hmapped
      _ = PMF.bind (@Crypto.Infrastructure.Probability.uniformPMF
          Carrier pp.fintypeCarrier ⟨pp.addGroup.zero⟩)
          (fun z => PMF.pure
            ((some (r • pp.generator, z) :
              Option (Carrier × Carrier)), true)) := by
            symm
            simpa only [Function.comp_apply] using
              PMF.bind_pure_comp
                (fun z => ((some (r • pp.generator, z) :
                  Option (Carrier × Carrier)), true))
                (@Crypto.Infrastructure.Probability.uniformPMF
                  Carrier pp.fintypeCarrier ⟨pp.addGroup.zero⟩)
  · rfl

private theorem fixedRandomMaskOracle_eq_reductionOracle_randomChallenge
    (F : Family M Parameter Scalar Carrier)
    (sec : Crypto.SecPar)
    (parameter : Parameter) (a b : Scalar) (z : Carrier)
    (rightMessage : Bool) :
    fixedRandomMaskOracle F sec parameter
        ((F.publicParam parameter).smul.smul a
          (F.publicParam parameter).generator) rightMessage (b, z) =
      reductionOracle F sec
        (Crypto.Assumption.DL.DDH.randomChallenge F parameter a b z)
        rightMessage := by
  dsimp [fixedRandomMaskOracle, OracleEnv.withFixedOneShotSeed,
    reductionOracle, randomMaskAnswer, afterChallenge]
  congr
  funext name querySec used query
  cases name
  cases used
  · simp only [Bool.false_eq_true, ↓reduceIte]
    exact PMF.pure_map _ _
  · simp only [↓reduceIte]
    exact PMF.pure_map _ _

private theorem runWithEnv_lazyRandomMaskOracle_eq_bind_fixedRandom
    (F : Family M Parameter Scalar Carrier)
    (adversary : Crypto.Infrastructure.Complexity.OracleMachine M
      (PublicInput Parameter (PublicKey (Carrier := Carrier)))
      (fun _sec _input => Bool)
      (indCPAOracleSpec
        (Message (Carrier := Carrier)) (Ciphertext (Carrier := Carrier))))
    (sec : Crypto.SecPar)
    (parameter : Parameter) (pk : Carrier) (rightMessage : Bool) :
    adversary.runWithEnv sec (publicInput F sec parameter pk)
        (lazyRandomMaskOracle F sec parameter pk rightMessage) =
      PMF.bind (randomSeedDist (F.publicParam parameter)) fun seed =>
        adversary.runWithEnv sec (publicInput F sec parameter pk)
          (fixedRandomMaskOracle F sec parameter pk rightMessage seed) := by
  let pp := F.publicParam parameter
  letI : Nonempty (Scalar × Carrier) :=
    ⟨(pp.commMonoidScalar.one, pp.addGroup.zero)⟩
  unfold Crypto.Infrastructure.Complexity.OracleMachine.runWithEnv
  simp only [lazyRandomMaskOracle, fixedRandomMaskOracle]
  rw [OracleEnv.runWithEnv_withLazyOneShotSeed]
  rw [PMF.map_bind]

/-- The common random-ciphertext hybrid. Its challenge response is independent
of which challenge message the adversary selected. -/
noncomputable def randomHybridGame
    (F : Family M Parameter Scalar Carrier)
    (adversary : Crypto.Infrastructure.Complexity.OracleMachine M
      (PublicInput Parameter (PublicKey (Carrier := Carrier)))
      (fun _sec _input => Bool)
      (indCPAOracleSpec
        (Message (Carrier := Carrier)) (Ciphertext (Carrier := Carrier)))) :
    Crypto.Infrastructure.Computation.Game Bool :=
  fun sec =>
    PMF.bind (F.setupDist sec) fun parameter =>
      let pp := F.publicParam parameter
      PMF.bind
          (@Crypto.Infrastructure.Probability.uniformPMF
            Scalar pp.fintypeScalar ⟨pp.commMonoidScalar.one⟩) fun a =>
        adversary.runWithEnv sec
          (publicInput F sec parameter (pp.smul.smul a pp.generator))
          (uniformCiphertextOracle F sec parameter
            (pp.smul.smul a pp.generator))

/-- In the random DDH game, either selected message reduces to the same
message-independent random-ciphertext hybrid. -/
theorem randomReductionGame_eq_randomHybridGame
    (F : Family M Parameter Scalar Carrier)
    (adversary : Crypto.Infrastructure.Complexity.OracleMachine M
      (PublicInput Parameter (PublicKey (Carrier := Carrier)))
      (fun _sec _input => Bool)
      (indCPAOracleSpec
        (Message (Carrier := Carrier)) (Ciphertext (Carrier := Carrier))))
    (rightMessage : Bool) :
    randomReductionGame F adversary rightMessage =
      randomHybridGame F adversary := by
  funext sec
  simp only [randomReductionGame, semanticReductionGame,
    Crypto.Assumption.DL.DDH.randomSample_eq, semanticDDHReduction,
    randomHybridGame,
    PMF.bind_bind, PMF.pure_bind]
  congr 1
  funext parameter
  let pp := F.publicParam parameter
  congr 1
  funext a
  rw [← lazyRandomMaskOracle_eq_uniformCiphertextOracle
    F sec parameter (pp.smul.smul a pp.generator) rightMessage]
  rw [runWithEnv_lazyRandomMaskOracle_eq_bind_fixedRandom F]
  simp only [randomSeedDist, PMF.bind_bind, PMF.pure_bind]
  congr 1
  funext b
  congr 1
  funext z
  rw [fixedRandomMaskOracle_eq_reductionOracle_randomChallenge F]
  rfl

/-- The ElGamal sequence has two transitions and three games. This is one
concrete instance of the arbitrary-length `Hybrid` interface. -/
noncomputable def gameSequence
    (F : Family M Parameter Scalar Carrier)
    (adversary : Crypto.Infrastructure.Complexity.OracleMachine M
      (PublicInput Parameter (PublicKey (Carrier := Carrier)))
      (fun _sec _input => Bool)
      (indCPAOracleSpec (Message (Carrier := Carrier)) (Ciphertext (Carrier := Carrier)))) :
    Crypto.Infrastructure.GameBased.Hybrid Bool where
  length := 2
  securityGame :=
    Fin.cases
      (indCPASecurityGame (scheme F) adversary false)
      (Fin.cases
        (randomHybridGame F adversary)
        (fun _ => indCPASecurityGame (scheme F) adversary true))

@[simp] theorem gameSequence_length
    (F : Family M Parameter Scalar Carrier)
    (adversary : Crypto.Infrastructure.Complexity.OracleMachine M
      (PublicInput Parameter (PublicKey (Carrier := Carrier)))
      (fun _sec _input => Bool)
      (indCPAOracleSpec (Message (Carrier := Carrier)) (Ciphertext (Carrier := Carrier)))) :
    (gameSequence F adversary).length = 2 :=
  rfl

@[simp] theorem gameSequence_first
    (F : Family M Parameter Scalar Carrier)
    (adversary : Crypto.Infrastructure.Complexity.OracleMachine M
      (PublicInput Parameter (PublicKey (Carrier := Carrier)))
      (fun _sec _input => Bool)
      (indCPAOracleSpec (Message (Carrier := Carrier)) (Ciphertext (Carrier := Carrier)))) :
    (gameSequence F adversary).first =
      indCPASecurityGame (scheme F) adversary false :=
  rfl

@[simp] theorem gameSequence_last
    (F : Family M Parameter Scalar Carrier)
    (adversary : Crypto.Infrastructure.Complexity.OracleMachine M
      (PublicInput Parameter (PublicKey (Carrier := Carrier)))
      (fun _sec _input => Bool)
      (indCPAOracleSpec (Message (Carrier := Carrier)) (Ciphertext (Carrier := Carrier)))) :
    (gameSequence F adversary).last =
      indCPASecurityGame (scheme F) adversary true :=
  rfl

/-- The two DDH reduction gaps establish every adjacent transition of the
ElGamal hybrid sequence. -/
theorem gameSequence_stepIndistinguishable
    (F : Family M Parameter Scalar Carrier)
    (adversary : Crypto.Infrastructure.Complexity.OracleMachine M
      (PublicInput Parameter (PublicKey (Carrier := Carrier)))
      (fun _sec _input => Bool)
      (indCPAOracleSpec (Message (Carrier := Carrier)) (Ciphertext (Carrier := Carrier))))
    (hleft : Crypto.Infrastructure.GameBased.Indistinguishable
      (realReductionGame F adversary false)
      (randomReductionGame F adversary false))
    (hright : Crypto.Infrastructure.GameBased.Indistinguishable
      (realReductionGame F adversary true)
      (randomReductionGame F adversary true)) :
    (gameSequence F adversary).StepIndistinguishable := by
  intro step
  fin_cases step
  · exact
      (Crypto.Infrastructure.GameBased.Indistinguishable.of_eq
        (indCPASecurityGame_eq_realReductionGame F adversary false)).trans
        (hleft.trans
          (Crypto.Infrastructure.GameBased.Indistinguishable.of_eq
            (randomReductionGame_eq_randomHybridGame F adversary false)))
  · exact
      (Crypto.Infrastructure.GameBased.Indistinguishable.of_eq
        (randomReductionGame_eq_randomHybridGame F adversary true)).symm.trans
        (hright.symm.trans
          (Crypto.Infrastructure.GameBased.Indistinguishable.of_eq
            (indCPASecurityGame_eq_realReductionGame F adversary true).symm))

/-- If both semantic DDH reductions have negligible gaps, then the original
left and right ElGamal IND-CPA games are indistinguishable. -/
theorem indCPA_indistinguishable_of_reductions
    (F : Family M Parameter Scalar Carrier)
    (adversary : Crypto.Infrastructure.Complexity.OracleMachine M
      (PublicInput Parameter (PublicKey (Carrier := Carrier)))
      (fun _sec _input => Bool)
      (indCPAOracleSpec (Message (Carrier := Carrier)) (Ciphertext (Carrier := Carrier))))
    (hleft : Crypto.Infrastructure.GameBased.Indistinguishable
      (realReductionGame F adversary false)
      (randomReductionGame F adversary false))
    (hright : Crypto.Infrastructure.GameBased.Indistinguishable
      (realReductionGame F adversary true)
      (randomReductionGame F adversary true)) :
    Crypto.Infrastructure.GameBased.Indistinguishable
      (indCPASecurityGame (scheme F) adversary false)
      (indCPASecurityGame (scheme F) adversary true) := by
  exact (gameSequence F adversary).endpoints_indistinguishable
    (gameSequence_stepIndistinguishable F adversary hleft hright)

/-- The concrete IND-CPA advantage is bounded by the sum of the two DDH
reduction advantages. This instantiates the arbitrary-length hybrid sum lemma. -/
theorem indCPAAdvantage_le_ddhAdvantages
    (F : Family M Parameter Scalar Carrier)
    (adversary : Crypto.Infrastructure.Complexity.OracleMachine M
      (PublicInput Parameter (PublicKey (Carrier := Carrier)))
      (fun _sec _input => Bool)
      (indCPAOracleSpec (Message (Carrier := Carrier)) (Ciphertext (Carrier := Carrier))))
    (sec : Crypto.SecPar) :
    INDCPAAdvantage (scheme F) adversary sec ≤
      Crypto.Infrastructure.GameBased.Advantage
          (realReductionGame F adversary false)
          (randomReductionGame F adversary false) sec +
        Crypto.Infrastructure.GameBased.Advantage
          (realReductionGame F adversary true)
          (randomReductionGame F adversary true) sec := by
  have h := (gameSequence F adversary).endpointAdvantage_le_sum sec
  change Crypto.Infrastructure.GameBased.Advantage
      (indCPASecurityGame (scheme F) adversary false)
      (indCPASecurityGame (scheme F) adversary true) sec ≤
    ∑ step : Fin 2,
      Crypto.Infrastructure.GameBased.Advantage
        ((gameSequence F adversary).before step)
        ((gameSequence F adversary).after step) sec at h
  rw [Fin.sum_univ_two] at h
  change Crypto.Infrastructure.GameBased.Advantage
      (indCPASecurityGame (scheme F) adversary false)
      (indCPASecurityGame (scheme F) adversary true) sec ≤
    Crypto.Infrastructure.GameBased.Advantage
        (indCPASecurityGame (scheme F) adversary false)
        (randomHybridGame F adversary) sec +
      Crypto.Infrastructure.GameBased.Advantage
        (randomHybridGame F adversary)
        (indCPASecurityGame (scheme F) adversary true) sec at h
  unfold INDCPAAdvantage
  calc
    Crypto.Infrastructure.GameBased.Advantage
        (indCPASecurityGame (scheme F) adversary false)
        (indCPASecurityGame (scheme F) adversary true) sec ≤
      Crypto.Infrastructure.GameBased.Advantage
          (indCPASecurityGame (scheme F) adversary false)
          (randomHybridGame F adversary) sec +
        Crypto.Infrastructure.GameBased.Advantage
          (randomHybridGame F adversary)
          (indCPASecurityGame (scheme F) adversary true) sec := h
    _ = Crypto.Infrastructure.GameBased.Advantage
          (realReductionGame F adversary false)
          (randomReductionGame F adversary false) sec +
        Crypto.Infrastructure.GameBased.Advantage
          (realReductionGame F adversary true)
          (randomReductionGame F adversary true) sec := by
      apply congrArg₂ (fun left right : Real => left + right)
      · rw [indCPASecurityGame_eq_realReductionGame F adversary false]
        rw [← randomReductionGame_eq_randomHybridGame F adversary false]
      · rw [← randomReductionGame_eq_randomHybridGame F adversary true]
        rw [indCPASecurityGame_eq_realReductionGame F adversary true]
        rw [Crypto.Infrastructure.GameBased.Advantage.symm
          (G₀ := randomReductionGame F adversary true)
          (G₁ := realReductionGame F adversary true)]

/-- A certified semantic reduction turns the DDH assumption into one adjacent
ElGamal hybrid transition. -/
theorem ddhReduction_indistinguishable
    (F : Family M Parameter Scalar Carrier)
    (adversary : Crypto.Infrastructure.Complexity.PPTOracleMachine M measure
      (PublicInput Parameter (PublicKey (Carrier := Carrier)))
      (fun _sec _input => Bool)
      (indCPAOracleSpec (Message (Carrier := Carrier)) (Ciphertext (Carrier := Carrier))))
    (rightMessage : Bool)
    (hDDH : Crypto.Assumption.DL.DDH.Assumption M measure F)
    (certificate : DDHReductionCertificate F measure adversary rightMessage) :
    Crypto.Infrastructure.GameBased.Indistinguishable
      (realReductionGame F adversary.toOracleMachine rightMessage)
      (randomReductionGame F adversary.toOracleMachine rightMessage) := by
  have hProblem := hDDH
    (concreteDDHReductionPPT F certificate.efficiency adversary rightMessage)
  exact
    (Crypto.Infrastructure.GameBased.Indistinguishable.of_eq
      certificate.realGame_eq.symm).trans
      (hProblem.trans
        (Crypto.Infrastructure.GameBased.Indistinguishable.of_eq
          certificate.randomGame_eq))

/--
ElGamal is IND-CPA secure under DDH.  Operational closure is constructed in
the library; the caller supplies only the explicit reduction-efficiency data.
-/
theorem indCPASecure_of_ddh
    (F : Family M Parameter Scalar Carrier)
    (hDDH : Crypto.Assumption.DL.DDH.Assumption M measure F)
    (efficiency : ReductionEfficiencyCertificate measure F) :
    INDCPASecure M measure (scheme F) := by
  intro adversary
  exact indCPA_indistinguishable_of_reductions F adversary.toOracleMachine
    (ddhReduction_indistinguishable F adversary false hDDH
      (ddhReductionCertificate F efficiency adversary false))
    (ddhReduction_indistinguishable F adversary true hDDH
      (ddhReductionCertificate F efficiency adversary true))

end CryptoConstruction.Primitive.Encryption.AsymmetricEncryption.ElGamal

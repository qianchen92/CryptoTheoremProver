import CryptoLib.Instantiation.Primitive.Encryption.AsymmetricEncryption.ElGamal.Properties.INDCPA.Definition.Cost
import CryptoLib.Instantiation.Primitive.Encryption.AsymmetricEncryption.ElGamal.Properties.INDCPA.Lemma.Reduction

/-! # Timed machine and validated adapter for the concrete DDH reduction -/

namespace CryptoLib.Instantiation.Primitive.Encryption.AsymmetricEncryption.ElGamal

open CryptoLib.Core.Infrastructure.Computation.Cost
open CryptoLib.Core.Infrastructure.Computation
open CryptoLib.Core.Infrastructure.Computation.Oracle
open CryptoLib.Core.Primitive.Encryption.AsymmetricEncryption
open CryptoLib.Program.Adapter.OneShotChoiceAdd
open scoped DDHParameter

universe uCost uParameter uScalar uGroup

variable
    {M : CostModel.{uCost}}
    {measure : NatMeasure M}
    {Parameter : Type uParameter}
    {Scalar : Type uScalar}
    {Carrier : Type uGroup}

/-- The concrete reduction is a timed machine without any operational
admission premise. -/
noncomputable def concreteDDHReductionTimed
    (F : Family M Parameter Scalar Carrier)
    (efficiency : ReductionEfficiencyCertificate measure F)
    (adversary : CryptoLib.Core.Infrastructure.Complexity.TimedOracleMachine
      M measure
      (PublicInput Parameter (PublicKey (Carrier := Carrier)))
      (fun _sec _input => Bool)
      (indCPAOracleSpec
        (Message (Carrier := Carrier)) (Ciphertext (Carrier := Carrier))))
    (rightMessage : Bool) :
    CryptoLib.Core.Infrastructure.Complexity.TimedMachine M measure
      (fun _sec => CryptoLib.Core.Assumption.DL.DDH.ChallengeInput F)
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

/-- Internally validated first-order adapter bundle used by the operational
compiler. Its host boundary contains only the canonical representation maps;
all charged work is executed by the three stored programs. -/
noncomputable def reductionOperationalAdapter
    (F : Family M Parameter Scalar Carrier)
    (efficiency : ReductionEfficiencyCertificate measure F)
    (rightMessage : Bool) :
    CryptoLib.Core.Infrastructure.Complexity.FirstOrderOracleAdapter M measure
      (fun _sec => CryptoLib.Core.Assumption.DL.DDH.ChallengeInput F)
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

end CryptoLib.Instantiation.Primitive.Encryption.AsymmetricEncryption.ElGamal

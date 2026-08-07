import CryptoLib.Instantiation.Primitive.Encryption.AsymmetricEncryption.ElGamal.Properties.INDCPA.Definition.Reduction

/-! # Cost erasure and exact-execution lemmas for the DDH reduction -/

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

@[simp] theorem reductionPrepare_eq_liftCosted
    (F : Family M Parameter Scalar Carrier)
    (efficiency : ReductionEfficiencyCertificate measure F)
    (sec : CryptoLib.Core.SecPar)
    (challenge : CryptoLib.Core.Assumption.DL.DDH.ChallengeInput F) :
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
    (sec : CryptoLib.Core.SecPar)
    (challenge : CryptoLib.Core.Assumption.DL.DDH.ChallengeInput F) :
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
    (sec : CryptoLib.Core.SecPar)
    (challenge : CryptoLib.Core.Assumption.DL.DDH.ChallengeInput F)
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
    (sec : CryptoLib.Core.SecPar)
    (challenge : CryptoLib.Core.Assumption.DL.DDH.ChallengeInput F)
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
      (CryptoLib.Program.Procedure.runCosted
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
    (adversary : CryptoLib.Core.Infrastructure.Complexity.OracleMachine M
      (PublicInput Parameter (PublicKey (Carrier := Carrier)))
      (fun _sec _input => Bool)
      (indCPAOracleSpec
        (Message (Carrier := Carrier)) (Ciphertext (Carrier := Carrier))))
    (rightMessage : Bool)
    (sec : CryptoLib.Core.SecPar)
    (challenge : CryptoLib.Core.Assumption.DL.DDH.ChallengeInput F) :
    (concreteDDHReduction F efficiency adversary rightMessage).runDist
        sec challenge =
      if F.parameterSec challenge.parameter = sec then
        adversary.runWithEnv sec (reductionPublicInput F sec challenge)
          (reductionOracle F sec challenge rightMessage)
      else
        PMF.pure false := by
  by_cases htag : F.parameterSec challenge.parameter = sec
  · simp only [CryptoLib.Core.Infrastructure.Complexity.ProbabilisticMachine.runDist,
      RandomizedComputation.valueDist, concreteDDHReduction, htag, if_true,
      RandCosted.valueDist_bind, valueDist_reductionPrepare, PMF.pure_bind]
    rw [adversary.valueDist_runCosted]
    rw [erase_costedReductionOracle]
  · simp only [CryptoLib.Core.Infrastructure.Complexity.ProbabilisticMachine.runDist,
      RandomizedComputation.valueDist, concreteDDHReduction, htag, if_false,
      valueDist_reductionReject]

/-- The concrete costed machine is the unique source of reduction semantics. -/
theorem concreteDDHReduction_runDist_eq_semantic
    (F : Family M Parameter Scalar Carrier)
    (efficiency : ReductionEfficiencyCertificate measure F)
    (adversary : CryptoLib.Core.Infrastructure.Complexity.OracleMachine M
      (PublicInput Parameter (PublicKey (Carrier := Carrier)))
      (fun _sec _input => Bool)
      (indCPAOracleSpec
        (Message (Carrier := Carrier)) (Ciphertext (Carrier := Carrier))))
    (rightMessage : Bool)
    (sec : CryptoLib.Core.SecPar)
    (challenge : CryptoLib.Core.Assumption.DL.DDH.ChallengeInput F)
    (htag : F.parameterSec challenge.parameter = sec) :
    (concreteDDHReduction F efficiency adversary rightMessage).runDist
        sec challenge =
      semanticDDHReduction F adversary rightMessage sec challenge := by
  rw [concreteDDHReduction_runDist]
  simp only [htag, if_true, semanticDDHReduction]

end CryptoLib.Instantiation.Primitive.Encryption.AsymmetricEncryption.ElGamal

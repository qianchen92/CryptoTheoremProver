import CryptoLib.Core.Infrastructure.Computation.Program.Semantics

namespace CryptoLib.Core.Infrastructure.Computation

open CryptoLib.Core.Infrastructure.Computation.Algebra
open CryptoLib.Core.Infrastructure.Computation.Cost

universe uCost uResult uOp

namespace Program.Code

variable
    {M : CostModel.{uCost}}
    {S : Signature.{uResult, uOp}}
    {A : CostedAlgebra M S}

/-- A structural execution path and its exact accumulated resource cost. -/
inductive Execution :
    {Result : Type uResult} → Code A Result → Result → M.Cost → Prop where
  | pure {Result : Type uResult} (value : Result) :
      Execution (.pure value) value M.instAddMonoid.zero
  | bind
      {First Result : Type uResult}
      {first : Code A First} {next : First → Code A Result}
      {firstValue : First} {value : Result}
      {firstCost nextCost : M.Cost}
      (firstExecution : Execution first firstValue firstCost)
      (nextExecution : Execution (next firstValue) value nextCost) :
      Execution (.bind first next) value
        (M.instAddMonoid.add firstCost nextCost)
  | call
      {Result : Type uResult} (operation : S.Op Result)
      (result : Costed M Result)
      (result_mem : result ∈ (A.exec operation).support) :
      Execution (.call operation) result.val result.cost
  | branchTrue
      {Result : Type uResult} {thenCode elseCode : Code A Result}
      {value : Result} {cost : M.Cost}
      (execution : Execution thenCode value cost) :
      Execution (.branch true thenCode elseCode) value cost
  | branchFalse
      {Result : Type uResult} {thenCode elseCode : Code A Result}
      {value : Result} {cost : M.Cost}
      (execution : Execution elseCode value cost) :
      Execution (.branch false thenCode elseCode) value cost

variable {Result : Type uResult}

/-- Every exact interpreter result determines a structural execution. -/
theorem execution_of_mem_support_runCosted
    (code : Code A Result)
    (result : Costed M Result)
    (hresult : result ∈ (runCosted code).support) :
    Execution code result.val result.cost := by
  induction code with
  | pure value =>
      simp only [runCosted, RandCosted.pure, RandCosted.liftCosted,
        Costed.pure] at hresult
      rw [PMF.mem_support_pure_iff] at hresult
      subst result
      exact Execution.pure value
  | bind first next ihFirst ihNext =>
      simp only [runCosted, RandCosted.bind] at hresult
      rw [PMF.mem_support_bind_iff] at hresult
      rcases hresult with ⟨firstResult, hfirstResult, hnextResult⟩
      rw [PMF.mem_support_map_iff] at hnextResult
      rcases hnextResult with ⟨nextResult, hnextResult, hresult⟩
      subst result
      exact Execution.bind
        (ihFirst firstResult hfirstResult)
        (ihNext firstResult.val nextResult hnextResult)
  | call operation =>
      exact Execution.call operation result hresult
  | branch condition thenCode elseCode ihThen ihElse =>
      cases condition with
      | false =>
          simp only [runCosted] at hresult
          exact Execution.branchFalse (ihElse result hresult)
      | true =>
          simp only [runCosted, if_true] at hresult
          exact Execution.branchTrue (ihThen result hresult)

variable
    {code : Code A Result}
    {value : Result} {cost : M.Cost}

/-- Every structural execution is realized by the exact interpreter. -/
theorem mem_support_runCosted_of_execution
    (execution : Execution code value cost) :
    (⟨value, cost⟩ : Costed M Result) ∈ (runCosted code).support := by
  induction execution with
  | pure value =>
      change
        (⟨value, M.instAddMonoid.zero⟩ : Costed M _) ∈
          (PMF.pure (Costed.pure M value)).support
      rw [PMF.mem_support_pure_iff]
      rfl
  | bind firstExecution nextExecution ihFirst ihNext =>
      simp only [runCosted, RandCosted.bind]
      rw [PMF.mem_support_bind_iff]
      refine ⟨⟨_, _⟩, ihFirst, ?_⟩
      rw [PMF.mem_support_map_iff]
      exact ⟨⟨_, _⟩, ihNext, rfl⟩
  | call operation result result_mem =>
      exact result_mem
  | branchTrue execution ih =>
      simpa [runCosted] using ih
  | branchFalse execution ih =>
      simpa [runCosted] using ih

/-- Structural execution and exact interpreter support describe the same paths. -/
theorem execution_iff_mem_support_runCosted :
    Execution code value cost ↔
      (⟨value, cost⟩ : Costed M Result) ∈ (runCosted code).support := by
  constructor
  · exact mem_support_runCosted_of_execution
  · intro hresult
    exact execution_of_mem_support_runCosted code ⟨value, cost⟩ hresult

end Program.Code

end CryptoLib.Core.Infrastructure.Computation

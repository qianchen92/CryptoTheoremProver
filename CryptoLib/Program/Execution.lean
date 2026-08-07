import CryptoLib.Program.Semantics

namespace CryptoLib.Program

open CryptoLib.Core.Infrastructure.Computation.Cost

universe uCost uBase uValue uOp

namespace Code

variable
    {M : CostModel.{uCost}}
    {Base : Type uBase} {interpret : Base → Type uValue}
    {S : Signature.{uBase, uOp} Base}
    {A : CostedAlgebra M interpret S}

/-- A structural execution path of first-order code with its exact cost. -/
inductive Execution :
    {context : List (Ty Base)} → {Result : Ty Base} →
      Code interpret S context Result → Env interpret context →
      Ty.denote interpret Result → M.Cost → Prop where
  | ret
      {context : List (Ty Base)} {Result : Ty Base}
      (result : Expr interpret context Result)
      (environment : Env interpret context) :
      Execution (.ret result) environment (result.eval environment)
        M.instAddMonoid.zero
  | letPure
      {context : List (Ty Base)} {Value Result : Ty Base}
      {value : Expr interpret context Value}
      {next : Code interpret S (Value :: context) Result}
      {environment : Env interpret context}
      {result : Ty.denote interpret Result} {cost : M.Cost}
      (nextExecution :
        Execution next (.cons (value.eval environment) environment)
          result cost) :
      Execution (.letPure value next) environment result cost
  | call
      {context : List (Ty Base)} {Args Value Result : Ty Base}
      {operation : S.Op Args Value} {args : Expr interpret context Args}
      {next : Code interpret S (Value :: context) Result}
      {environment : Env interpret context}
      (operationResult : Costed M (Ty.denote interpret Value))
      (operationResult_mem :
        operationResult ∈ (A.exec operation (args.eval environment)).support)
      {result : Ty.denote interpret Result} {nextCost : M.Cost}
      (nextExecution :
        Execution next (.cons operationResult.val environment)
          result nextCost) :
      Execution (.call operation args next) environment result
        (M.instAddMonoid.add operationResult.cost nextCost)
  | branchTrue
      {context : List (Ty Base)} {Result : Ty Base}
      {condition : Expr interpret context .bool}
      {thenCode elseCode : Code interpret S context Result}
      {environment : Env interpret context}
      (condition_true : (condition.eval environment).down = true)
      {result : Ty.denote interpret Result} {cost : M.Cost}
      (thenExecution : Execution thenCode environment result cost) :
      Execution (.branch condition thenCode elseCode) environment result cost
  | branchFalse
      {context : List (Ty Base)} {Result : Ty Base}
      {condition : Expr interpret context .bool}
      {thenCode elseCode : Code interpret S context Result}
      {environment : Env interpret context}
      (condition_false : (condition.eval environment).down = false)
      {result : Ty.denote interpret Result} {cost : M.Cost}
      (elseExecution : Execution elseCode environment result cost) :
      Execution (.branch condition thenCode elseCode) environment result cost

/-- Every interpreter result determines a structural first-order execution. -/
theorem execution_of_mem_support_runCosted
    {context : List (Ty Base)} {Result : Ty Base}
    (code : Code interpret S context Result)
    (environment : Env interpret context)
    (result : Costed M (Ty.denote interpret Result))
    (hresult : result ∈ (runCosted A code environment).support) :
    Execution (A := A) code environment result.val result.cost := by
  induction code with
  | ret value =>
      simp only [runCosted, RandCosted.pure, RandCosted.liftCosted,
        Costed.pure] at hresult
      rw [PMF.mem_support_pure_iff] at hresult
      subst result
      exact Execution.ret value environment
  | letPure value next ih =>
      exact Execution.letPure
        (ih (.cons (value.eval environment) environment) result hresult)
  | call operation args next ih =>
      simp only [runCosted, RandCosted.bind] at hresult
      rw [PMF.mem_support_bind_iff] at hresult
      rcases hresult with
        ⟨operationResult, operationResult_mem, nextResult_mem⟩
      rw [PMF.mem_support_map_iff] at nextResult_mem
      rcases nextResult_mem with ⟨nextResult, nextResult_mem, hresult⟩
      subst result
      exact Execution.call operationResult operationResult_mem
        (ih (.cons operationResult.val environment)
          nextResult nextResult_mem)
  | branch condition thenCode elseCode ihThen ihElse =>
      cases conditionValue : (condition.eval environment).down with
      | false =>
          simp only [runCosted, conditionValue, Bool.false_eq_true,
            ↓reduceIte] at hresult
          exact Execution.branchFalse conditionValue
            (ihElse environment result hresult)
      | true =>
          simp only [runCosted, conditionValue, ↓reduceIte] at hresult
          exact Execution.branchTrue conditionValue
            (ihThen environment result hresult)

/-- Every structural first-order execution is realized by the interpreter. -/
theorem mem_support_runCosted_of_execution
    {context : List (Ty Base)} {Result : Ty Base}
    {code : Code interpret S context Result}
    {environment : Env interpret context}
    {value : Ty.denote interpret Result} {cost : M.Cost}
    (execution : Execution (A := A) code environment value cost) :
    (⟨value, cost⟩ : Costed M _) ∈
      (runCosted A code environment).support := by
  induction execution with
  | ret result environment =>
      change
        (⟨result.eval environment, M.instAddMonoid.zero⟩ : Costed M _) ∈
          (PMF.pure (Costed.pure M (result.eval environment))).support
      rw [PMF.mem_support_pure_iff]
      rfl
  | letPure nextExecution ih =>
      exact ih
  | call operationResult operationResult_mem nextExecution ih =>
      simp only [runCosted, RandCosted.bind]
      rw [PMF.mem_support_bind_iff]
      refine ⟨operationResult, operationResult_mem, ?_⟩
      rw [PMF.mem_support_map_iff]
      exact ⟨⟨_, _⟩, ih, rfl⟩
  | branchTrue condition_true thenExecution ih =>
      simpa [runCosted, condition_true] using ih
  | branchFalse condition_false elseExecution ih =>
      simpa [runCosted, condition_false] using ih

/-- Structural execution and interpreter support describe the same paths. -/
theorem execution_iff_mem_support_runCosted
    {context : List (Ty Base)} {Result : Ty Base}
    {code : Code interpret S context Result}
    {environment : Env interpret context}
    {value : Ty.denote interpret Result} {cost : M.Cost} :
    Execution (A := A) code environment value cost ↔
      (⟨value, cost⟩ : Costed M _) ∈
        (runCosted A code environment).support := by
  constructor
  · exact mem_support_runCosted_of_execution
  · intro hresult
    exact execution_of_mem_support_runCosted code environment
      ⟨value, cost⟩ hresult

end Code

end CryptoLib.Program

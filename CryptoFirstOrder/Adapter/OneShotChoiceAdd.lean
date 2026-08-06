import CryptoFirstOrder.Core

namespace CryptoFirstOrder.Adapter.OneShotChoiceAdd

open Crypto.Infrastructure.Computation.Cost
open CryptoFirstOrder

universe uCost uParameter uCarrier

/-- The two host carriers exposed to the closed one-shot adapter. -/
inductive Base (_Parameter : Type uParameter) (_Carrier : Type uCarrier) :
    Type (max uParameter uCarrier) where
  | parameter
  | carrier
  deriving DecidableEq

/-- Interpret both host carriers in one common object-language universe. -/
def interpret
    (Parameter : Type uParameter) (Carrier : Type uCarrier) :
    Base Parameter Carrier → Type (max uParameter uCarrier)
  | .parameter => ULift.{uCarrier} Parameter
  | .carrier => ULift.{uParameter} Carrier

abbrev parameterTy
    (Parameter : Type uParameter) (Carrier : Type uCarrier) :
    Ty (Base Parameter Carrier) :=
  .base .parameter

abbrev carrierTy
    (Parameter : Type uParameter) (Carrier : Type uCarrier) :
    Ty (Base Parameter Carrier) :=
  .base .carrier

abbrev ParameterValue
    (Parameter : Type uParameter) (Carrier : Type uCarrier) :=
  Ty.denote (interpret Parameter Carrier) (parameterTy Parameter Carrier)

abbrev CarrierValue
    (Parameter : Type uParameter) (Carrier : Type uCarrier) :=
  Ty.denote (interpret Parameter Carrier) (carrierTy Parameter Carrier)

/-- Labels are static syntax carried by the trusted tick primitive. -/
inductive ChargeLabel where
  | prepare
  | reject
  | queryPrefix
  | querySuffix
  | repeatQuery
  deriving DecidableEq

/-- Exact costs used by the adapter's primitive algebra. -/
structure Costs
    (M : CostModel.{uCost}) (Parameter : Type uParameter) where
  prepare : M.Cost
  reject : M.Cost
  queryPrefix : M.Cost
  querySuffix : M.Cost
  repeatQuery : M.Cost
  add : Parameter → M.Cost

namespace Costs

def charge
    {M : CostModel.{uCost}} {Parameter : Type uParameter}
    (costs : Costs M Parameter) : ChargeLabel → M.Cost
  | .prepare => costs.prepare
  | .reject => costs.reject
  | .queryPrefix => costs.queryPrefix
  | .querySuffix => costs.querySuffix
  | .repeatQuery => costs.repeatQuery

def firstQuery
    {M : CostModel.{uCost}} {Parameter : Type uParameter}
    (costs : Costs M Parameter) (parameter : Parameter) : M.Cost :=
  M.instAddMonoid.add costs.queryPrefix
    (M.instAddMonoid.add (costs.add parameter)
      (M.instAddMonoid.add costs.querySuffix M.instAddMonoid.zero))

end Costs

abbrev Signature
    (Parameter : Type uParameter) (Carrier : Type uCarrier) :=
  CryptoFirstOrder.Signature.sum
    (TickOperation.signature (Base := Base Parameter Carrier)
      (ULift.{max uParameter uCarrier} ChargeLabel))
    (ParameterizedAddOperation.signature
      (parameterTy Parameter Carrier) (carrierTy Parameter Carrier))

def tickOperation
    {Parameter : Type uParameter} {Carrier : Type uCarrier}
    (label : ChargeLabel) :
    (Signature Parameter Carrier).Op .unit .unit :=
  .inl (.tick (ULift.up label))

def addOperation
    {Parameter : Type uParameter} {Carrier : Type uCarrier} :
    (Signature Parameter Carrier).Op
      (.prod (parameterTy Parameter Carrier)
        (.prod (carrierTy Parameter Carrier) (carrierTy Parameter Carrier)))
      (carrierTy Parameter Carrier) :=
  .inr .add

/-- Host data sufficient to instantiate the sealed parameterized-add primitive. -/
structure Adapter
    (M : CostModel.{uCost})
    (Parameter : Type uParameter) (Carrier : Type uCarrier) where
  add : Parameter → Carrier → Carrier → Carrier
  costs : Costs M Parameter

private def liftedParameterizedAdd
    {M : CostModel.{uCost}}
    {Parameter : Type uParameter} {Carrier : Type uCarrier}
    (adapter : Adapter M Parameter Carrier) :
    ParameterizedAdd
      (ParameterValue Parameter Carrier) (CarrierValue Parameter Carrier) where
  add parameter left right :=
    ULift.up (adapter.add parameter.down left.down right.down)

/-- The exact algebra is assembled only from validated tick and parameterized-add leaves. -/
noncomputable def algebra
    {M : CostModel.{uCost}}
    {Parameter : Type uParameter} {Carrier : Type uCarrier}
    (adapter : Adapter M Parameter Carrier) :
    CostedAlgebra M (interpret Parameter Carrier) (Signature Parameter Carrier) := by
  letI := liftedParameterizedAdd adapter
  exact CostedAlgebra.sum
    (TickOperation.algebra M (interpret Parameter Carrier)
      (ULift.{max uParameter uCarrier} ChargeLabel)
      (fun label => adapter.costs.charge label.down))
    (ParameterizedAddOperation.algebra M (interpret Parameter Carrier)
      (parameterTy Parameter Carrier) (carrierTy Parameter Carrier)
      (fun parameter : ParameterValue Parameter Carrier =>
        adapter.costs.add parameter.down))

/-- Structural validity of the adapter algebra; no external admission is used. -/
theorem algebra_valid
    {M : CostModel.{uCost}}
    {Parameter : Type uParameter} {Carrier : Type uCarrier}
    (adapter : Adapter M Parameter Carrier) :
    ValidAlgebra M (interpret Parameter Carrier) (algebra adapter) := by
  letI := liftedParameterizedAdd adapter
  exact ValidAlgebra.sum
    (ValidAlgebra.tick (ULift.{max uParameter uCarrier} ChargeLabel)
      (fun label => adapter.costs.charge label.down))
    (ValidAlgebra.parameterizedAdd
      (parameterTy Parameter Carrier) (carrierTy Parameter Carrier)
      (fun parameter : ParameterValue Parameter Carrier =>
        adapter.costs.add parameter.down))

abbrev PrepareInputTy
    (Parameter : Type uParameter) (Carrier : Type uCarrier) :=
  parameterTy Parameter Carrier ×ₜ carrierTy Parameter Carrier

abbrev PrepareOutputTy
    (Parameter : Type uParameter) (Carrier : Type uCarrier) :=
  PrepareInputTy Parameter Carrier

/-- Preparation is one charged structural wrapper around `(parameter, publicKey)`. -/
def prepareProgram
    (Parameter : Type uParameter) (Carrier : Type uCarrier) :
    Program (interpret Parameter Carrier) (Signature Parameter Carrier)
      (PrepareInputTy Parameter Carrier) (PrepareOutputTy Parameter Carrier) where
  body :=
    .call (tickOperation .prepare) .unit
      (.ret (.var (.there .here)))

/-- The malformed-security-parameter path has an explicit charge and returns `false`. -/
def rejectProgram
    (Parameter : Type uParameter) (Carrier : Type uCarrier) :
    Program (interpret Parameter Carrier) (Signature Parameter Carrier)
      .unit .bool where
  body :=
    .call (tickOperation .reject) .unit
      (.ret (.bool false))

abbrev QueryInputTy
    (Parameter : Type uParameter) (Carrier : Type uCarrier) :=
  Ty.tuple
    [parameterTy Parameter Carrier,
      carrierTy Parameter Carrier,
      carrierTy Parameter Carrier,
      .bool,
      carrierTy Parameter Carrier,
      carrierTy Parameter Carrier]

abbrev CiphertextTy
    (Parameter : Type uParameter) (Carrier : Type uCarrier) :=
  carrierTy Parameter Carrier ×ₜ carrierTy Parameter Carrier

abbrev QueryOutputTy
    (Parameter : Type uParameter) (Carrier : Type uCarrier) :=
  Ty.option (CiphertextTy Parameter Carrier) ×ₜ .bool

private abbrev QueryContext
    (Parameter : Type uParameter) (Carrier : Type uCarrier) :=
  [QueryInputTy Parameter Carrier]

private def queryInput
    (Parameter : Type uParameter) (Carrier : Type uCarrier) :
    Expr (interpret Parameter Carrier) (QueryContext Parameter Carrier)
      (QueryInputTy Parameter Carrier) :=
  .var .here

private def queryParameter
    (Parameter : Type uParameter) (Carrier : Type uCarrier) :
    Expr (interpret Parameter Carrier) (QueryContext Parameter Carrier)
      (parameterTy Parameter Carrier) :=
  .fst (queryInput Parameter Carrier)

private def queryRight
    (Parameter : Type uParameter) (Carrier : Type uCarrier) :
    Expr (interpret Parameter Carrier) (QueryContext Parameter Carrier)
      (carrierTy Parameter Carrier) :=
  .fst (.snd (queryInput Parameter Carrier))

private def queryShared
    (Parameter : Type uParameter) (Carrier : Type uCarrier) :
    Expr (interpret Parameter Carrier) (QueryContext Parameter Carrier)
      (carrierTy Parameter Carrier) :=
  .fst (.snd (.snd (queryInput Parameter Carrier)))

private def queryUsed
    (Parameter : Type uParameter) (Carrier : Type uCarrier) :
    Expr (interpret Parameter Carrier) (QueryContext Parameter Carrier) .bool :=
  .fst (.snd (.snd (.snd (queryInput Parameter Carrier))))

private def queryLeftMessage
    (Parameter : Type uParameter) (Carrier : Type uCarrier) :
    Expr (interpret Parameter Carrier) (QueryContext Parameter Carrier)
      (carrierTy Parameter Carrier) :=
  .fst (.snd (.snd (.snd (.snd (queryInput Parameter Carrier)))))

private def queryRightMessage
    (Parameter : Type uParameter) (Carrier : Type uCarrier) :
    Expr (interpret Parameter Carrier) (QueryContext Parameter Carrier)
      (carrierTy Parameter Carrier) :=
  .snd (.snd (.snd (.snd (.snd (queryInput Parameter Carrier)))))

private def repeatQueryCode
    (Parameter : Type uParameter) (Carrier : Type uCarrier) :
    Code (interpret Parameter Carrier) (Signature Parameter Carrier)
      (QueryContext Parameter Carrier) (QueryOutputTy Parameter Carrier) :=
  .call (tickOperation .repeatQuery) .unit
    (.ret (.pair (.none) (.bool true)))

private def freshQueryCode
    (Parameter : Type uParameter) (Carrier : Type uCarrier)
    (rightMessage : Bool) :
    Code (interpret Parameter Carrier) (Signature Parameter Carrier)
      (QueryContext Parameter Carrier) (QueryOutputTy Parameter Carrier) :=
  let selected :=
    if rightMessage then
      queryRightMessage Parameter Carrier
    else
      queryLeftMessage Parameter Carrier
  .call (tickOperation .queryPrefix) .unit
    (.call addOperation
      (.pair (queryParameter Parameter Carrier).weaken
        (.pair selected.weaken (queryShared Parameter Carrier).weaken))
      (.call (tickOperation .querySuffix) .unit
        (.ret
          (.pair
            (.some
              (.pair
                (queryRight Parameter Carrier).weaken.weaken.weaken
                (.var (.there .here))))
            (.bool true)))))

/-- One query program owns the Boolean one-shot state and both charged paths. -/
def queryProgram
    (Parameter : Type uParameter) (Carrier : Type uCarrier)
    (rightMessage : Bool) :
    Program (interpret Parameter Carrier) (Signature Parameter Carrier)
      (QueryInputTy Parameter Carrier) (QueryOutputTy Parameter Carrier) where
  body :=
    .branch (queryUsed Parameter Carrier)
      (repeatQueryCode Parameter Carrier)
      (freshQueryCode Parameter Carrier rightMessage)

/-- Canonical represented input for preparation. -/
def prepareInputValue
    {Parameter : Type uParameter} {Carrier : Type uCarrier}
    (parameter : Parameter) (publicKey : Carrier) :
    Ty.denote (interpret Parameter Carrier) (PrepareInputTy Parameter Carrier) :=
  (ULift.up parameter, ULift.up publicKey)

/-- Canonical represented input for one stateful challenge query. -/
def queryInputValue
    {Parameter : Type uParameter} {Carrier : Type uCarrier}
    (parameter : Parameter) (right shared : Carrier) (used : Bool)
    (leftMessage rightMessage : Carrier) :
    Ty.denote (interpret Parameter Carrier) (QueryInputTy Parameter Carrier) :=
  (ULift.up parameter,
    (ULift.up right,
      (ULift.up shared,
        (ULift.up used, (ULift.up leftMessage, ULift.up rightMessage)))))

@[simp] theorem algebra_exec_tick
    {M : CostModel.{uCost}}
    {Parameter : Type uParameter} {Carrier : Type uCarrier}
    (adapter : Adapter M Parameter Carrier) (label : ChargeLabel)
    (args : Ty.denote (interpret Parameter Carrier) .unit) :
    (algebra adapter).exec (tickOperation label) args =
      RandCosted.liftCosted
        (⟨ULift.up (), adapter.costs.charge label⟩ :
          Costed M (Ty.denote (interpret Parameter Carrier) .unit)) := by
  rfl

@[simp] theorem algebra_exec_add
    {M : CostModel.{uCost}}
    {Parameter : Type uParameter} {Carrier : Type uCarrier}
    (adapter : Adapter M Parameter Carrier)
    (parameter : ParameterValue Parameter Carrier)
    (left right : CarrierValue Parameter Carrier) :
    (algebra adapter).exec addOperation (parameter, (left, right)) =
      RandCosted.liftCosted
        (⟨ULift.up (adapter.add parameter.down left.down right.down),
            adapter.costs.add parameter.down⟩ :
          Costed M (CarrierValue Parameter Carrier)) := by
  rfl

@[simp] theorem runCosted_prepare
    {M : CostModel.{uCost}}
    {Parameter : Type uParameter} {Carrier : Type uCarrier}
    (adapter : Adapter M Parameter Carrier)
    (parameter : Parameter) (publicKey : Carrier) :
    Program.runCosted (algebra adapter)
        (prepareProgram Parameter Carrier)
        (prepareInputValue parameter publicKey) =
      RandCosted.liftCosted
        (⟨prepareInputValue parameter publicKey,
            M.instAddMonoid.add adapter.costs.prepare M.instAddMonoid.zero⟩ :
          Costed M _) := by
  letI := M.instAddMonoid
  simp only [Program.runCosted, prepareProgram, Code.runCosted,
    algebra_exec_tick, RandCosted.liftCosted_bind_liftCosted,
    Expr.eval, Env.get, Costed.bind, Costed.pure_val, Costed.pure_cost,
    Costs.charge]

@[simp] theorem runCosted_reject
    {M : CostModel.{uCost}}
    {Parameter : Type uParameter} {Carrier : Type uCarrier}
    (adapter : Adapter M Parameter Carrier) :
    Program.runCosted (algebra adapter)
        (rejectProgram Parameter Carrier) (ULift.up ()) =
      RandCosted.liftCosted
        (⟨ULift.up false,
            M.instAddMonoid.add adapter.costs.reject M.instAddMonoid.zero⟩ :
          Costed M (Ty.denote (interpret Parameter Carrier) .bool)) := by
  letI := M.instAddMonoid
  simp only [Program.runCosted, rejectProgram, Code.runCosted,
    algebra_exec_tick, RandCosted.liftCosted_bind_liftCosted,
    Expr.eval, Costed.bind, Costed.pure_val, Costed.pure_cost, Costs.charge]

@[simp] theorem runCosted_query_used
    {M : CostModel.{uCost}}
    {Parameter : Type uParameter} {Carrier : Type uCarrier}
    (adapter : Adapter M Parameter Carrier) (rightMessage : Bool)
    (parameter : Parameter) (right shared leftMessage chosenRightMessage : Carrier) :
    Program.runCosted (algebra adapter)
        (queryProgram Parameter Carrier rightMessage)
        (queryInputValue parameter right shared true leftMessage chosenRightMessage) =
      RandCosted.liftCosted
        (⟨(none, ULift.up true),
            M.instAddMonoid.add adapter.costs.repeatQuery M.instAddMonoid.zero⟩ :
          Costed M (Ty.denote (interpret Parameter Carrier)
            (QueryOutputTy Parameter Carrier))) := by
  letI := M.instAddMonoid
  simp only [Program.runCosted, queryProgram, repeatQueryCode, Code.runCosted,
    queryUsed, queryInput, queryInputValue, Expr.eval, Env.get,
    algebra_exec_tick, RandCosted.liftCosted_bind_liftCosted,
    Costed.bind, Costed.pure_val, Costed.pure_cost, Costs.charge,
    ↓reduceIte]

@[simp] theorem runCosted_query_fresh
    {M : CostModel.{uCost}}
    {Parameter : Type uParameter} {Carrier : Type uCarrier}
    (adapter : Adapter M Parameter Carrier) (rightMessage : Bool)
    (parameter : Parameter) (right shared leftMessage chosenRightMessage : Carrier) :
    Program.runCosted (algebra adapter)
        (queryProgram Parameter Carrier rightMessage)
        (queryInputValue parameter right shared false leftMessage chosenRightMessage) =
      RandCosted.liftCosted
        (⟨(some (ULift.up right,
              ULift.up (adapter.add parameter
                (if rightMessage then chosenRightMessage else leftMessage) shared)),
            ULift.up true),
          adapter.costs.firstQuery parameter⟩ :
          Costed M (Ty.denote (interpret Parameter Carrier)
            (QueryOutputTy Parameter Carrier))) := by
  letI := M.instAddMonoid
  cases rightMessage <;>
    simp only [Program.runCosted, queryProgram, freshQueryCode, Code.runCosted,
      queryUsed, queryInput, queryInputValue, queryParameter, queryRight,
      queryShared, queryLeftMessage, queryRightMessage, Costs.firstQuery,
      Expr.eval, Expr.weaken, Env.get, algebra_exec_tick, algebra_exec_add,
      RandCosted.liftCosted_bind_liftCosted, Costed.bind,
      Costed.pure_val, Costed.pure_cost, Costs.charge,
      Bool.false_eq_true, ↓reduceIte]

def prepareBudget
    {M : CostModel.{uCost}}
    {Parameter : Type uParameter} {Carrier : Type uCarrier}
    (adapter : Adapter M Parameter Carrier) :
    Ty.denote (interpret Parameter Carrier) (PrepareInputTy Parameter Carrier) →
      M.Cost :=
  fun _input =>
    M.instAddMonoid.add adapter.costs.prepare M.instAddMonoid.zero

def rejectBudget
    {M : CostModel.{uCost}}
    {Parameter : Type uParameter} {Carrier : Type uCarrier}
    (adapter : Adapter M Parameter Carrier) :
    Ty.denote (interpret Parameter Carrier) .unit → M.Cost :=
  fun _input =>
    M.instAddMonoid.add adapter.costs.reject M.instAddMonoid.zero

/-- The query budget preserves the exact first/repeat branch distinction. -/
def queryExactBudget
    {M : CostModel.{uCost}}
    {Parameter : Type uParameter} {Carrier : Type uCarrier}
    (adapter : Adapter M Parameter Carrier) :
    Ty.denote (interpret Parameter Carrier) (QueryInputTy Parameter Carrier) →
      M.Cost :=
  fun input =>
    if input.2.2.2.1.down then
      M.instAddMonoid.add adapter.costs.repeatQuery M.instAddMonoid.zero
    else
      adapter.costs.firstQuery input.1.down

theorem prepare_costBound
    {M : CostModel.{uCost}}
    {Parameter : Type uParameter} {Carrier : Type uCarrier}
    (adapter : Adapter M Parameter Carrier) :
    Program.CostBound (algebra adapter)
      (prepareProgram Parameter Carrier) (prepareBudget adapter) := by
  rintro ⟨⟨parameter⟩, ⟨publicKey⟩⟩ result hresult
  change result ∈
    (Program.runCosted (algebra adapter)
      (prepareProgram Parameter Carrier)
      (prepareInputValue parameter publicKey)).support at hresult
  rw [runCosted_prepare] at hresult
  simp only [RandCosted.liftCosted, PMF.mem_support_pure_iff] at hresult
  subst result
  exact M.instPartialOrder.le_refl _

theorem reject_costBound
    {M : CostModel.{uCost}}
    {Parameter : Type uParameter} {Carrier : Type uCarrier}
    (adapter : Adapter M Parameter Carrier) :
    Program.CostBound (algebra adapter)
      (rejectProgram Parameter Carrier) (rejectBudget adapter) := by
  rintro ⟨unitValue⟩ result hresult
  cases unitValue
  change result ∈
    (Program.runCosted (algebra adapter)
      (rejectProgram Parameter Carrier) (ULift.up ())).support at hresult
  rw [runCosted_reject] at hresult
  simp only [RandCosted.liftCosted, PMF.mem_support_pure_iff] at hresult
  subst result
  exact M.instPartialOrder.le_refl _

theorem query_costBound
    {M : CostModel.{uCost}}
    {Parameter : Type uParameter} {Carrier : Type uCarrier}
    (adapter : Adapter M Parameter Carrier) (rightMessage : Bool) :
    Program.CostBound (algebra adapter)
      (queryProgram Parameter Carrier rightMessage)
      (queryExactBudget adapter) := by
  rintro ⟨⟨parameter⟩,
    ⟨right⟩, ⟨shared⟩, ⟨used⟩, ⟨leftMessage⟩, ⟨chosenRightMessage⟩⟩
    result hresult
  cases used with
  | false =>
      change result ∈
        (Program.runCosted (algebra adapter)
          (queryProgram Parameter Carrier rightMessage)
          (queryInputValue parameter right shared false
            leftMessage chosenRightMessage)).support at hresult
      rw [runCosted_query_fresh] at hresult
      simp only [RandCosted.liftCosted, PMF.mem_support_pure_iff] at hresult
      subst result
      exact M.instPartialOrder.le_refl _
  | true =>
      change result ∈
        (Program.runCosted (algebra adapter)
          (queryProgram Parameter Carrier rightMessage)
          (queryInputValue parameter right shared true
            leftMessage chosenRightMessage)).support at hresult
      rw [runCosted_query_used] at hresult
      simp only [RandCosted.liftCosted, PMF.mem_support_pure_iff] at hresult
      subst result
      exact M.instPartialOrder.le_refl _

end CryptoFirstOrder.Adapter.OneShotChoiceAdd

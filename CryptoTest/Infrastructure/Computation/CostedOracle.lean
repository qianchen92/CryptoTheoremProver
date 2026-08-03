import Crypto.Infrastructure.Complexity.Machine

namespace CryptoTest.Infrastructure.Computation.CostedOracle

open Crypto.Infrastructure.Complexity
open Crypto.Infrastructure.Asymptotic
open Crypto.Infrastructure.Computation.Cost
open Crypto.Infrastructure.Computation.Oracle

inductive TestOracle where
  | bit
deriving DecidableEq

def testOracleSpec : OracleSpec where
  Name := TestOracle
  Query
    | TestOracle.bit => Bool
  Response
    | TestOracle.bit => Bool

/-- Two adaptive calls, each charged once by the machine profile. -/
def twoQueryProgram : OracleProgram CostModel.nat testOracleSpec (ULift Bool) :=
  OracleProgram.bind
      (OracleProgram.query (M := CostModel.nat) (1 : Nat) TestOracle.bit false)
      fun first =>
    OracleProgram.query (M := CostModel.nat) (1 : Nat) TestOracle.bit first.down

/-- The implementation negates its query and charges three internal units. -/
noncomputable def costedEnv : CostedOracleEnv CostModel.nat testOracleSpec where
  State := Nat
  init := 0
  query := fun name _sec state query =>
    match name with
    | TestOracle.bit => PMF.pure ⟨(!query, state + 1), 3⟩

theorem costedEnv_queryCostBound :
    costedEnv.QueryCostBound (fun _sec => 3) := by
  intro name sec state query result hresult
  cases name
  change Nat at state
  change Bool at query
  change CostedT CostModel.nat (Bool × Nat) at result
  simp only [costedEnv] at hresult
  have hresultEq :
      result = (⟨(!query, state + 1), 3⟩ : CostedT CostModel.nat (Bool × Nat)) :=
    (PMF.mem_support_pure_iff
      (⟨(!query, state + 1), 3⟩ : CostedT CostModel.nat (Bool × Nat)) result).1 hresult
  subst result
  exact Nat.le_refl 3

theorem twoQueryProgram_costBound :
    OracleProgram.CostBound twoQueryProgram 2 := by
  intro value profile execution
  unfold twoQueryProgram at execution
  cases execution with
  | bind firstExecution secondExecution =>
      cases firstExecution
      cases secondExecution
      exact Nat.le_refl 2

theorem twoQueryProgram_totalQueryBound :
    OracleProgram.TotalQueryBound twoQueryProgram 2 := by
  intro value profile execution
  unfold twoQueryProgram at execution
  cases execution with
  | bind firstExecution secondExecution =>
      cases firstExecution
      cases secondExecution
      exact Nat.le_refl 2

/-- A PPT oracle machine exposing the same two-query program. -/
noncomputable def twoQueryPPTMachine :
    PPTOracleMachine
      CostModel.nat NatMeasure.nat
      (fun _sec => Unit)
      (fun _sec => Bool)
      (fun _sec _input => testOracleSpec) where
  run := fun _sec _input => twoQueryProgram
  costBound := fun _sec _input => 2
  runtime := fun _sec => 2
  queryBound := fun _sec _input _name => 2
  totalQueryBound := fun _sec => 2
  costBound_sound := by
    intro sec input
    exact twoQueryProgram_costBound
  costBound_le_runtime := by
    intro sec input
    exact Nat.le_refl 2
  queryBound_sound := by
    intro sec input value profile execution name
    change OracleProgram.Execution twoQueryProgram value profile at execution
    unfold twoQueryProgram at execution
    cases execution with
    | bind firstExecution secondExecution =>
        cases firstExecution
        cases secondExecution
        cases name
        simp [OracleProfile.queryCount, OracleProfile.append]
  totalQueryBound_sound := by
    intro sec input
    exact twoQueryProgram_totalQueryBound
  runtime_isPoly := IsPolyBounded.const 2
  totalQueryBound_isPoly := IsPolyBounded.const 2

/-- Two machine calls plus two three-unit oracle executions compose to eight. -/
example
    (result : CostedT CostModel.nat (ULift Bool))
    (hresult :
      result ∈
        (OracleProgram.runCostedWithCostedEnv
          twoQueryProgram 0 costedEnv).support) :
    result.cost ≤ 8 := by
  simpa using
    OracleProgram.runCostedWithCostedEnv_cost_le
      twoQueryProgram 0 costedEnv 2 2 (fun _sec => 3)
      (OracleProgram.repeatCost_nat_mono 3)
      OracleProgram.costExchange_nat
      twoQueryProgram_costBound twoQueryProgram_totalQueryBound
      (costedEnv_queryCostBound.at 0) result hresult

/-- Cost erasure still produces the ordinary stateful oracle semantics. -/
example :
    RandCostedT.valueDist
        (OracleProgram.runCostedWithCostedEnv twoQueryProgram 0 costedEnv) =
      OracleProgram.runWithEnv twoQueryProgram 0 costedEnv.erase :=
  OracleProgram.valueDist_runCostedWithCostedEnv
    twoQueryProgram 0 costedEnv

/-- The machine-level bridge exposes the same eight-unit composed bound. -/
example
    (result : CostedT CostModel.nat Bool)
    (hresult :
      result ∈
        (twoQueryPPTMachine.toProbabilisticOracleMachine
          |>.runCostedWithCostedEnv 0 () costedEnv).support) :
    result.cost ≤ 8 := by
  simpa using
    twoQueryPPTMachine.toTimedOracleMachine
      |>.runCostedWithCostedEnv_cost_le_composed
        0 () costedEnv (fun _sec => 3)
        (OracleProgram.repeatCost_nat_mono 3)
        OracleProgram.costExchange_nat
        (costedEnv_queryCostBound.at 0) result hresult

/-- The composed machine/oracle runtime remains polynomially bounded. -/
example :
    IsPolyBounded
      (fun sec =>
        twoQueryPPTMachine.runtime sec +
          twoQueryPPTMachine.totalQueryBound sec * 3) :=
  twoQueryPPTMachine.composedRuntime_isPoly
    (fun _sec => 3) (IsPolyBounded.const 3)

/-- Explicit zero local work still requires an independent query certificate. -/
def zeroLocalCostQueryProgram :
    OracleProgram CostModel.nat testOracleSpec (ULift Bool) :=
  OracleProgram.query
    (M := CostModel.nat) (0 : Nat) TestOracle.bit false

theorem zeroLocalCostQueryProgram_costBound :
    OracleProgram.CostBound zeroLocalCostQueryProgram 0 := by
  intro value profile execution
  cases execution
  exact Nat.le_refl 0

theorem zeroLocalCostQueryProgram_totalQueryBound :
    OracleProgram.TotalQueryBound zeroLocalCostQueryProgram 1 := by
  intro value profile execution
  cases execution
  exact Nat.le_refl 1

/-- Generic query count, rather than zero local cost, pays for oracle work. -/
example
    (result : CostedT CostModel.nat (ULift Bool))
    (hresult :
      result ∈
        (OracleProgram.runCostedWithCostedEnv
          zeroLocalCostQueryProgram 0 costedEnv).support) :
    result.cost ≤ 3 := by
  simpa only [OracleProgram.repeatCost_nat] using
    OracleProgram.runCostedWithCostedEnv_cost_le
      zeroLocalCostQueryProgram 0 costedEnv 0 1 (fun _sec => 3)
      (OracleProgram.repeatCost_nat_mono 3)
      OracleProgram.costExchange_nat
      zeroLocalCostQueryProgram_costBound
      zeroLocalCostQueryProgram_totalQueryBound
      (CostedOracleEnv.QueryCostBound.at costedEnv_queryCostBound 0)
      result hresult

/-! ## Generic multi-resource oracle composition -/

/-- Local steps and oracle work remain separate exact resource coordinates. -/
abbrev OracleResources := Nat × Nat

abbrev oracleResourcesCostModel : CostModel where
  Cost := OracleResources
  instAddMonoid := inferInstance
  instPartialOrder := inferInstance
  instAddLeftMono :=
    ⟨fun fixed _left _right hle =>
      ⟨Nat.add_le_add_left hle.1 fixed.1,
        Nat.add_le_add_left hle.2 fixed.2⟩⟩
  instAddRightMono :=
    ⟨fun fixed _left _right hle =>
      ⟨Nat.add_le_add_right hle.1 fixed.1,
        Nat.add_le_add_right hle.2 fixed.2⟩⟩

/-- Every generic query has an explicit caller-side cost. -/
def resourceTwoQueryProgram :
    OracleProgram oracleResourcesCostModel testOracleSpec (ULift Bool) :=
  OracleProgram.bind
      (OracleProgram.query (2, 0) TestOracle.bit false) fun first =>
    OracleProgram.query (3, 0) TestOracle.bit first.down

/-- The implementation charges only the query-resource coordinate. -/
noncomputable def resourceCostedEnv :
    CostedOracleEnv oracleResourcesCostModel testOracleSpec where
  State := Nat
  init := 0
  query := fun name _sec state query =>
    match name with
    | TestOracle.bit => PMF.pure ⟨(!query, state + 1), (0, 1)⟩

theorem resourceCostedEnv_queryCostBound :
    resourceCostedEnv.QueryCostBound (fun _sec => (0, 1)) := by
  intro name sec state query result hresult
  cases name
  change Nat at state
  change Bool at query
  change CostedT oracleResourcesCostModel (Bool × Nat) at result
  simp only [resourceCostedEnv] at hresult
  have hresultEq :
      result =
        (⟨(!query, state + 1), (0, 1)⟩ :
          CostedT oracleResourcesCostModel (Bool × Nat)) :=
    (PMF.mem_support_pure_iff
      (⟨(!query, state + 1), (0, 1)⟩ :
        CostedT oracleResourcesCostModel (Bool × Nat)) result).1 hresult
  subst result
  exact le_refl _

theorem resourceTwoQueryProgram_costBound :
    OracleProgram.CostBound resourceTwoQueryProgram (5, 0) := by
  intro value profile execution
  unfold resourceTwoQueryProgram at execution
  cases execution with
  | bind firstExecution secondExecution =>
      cases firstExecution
      cases secondExecution
      exact le_refl _

theorem resourceTwoQueryProgram_totalQueryBound :
    OracleProgram.TotalQueryBound resourceTwoQueryProgram 2 := by
  intro value profile execution
  unfold resourceTwoQueryProgram at execution
  cases execution with
  | bind firstExecution secondExecution =>
      cases firstExecution
      cases secondExecution
      exact Nat.le_refl 2

theorem oracleResourcesCostExchange :
    OracleProgram.CostExchange oracleResourcesCostModel := by
  intro localLeft oracleLeft localRight oracleRight
  change (localLeft + oracleLeft) + (localRight + oracleRight) ≤
    (localLeft + localRight) + (oracleLeft + oracleRight)
  constructor
  · simp only [Prod.fst_add]
    omega
  · simp only [Prod.snd_add]
    omega

theorem oracleResources_repeatCost_mono :
    ∀ {left right : Nat}, left ≤ right →
      oracleResourcesCostModel.instPartialOrder.le
        (OracleProgram.repeatCost oracleResourcesCostModel left (0, 1))
        (OracleProgram.repeatCost oracleResourcesCostModel right (0, 1)) := by
  intro left right hle
  change (left * 0, left * 1) ≤ (right * 0, right * 1)
  constructor
  · exact Nat.le_refl 0
  · simpa using hle

/-- Generic coarse composition has the requested vector formula. -/
example
    (result : CostedT oracleResourcesCostModel (ULift Bool))
    (hresult :
      result ∈
        (OracleProgram.runCostedWithCostedEnv
          resourceTwoQueryProgram 0 resourceCostedEnv).support) :
    result.cost ≤ (5, 2) := by
  simpa using
    OracleProgram.runCostedWithCostedEnv_cost_le
      resourceTwoQueryProgram 0 resourceCostedEnv (5, 0) 2 (fun _sec => (0, 1))
      oracleResources_repeatCost_mono oracleResourcesCostExchange
      resourceTwoQueryProgram_costBound resourceTwoQueryProgram_totalQueryBound
      (resourceCostedEnv_queryCostBound.at 0) result hresult

/-- Generic erasure preserves the value distribution exactly. -/
example :
    RandCostedT.valueDist
        (OracleProgram.runCostedWithCostedEnv resourceTwoQueryProgram 0 resourceCostedEnv) =
      OracleProgram.runWithEnv resourceTwoQueryProgram 0 resourceCostedEnv.erase :=
  OracleProgram.valueDist_runCostedWithCostedEnv
    resourceTwoQueryProgram 0 resourceCostedEnv

/-! ## Noncommutative exact-order regression -/

inductive TraceEvent where
  | localFirst
  | oracleFirst
  | localSecond
  | oracleSecond
deriving DecidableEq, Repr

structure TraceCost where
  events : List TraceEvent
deriving DecidableEq, Repr

instance : Zero TraceCost := ⟨⟨[]⟩⟩

instance : Add TraceCost :=
  ⟨fun left right => ⟨left.events ++ right.events⟩⟩

instance : AddMonoid TraceCost where
  add_assoc left middle right := by
    cases left with | mk leftEvents =>
      cases middle with | mk middleEvents =>
        cases right with | mk rightEvents =>
          exact congrArg TraceCost.mk
            (List.append_assoc leftEvents middleEvents rightEvents)
  zero_add cost := by
    cases cost
    rfl
  add_zero cost := by
    cases cost with | mk events =>
      exact congrArg TraceCost.mk (List.append_nil events)
  nsmul := nsmulRec
  nsmul_zero _cost := rfl
  nsmul_succ _count _cost := rfl

instance : LE TraceCost where
  le left right := left = right

instance : PartialOrder TraceCost where
  le_refl := fun _ => rfl
  le_trans := by
    intro left middle right leftMiddle middleRight
    change left = middle at leftMiddle
    change middle = right at middleRight
    change left = right
    exact leftMiddle.trans middleRight
  le_antisymm := by
    intro left right leftRight _rightLeft
    change left = right at leftRight
    exact leftRight

instance : AddLeftMono TraceCost where
  elim := fun fixed _left _right leftRight =>
    congrArg (fun value => fixed + value) leftRight

instance : AddRightMono TraceCost where
  elim := fun fixed _left _right leftRight =>
    congrArg (fun value => value + fixed) leftRight

abbrev traceCostModel : CostModel where
  Cost := TraceCost
  instAddMonoid := inferInstance
  instPartialOrder := inferInstance
  instAddLeftMono := inferInstance
  instAddRightMono := inferInstance

def traceCost (event : TraceEvent) : TraceCost :=
  ⟨[event]⟩

def orderedTwoQueryProgram :
    OracleProgram traceCostModel testOracleSpec (ULift Bool) :=
  OracleProgram.bind
      (OracleProgram.query
        (traceCost .localFirst) TestOracle.bit false) fun first =>
    OracleProgram.query
      (traceCost .localSecond) TestOracle.bit first.down

noncomputable def orderedCostedEnv :
    CostedOracleEnv traceCostModel testOracleSpec where
  State := Bool
  init := false
  query := fun name _sec seenSecond query =>
    match name with
    | TestOracle.bit =>
        PMF.pure
          ⟨(!query, true),
            traceCost (if seenSecond then .oracleSecond else .oracleFirst)⟩

/-- Exact cost follows execution order, not grouped local/oracle order. -/
example :
    OracleProgram.runCostedWithCostedEnv
        orderedTwoQueryProgram 0 orderedCostedEnv =
      PMF.pure
        ⟨ULift.up false,
          ⟨[.localFirst, .oracleFirst, .localSecond, .oracleSecond]⟩⟩ := by
  simp only [OracleProgram.runCostedWithCostedEnv,
    OracleProgram.runProfiledWithCostedEnvFromInit,
    orderedTwoQueryProgram, orderedCostedEnv, traceCost,
    OracleProgram.runProfiledWithCostedEnv, PMF.pure_bind,
    Bool.not_false, Bool.not_true, Bool.false_eq_true, if_false, if_true]
  change PMF.map _ (PMF.bind (PMF.pure _) _) = _
  rw [PMF.pure_bind, PMF.pure_map]
  rfl

/-- The forbidden grouped order is observably different. -/
example :
    (⟨[.localFirst, .oracleFirst, .localSecond, .oracleSecond]⟩ : TraceCost) ≠
      ⟨[.localFirst, .localSecond, .oracleFirst, .oracleSecond]⟩ := by
  decide

end CryptoTest.Infrastructure.Computation.CostedOracle

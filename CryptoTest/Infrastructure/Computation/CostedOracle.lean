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
def twoQueryProgram : OracleProgram testOracleSpec (ULift Bool) :=
  OracleProgram.bind (OracleProgram.query TestOracle.bit false) fun first =>
    OracleProgram.query TestOracle.bit first.down

/-- The implementation negates its query and charges three internal units. -/
noncomputable def costedEnv : CostedOracleEnv testOracleSpec where
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
  change Costed (Bool × Nat) at result
  simp only [costedEnv] at hresult
  have hresultEq :
      result = (⟨(!query, state + 1), 3⟩ : Costed (Bool × Nat)) :=
    (PMF.mem_support_pure_iff
      (⟨(!query, state + 1), 3⟩ : Costed (Bool × Nat)) result).1 hresult
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
      (fun _sec => Unit)
      (fun _sec => Bool)
      (fun _sec _input => testOracleSpec) where
  run := fun _sec _input => twoQueryProgram
  runtime := fun _sec => 2
  queryBound := fun _sec _input _name => 2
  runtime_sound := by
    intro sec input
    exact twoQueryProgram_costBound
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
  runtime_isPoly := IsPolyBounded.const 2

/-- Optional polynomial total-query evidence for the existing PPT machine. -/
noncomputable def twoQueryPPTMachineTotalQueries :
    PolyTotalQueryBoundCertificate twoQueryPPTMachine where
  totalQueryBound := fun _sec => 2
  totalQueryBound_sound := by
    intro sec input
    exact twoQueryProgram_totalQueryBound
  totalQueryBound_isPoly := IsPolyBounded.const 2

/-- Two machine calls plus two three-unit oracle executions compose to eight. -/
example
    (result : Costed (ULift Bool))
    (hresult :
      result ∈
        (OracleProgram.runCostedWithCostedEnv
          twoQueryProgram 0 costedEnv).support) :
    result.cost ≤ 8 := by
  simpa using
    OracleProgram.runCostedWithCostedEnv_cost_le
      twoQueryProgram 0 costedEnv 2 2 (fun _sec => 3)
      twoQueryProgram_costBound twoQueryProgram_totalQueryBound
      (costedEnv_queryCostBound.at 0) result hresult

/-- Cost erasure still produces the ordinary stateful oracle semantics. -/
example :
    RandCosted.valueDist
        (OracleProgram.runCostedWithCostedEnv twoQueryProgram 0 costedEnv) =
      OracleProgram.runWithEnv twoQueryProgram 0 costedEnv.erase :=
  OracleProgram.valueDist_runCostedWithCostedEnv
    twoQueryProgram 0 costedEnv

/-- The machine-level bridge exposes the same eight-unit composed bound. -/
example
    (result : Costed Bool)
    (hresult :
      result ∈
        (twoQueryPPTMachine.toProbabilisticOracleMachine
          |>.runCostedWithCostedEnv 0 () costedEnv).support) :
    result.cost ≤ 8 := by
  simpa using
    twoQueryPPTMachine.toTimedOracleMachine
      |>.runCostedWithCostedEnv_cost_le_composed
        twoQueryPPTMachineTotalQueries.toTotalQueryBoundCertificate
        0 () costedEnv (fun _sec => 3)
        (costedEnv_queryCostBound.at 0) result hresult

/-- The composed machine/oracle runtime remains polynomially bounded. -/
example :
    IsPolyBounded
      (fun sec =>
        twoQueryPPTMachine.runtime sec +
          twoQueryPPTMachineTotalQueries.totalQueryBound sec * 3) :=
  twoQueryPPTMachine.composedRuntime_isPoly
    twoQueryPPTMachineTotalQueries
    (fun _sec => 3) (IsPolyBounded.const 3)

/-- Explicit zero local work is available only in the generic Nat syntax. -/
def zeroLocalCostQueryProgramT :
    OracleProgramT natCostModel testOracleSpec (ULift Bool) :=
  OracleProgramT.queryWithCost
    (M := natCostModel) (0 : Nat) TestOracle.bit false

theorem zeroLocalCostQueryProgramT_costBound :
    OracleProgramT.CostBound zeroLocalCostQueryProgramT 0 := by
  intro value profile execution
  cases execution
  exact Nat.le_refl 0

theorem zeroLocalCostQueryProgramT_totalQueryBound :
    OracleProgramT.TotalQueryBound zeroLocalCostQueryProgramT 1 := by
  intro value profile execution
  cases execution
  exact Nat.le_refl 1

/-- The legacy Nat environment certificate also supplies the generic Nat core. -/
theorem costedEnv_queryCostBoundT :
    CostedOracleEnvT.QueryCostBound costedEnv (fun _sec => 3) :=
  costedEnv_queryCostBound

/-- Generic query count, rather than zero local cost, pays for oracle work. -/
example
    (result : CostedT natCostModel (ULift Bool))
    (hresult :
      result ∈
        (OracleProgramT.runCostedWithCostedEnv
          zeroLocalCostQueryProgramT 0 costedEnv).support) :
    result.cost ≤ 3 := by
  simpa only [OracleProgramT.repeatCost_nat] using
    OracleProgramT.runCostedWithCostedEnv_cost_le
      zeroLocalCostQueryProgramT 0 costedEnv 0 1 (fun _sec => 3)
      (OracleProgramT.repeatCost_nat_mono 3)
      OracleProgramT.costExchange_nat
      zeroLocalCostQueryProgramT_costBound
      zeroLocalCostQueryProgramT_totalQueryBound
      (CostedOracleEnvT.QueryCostBound.at costedEnv_queryCostBoundT 0)
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
def twoQueryProgramT :
    OracleProgramT oracleResourcesCostModel testOracleSpec (ULift Bool) :=
  OracleProgramT.bind
      (OracleProgramT.queryWithCost (2, 0) TestOracle.bit false) fun first =>
    OracleProgramT.queryWithCost (3, 0) TestOracle.bit first.down

/-- The implementation charges only the query-resource coordinate. -/
noncomputable def costedEnvT :
    CostedOracleEnvT oracleResourcesCostModel testOracleSpec where
  State := Nat
  init := 0
  query := fun name _sec state query =>
    match name with
    | TestOracle.bit => PMF.pure ⟨(!query, state + 1), (0, 1)⟩

theorem costedEnvT_queryCostBound :
    costedEnvT.QueryCostBound (fun _sec => (0, 1)) := by
  intro name sec state query result hresult
  cases name
  change Nat at state
  change Bool at query
  change CostedT oracleResourcesCostModel (Bool × Nat) at result
  simp only [costedEnvT] at hresult
  have hresultEq :
      result =
        (⟨(!query, state + 1), (0, 1)⟩ :
          CostedT oracleResourcesCostModel (Bool × Nat)) :=
    (PMF.mem_support_pure_iff
      (⟨(!query, state + 1), (0, 1)⟩ :
        CostedT oracleResourcesCostModel (Bool × Nat)) result).1 hresult
  subst result
  exact le_refl _

theorem twoQueryProgramT_costBound :
    OracleProgramT.CostBound twoQueryProgramT (5, 0) := by
  intro value profile execution
  unfold twoQueryProgramT at execution
  cases execution with
  | bind firstExecution secondExecution =>
      cases firstExecution
      cases secondExecution
      exact le_refl _

theorem twoQueryProgramT_totalQueryBound :
    OracleProgramT.TotalQueryBound twoQueryProgramT 2 := by
  intro value profile execution
  unfold twoQueryProgramT at execution
  cases execution with
  | bind firstExecution secondExecution =>
      cases firstExecution
      cases secondExecution
      exact Nat.le_refl 2

theorem oracleResourcesCostExchange :
    OracleProgramT.CostExchange oracleResourcesCostModel := by
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
        (OracleProgramT.repeatCost oracleResourcesCostModel left (0, 1))
        (OracleProgramT.repeatCost oracleResourcesCostModel right (0, 1)) := by
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
        (OracleProgramT.runCostedWithCostedEnv
          twoQueryProgramT 0 costedEnvT).support) :
    result.cost ≤ (5, 2) := by
  simpa using
    OracleProgramT.runCostedWithCostedEnv_cost_le
      twoQueryProgramT 0 costedEnvT (5, 0) 2 (fun _sec => (0, 1))
      oracleResources_repeatCost_mono oracleResourcesCostExchange
      twoQueryProgramT_costBound twoQueryProgramT_totalQueryBound
      (costedEnvT_queryCostBound.at 0) result hresult

/-- Generic erasure preserves the value distribution exactly. -/
example :
    RandCostedT.valueDist
        (OracleProgramT.runCostedWithCostedEnv twoQueryProgramT 0 costedEnvT) =
      OracleProgramT.runWithEnv twoQueryProgramT 0 costedEnvT.erase :=
  OracleProgramT.valueDist_runCostedWithCostedEnv
    twoQueryProgramT 0 costedEnvT

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
    OracleProgramT traceCostModel testOracleSpec (ULift Bool) :=
  OracleProgramT.bind
      (OracleProgramT.queryWithCost
        (traceCost .localFirst) TestOracle.bit false) fun first =>
    OracleProgramT.queryWithCost
      (traceCost .localSecond) TestOracle.bit first.down

noncomputable def orderedCostedEnv :
    CostedOracleEnvT traceCostModel testOracleSpec where
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
    OracleProgramT.runCostedWithCostedEnv
        orderedTwoQueryProgram 0 orderedCostedEnv =
      PMF.pure
        ⟨ULift.up false,
          ⟨[.localFirst, .oracleFirst, .localSecond, .oracleSecond]⟩⟩ := by
  simp only [OracleProgramT.runCostedWithCostedEnv,
    OracleProgramT.runProfiledWithCostedEnvFromInit,
    orderedTwoQueryProgram, orderedCostedEnv, traceCost,
    OracleProgramT.runProfiledWithCostedEnv, PMF.pure_bind,
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

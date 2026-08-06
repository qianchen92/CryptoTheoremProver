import Crypto.Infrastructure.Computation.Oracle.Handler
import Crypto.Infrastructure.Computation.Oracle.Program
import Crypto.Infrastructure.Computation.Oracle.Trace
import Mathlib.Probability.ProbabilityMassFunction.Monad

namespace Crypto.Infrastructure.Computation.Oracle

open Crypto.Infrastructure.Computation.Algebra
open Crypto.Infrastructure.Computation.Cost

universe uCost uOracle uQuery uResponse uState uStateLeft uStateRight uValue uObserved

/--
The result of the sole structural oracle-program interpreter.

`totalCost` preserves the exact issue/environment order.  `localCost` and
`oracleCost` are separate audit projections and are not asserted to regroup to
`totalCost` in a noncommutative model.
-/
structure ExactRunResult
    (M : CostModel.{uCost})
    (Spec : OracleSpec.{uOracle, uQuery, uResponse})
    (State : Type uState) (α : Type (max uValue uResponse)) where
  value : α
  state : State
  trace : QueryTrace Spec
  localCost : M.Cost
  oracleCost : M.Cost
  totalCost : M.Cost

namespace Program

variable {M : CostModel.{uCost}}
variable {Spec : OracleSpec.{uOracle, uQuery, uResponse}}
variable {issueAlgebra : CostedAlgebra M (QueryIssue.signature Spec)}

section ExactRun

variable {α : Type (max uValue uResponse)}

/--
Interpret one oracle program exactly against an exact-cost environment.

This is the only structural recursion over `Program`.  Every public semantic,
trace, and cost view below is a projection or erasure of this distribution.
-/
noncomputable def runExact
    {α : Type (max uValue uResponse)} (program : Program issueAlgebra α)
    (sec : Crypto.SecPar)
    (env : CostedOracleEnv.{uCost, uOracle, uQuery, uResponse, uState} M Spec)
    (state : env.State) : PMF (ExactRunResult M Spec env.State α) := by
  letI := M.instAddMonoid
  exact
    match program with
    | .pure value =>
        PMF.pure ⟨value, state, QueryTrace.empty Spec, 0, 0, 0⟩
    | .bind first next =>
        PMF.bind (runExact first sec env state) fun firstResult =>
          PMF.bind (runExact (next firstResult.value) sec env firstResult.state)
            fun nextResult =>
              PMF.pure
                ⟨nextResult.value, nextResult.state,
                  QueryTrace.append firstResult.trace nextResult.trace,
                  firstResult.localCost + nextResult.localCost,
                  firstResult.oracleCost + nextResult.oracleCost,
                  firstResult.totalCost + nextResult.totalCost⟩
    | .liftCosted dist =>
        PMF.bind dist fun result =>
          PMF.pure
            ⟨result.val, state, QueryTrace.empty Spec,
              result.cost, 0, result.cost⟩
    | .query name oracleQuery =>
        PMF.bind (issueAlgebra.exec (.issue name oracleQuery)) fun issueResult =>
          PMF.bind (env.query name sec state oracleQuery) fun oracleResult =>
            PMF.pure
              ⟨ULift.up oracleResult.val.1, oracleResult.val.2,
                QueryTrace.singleton name,
                issueResult.cost, oracleResult.cost,
                issueResult.cost + oracleResult.cost⟩

/-- Run the exact interpreter from the environment's initial state. -/
noncomputable def runExactFromInit
    (program : Program issueAlgebra α)
    (sec : Crypto.SecPar)
    (env : CostedOracleEnv.{uCost, uOracle, uQuery, uResponse, uState} M Spec) :
    PMF (ExactRunResult M Spec env.State α) :=
  runExact program sec env env.init

/-- Retain only the returned value and exact ordered total cost. -/
noncomputable def runCosted
    (program : Program issueAlgebra α)
    (sec : Crypto.SecPar)
    (env : CostedOracleEnv.{uCost, uOracle, uQuery, uResponse, uState} M Spec) :
    RandCosted M α :=
  PMF.map (fun result => ⟨result.value, result.totalCost⟩)
    (runExactFromInit program sec env)

/-- Erase all costs and the final state from an exact environment execution. -/
noncomputable def runWithCostedEnv
    (program : Program issueAlgebra α)
    (sec : Crypto.SecPar)
    (env : CostedOracleEnv.{uCost, uOracle, uQuery, uResponse, uState} M Spec) :
    PMF α :=
  PMF.map ExactRunResult.value (runExactFromInit program sec env)

/-- Ordinary oracle semantics is exact execution against the zero-cost lift. -/
noncomputable def runWithEnv
    (program : Program issueAlgebra α)
    (sec : Crypto.SecPar)
    (env : OracleEnv.{uOracle, uQuery, uResponse, uState} Spec) : PMF α :=
  runWithCostedEnv program sec (env.zeroCost M)

/-- Retain the returned value and final semantic-environment state while
erasing costs and traces. This is a projection of `runExact`, not a second
interpreter. -/
noncomputable def runValueState
    (program : Program issueAlgebra α)
    (sec : Crypto.SecPar)
    (env : OracleEnv.{uOracle, uQuery, uResponse, uState} Spec)
    (state : env.State) : PMF (α × env.State) :=
  PMF.map (fun result => (result.value, result.state))
    (runExact program sec (env.zeroCost M) state)

/-- Ordinary value semantics started from an explicit semantic-environment
state. -/
noncomputable def runWithEnvFromState
    (program : Program issueAlgebra α)
    (sec : Crypto.SecPar)
    (env : OracleEnv.{uOracle, uQuery, uResponse, uState} Spec)
    (state : env.State) : PMF α :=
  PMF.map Prod.fst (runValueState program sec env state)

@[simp] theorem runWithEnvFromState_init
    (program : Program issueAlgebra α)
    (sec : Crypto.SecPar)
    (env : OracleEnv.{uOracle, uQuery, uResponse, uState} Spec) :
    runWithEnvFromState program sec env env.init = runWithEnv program sec env := by
  simp only [runWithEnvFromState, runValueState, runWithEnv, runWithCostedEnv,
    runExactFromInit, PMF.map_comp]
  rfl

/-- Retain returned values and query traces while erasing all costs. -/
noncomputable def runTraceWithCostedEnv
    (program : Program issueAlgebra α)
    (sec : Crypto.SecPar)
    (env : CostedOracleEnv.{uCost, uOracle, uQuery, uResponse, uState} M Spec) :
    PMF (α × QueryTrace Spec) :=
  PMF.map (fun result => (result.value, result.trace))
    (runExactFromInit program sec env)

/-- Ordinary value/trace semantics is exact execution against the zero-cost lift. -/
noncomputable def runTrace
    (program : Program issueAlgebra α)
    (sec : Crypto.SecPar)
    (env : OracleEnv.{uOracle, uQuery, uResponse, uState} Spec) :
    PMF (α × QueryTrace Spec) :=
  runTraceWithCostedEnv program sec (env.zeroCost M)

/-- Erasing the exact total cost recovers the value projection of the same run. -/
@[simp] theorem valueDist_runCosted
    (program : Program issueAlgebra α)
    (sec : Crypto.SecPar)
    (env : CostedOracleEnv.{uCost, uOracle, uQuery, uResponse, uState} M Spec) :
    RandCosted.valueDist (runCosted program sec env) =
      runWithCostedEnv program sec env := by
  simp only [RandCosted.valueDist, runCosted, runWithCostedEnv,
    runExactFromInit, PMF.map_comp]
  rfl

end ExactRun

/-- Binding a costed distribution through a value-only continuation erases cost. -/
private theorem bind_value_only
    {α : Type uValue} {β : Type uObserved}
    (dist : RandCosted M α) (continuation : α → PMF β) :
    PMF.bind dist (fun result => continuation result.val) =
      PMF.bind (RandCosted.valueDist dist) continuation := by
  simpa only [Function.comp_apply] using
    (PMF.bind_map dist Costed.val continuation).symm

@[simp] theorem runValueState_pure
    {α : Type (max uValue uResponse)}
    (value : α) (sec : Crypto.SecPar)
    (env : OracleEnv.{uOracle, uQuery, uResponse, uState} Spec)
    (state : env.State) :
    runValueState (.pure value : Program issueAlgebra α) sec env state =
      PMF.pure (value, state) := by
  simp only [runValueState, runExact]
  rw [PMF.pure_map]

@[simp] theorem runValueState_bind
    {α β : Type (max uValue uResponse)}
    (first : Program issueAlgebra α)
    (next : α → Program issueAlgebra β)
    (sec : Crypto.SecPar)
    (env : OracleEnv.{uOracle, uQuery, uResponse, uState} Spec)
    (state : env.State) :
    runValueState (.bind first next) sec env state =
      PMF.bind (runValueState first sec env state) fun firstResult =>
        runValueState (next firstResult.1) sec env firstResult.2 := by
  simp only [runValueState, runExact]
  rw [PMF.map_bind, PMF.bind_map]
  congr 1
  funext firstResult
  simp only [Function.comp_apply]
  rw [PMF.map_bind]
  congr 1
  funext nextResult
  rw [PMF.pure_map]
  rfl

@[simp] theorem runValueState_liftCosted
    {α : Type (max uValue uResponse)}
    (dist : RandCosted M α)
    (sec : Crypto.SecPar)
    (env : OracleEnv.{uOracle, uQuery, uResponse, uState} Spec)
    (state : env.State) :
    runValueState (.liftCosted dist : Program issueAlgebra α) sec env state =
      PMF.bind (RandCosted.valueDist dist) fun value =>
        PMF.pure (value, state) := by
  simp only [runValueState, runExact, RandCosted.valueDist]
  rw [PMF.map_bind, PMF.bind_map]
  congr 1
  funext result
  simp only [Function.comp_apply]
  rw [PMF.pure_map]

@[simp] theorem runValueState_query
    (name : Spec.Name) (query : Spec.Query name)
    (sec : Crypto.SecPar)
    (env : OracleEnv.{uOracle, uQuery, uResponse, uState} Spec)
    (state : env.State) :
    runValueState (.query name query : Program issueAlgebra
        (ULift.{uValue} (Spec.Response name))) sec env state =
      PMF.bind (env.query name sec state query) fun result =>
        PMF.pure (ULift.up result.1, result.2) := by
  simp only [runValueState, runExact, PMF.map_bind, PMF.pure_map]
  let continuation : Spec.Response name × env.State →
      PMF (ULift.{uValue} (Spec.Response name) × env.State) :=
    fun result => PMF.pure (ULift.up result.1, result.2)
  calc
    PMF.bind (issueAlgebra.exec (.issue name query)) (fun _issueResult =>
        PMF.bind ((env.zeroCost M).query name sec state query)
          (fun oracleResult => continuation oracleResult.val)) =
      PMF.bind (issueAlgebra.exec (.issue name query)) (fun _issueResult =>
        PMF.bind
          (RandCosted.valueDist
            ((env.zeroCost M).query name sec state query)) continuation) := by
            congr 1
            funext issueResult
            exact bind_value_only
              ((env.zeroCost M).query name sec state query) continuation
    _ = PMF.bind (issueAlgebra.exec (.issue name query)) (fun _issueResult =>
        PMF.bind (env.query name sec state query) continuation) := by
          simp only [OracleEnv.zeroCost]
          rw [RandCosted.valueDist_sampleZeroCost]
    _ = PMF.bind (env.query name sec state query) continuation :=
      PMF.bind_const _ _

/-- A probabilistic relation between environment states is preserved by every
oracle program when every query preserves that relation. -/
theorem runValueState_eq_of_stateSimulation
    (left : OracleEnv.{uOracle, uQuery, uResponse, uStateLeft} Spec)
    (right : OracleEnv.{uOracle, uQuery, uResponse, uStateRight} Spec)
    (stateSimulation : left.State → PMF right.State)
    (querySimulation : ∀ (name : Spec.Name) (querySec : Crypto.SecPar)
        (state : left.State) (query : Spec.Query name),
      (PMF.bind (left.query name querySec state query) fun result =>
          PMF.bind (stateSimulation result.2) fun simulatedState =>
            PMF.pure (result.1, simulatedState)) =
        PMF.bind (stateSimulation state) fun simulatedState =>
          right.query name querySec simulatedState query)
    {α : Type (max uValue uResponse)}
    (program : Program issueAlgebra α)
    (sec : Crypto.SecPar) (state : left.State) :
    (PMF.bind (runValueState program sec left state) fun result =>
        PMF.bind (stateSimulation result.2) fun simulatedState =>
          PMF.pure (result.1, simulatedState)) =
      PMF.bind (stateSimulation state) fun simulatedState =>
        runValueState program sec right simulatedState := by
  induction program generalizing state with
  | pure value =>
      simp only [runValueState_pure, PMF.pure_bind]
  | bind first next ihFirst ihNext =>
      simp only [runValueState_bind, PMF.bind_bind]
      calc
        PMF.bind (runValueState first sec left state) (fun firstResult =>
            PMF.bind (runValueState (next firstResult.1) sec left firstResult.2)
              (fun nextResult =>
                PMF.bind (stateSimulation nextResult.2) fun simulatedState =>
                  PMF.pure (nextResult.1, simulatedState))) =
          PMF.bind (runValueState first sec left state) (fun firstResult =>
            PMF.bind (stateSimulation firstResult.2) fun simulatedState =>
              runValueState (next firstResult.1) sec right simulatedState) := by
                congr 1
                funext firstResult
                exact ihNext firstResult.1 firstResult.2
        _ = PMF.bind
            (PMF.bind (runValueState first sec left state) fun firstResult =>
              PMF.bind (stateSimulation firstResult.2) fun simulatedState =>
                PMF.pure (firstResult.1, simulatedState))
            (fun firstResult =>
              runValueState (next firstResult.1) sec right firstResult.2) := by
                simp only [PMF.bind_bind, PMF.pure_bind]
        _ = PMF.bind
            (PMF.bind (stateSimulation state) fun simulatedState =>
              runValueState first sec right simulatedState)
            (fun firstResult =>
              runValueState (next firstResult.1) sec right firstResult.2) := by
                rw [ihFirst state]
        _ = PMF.bind (stateSimulation state) fun simulatedState =>
            PMF.bind (runValueState first sec right simulatedState) fun firstResult =>
              runValueState (next firstResult.1) sec right firstResult.2 := by
                rw [PMF.bind_bind]
  | liftCosted dist =>
      simp only [runValueState_liftCosted, PMF.bind_bind, PMF.pure_bind]
      exact PMF.bind_comm _ _ _
  | query name query =>
      simp only [runValueState_query, PMF.bind_bind, PMF.pure_bind]
      have hquery := querySimulation name sec state query
      have hmapped := congrArg
        (PMF.map (fun result => (ULift.up result.1, result.2))) hquery
      simpa only [PMF.map_bind, PMF.pure_map] using hmapped

/-- State simulation yields equality of ordinary value semantics from every
source state. -/
theorem runWithEnvFromState_eq_of_stateSimulation
    (left : OracleEnv.{uOracle, uQuery, uResponse, uStateLeft} Spec)
    (right : OracleEnv.{uOracle, uQuery, uResponse, uStateRight} Spec)
    (stateSimulation : left.State → PMF right.State)
    (querySimulation : ∀ (name : Spec.Name) (querySec : Crypto.SecPar)
        (state : left.State) (query : Spec.Query name),
      (PMF.bind (left.query name querySec state query) fun result =>
          PMF.bind (stateSimulation result.2) fun simulatedState =>
            PMF.pure (result.1, simulatedState)) =
        PMF.bind (stateSimulation state) fun simulatedState =>
          right.query name querySec simulatedState query)
    {α : Type (max uValue uResponse)}
    (program : Program issueAlgebra α)
    (sec : Crypto.SecPar) (state : left.State) :
    runWithEnvFromState program sec left state =
      PMF.bind (stateSimulation state) fun simulatedState =>
        runWithEnvFromState program sec right simulatedState := by
  have hsimulation := runValueState_eq_of_stateSimulation left right
    stateSimulation querySimulation program sec state
  have hmapped := congrArg (PMF.map Prod.fst) hsimulation
  simpa only [runWithEnvFromState, PMF.map_bind, PMF.pure_map,
    PMF.bind_const] using hmapped

variable {α : Type (max uValue uResponse)}

/--
Replacing a costed environment by the zero-cost lift of its erasure preserves
every value, final-state, and query-trace continuation.
-/
theorem bind_runExact_erase
    {β : Type uObserved}
    (program : Program issueAlgebra α) (sec : Crypto.SecPar)
    (env : CostedOracleEnv.{uCost, uOracle, uQuery, uResponse, uState} M Spec)
    (state : env.State)
    (continuation : α → env.State → QueryTrace Spec → PMF β) :
    PMF.bind (runExact program sec env state)
        (fun result => continuation result.value result.state result.trace) =
      PMF.bind (runExact program sec (env.erase.zeroCost M) state)
        (fun result => continuation result.value result.state result.trace) := by
  induction program generalizing state with
  | pure value =>
      simp [runExact]
  | bind first next ihFirst ihNext =>
      simp only [runExact, PMF.bind_bind, PMF.pure_bind]
      calc
        PMF.bind (runExact first sec env state)
            (fun firstResult =>
              PMF.bind
                (runExact (next firstResult.value) sec env firstResult.state)
                (fun nextResult =>
                  continuation nextResult.value nextResult.state
                    (QueryTrace.append firstResult.trace nextResult.trace))) =
          PMF.bind (runExact first sec env state)
            (fun firstResult =>
              PMF.bind
                (runExact (next firstResult.value) sec
                  (env.erase.zeroCost M) firstResult.state)
                (fun nextResult =>
                  continuation nextResult.value nextResult.state
                    (QueryTrace.append firstResult.trace nextResult.trace))) := by
              congr 1
              funext firstResult
              exact ihNext firstResult.value firstResult.state
                (fun value nextState nextTrace =>
                  continuation value nextState
                    (QueryTrace.append firstResult.trace nextTrace))
        _ =
          PMF.bind (runExact first sec (env.erase.zeroCost M) state)
            (fun firstResult =>
              PMF.bind
                (runExact (next firstResult.value) sec
                  (env.erase.zeroCost M) firstResult.state)
                (fun nextResult =>
                  continuation nextResult.value nextResult.state
                    (QueryTrace.append firstResult.trace nextResult.trace))) := by
              exact ihFirst state
                (fun firstValue firstState firstTrace =>
                  PMF.bind
                    (runExact (next firstValue) sec
                      (env.erase.zeroCost M) firstState)
                    (fun nextResult =>
                      continuation nextResult.value nextResult.state
                        (QueryTrace.append firstTrace nextResult.trace)))
  | liftCosted dist =>
      simp [runExact, PMF.bind_bind]
  | query name oracleQuery =>
      simp only [runExact, PMF.bind_bind, PMF.pure_bind]
      congr 1
      funext issueResult
      let continueQuery : Spec.Response name × env.State → PMF β :=
        fun oracleResult =>
          continuation (ULift.up oracleResult.1) oracleResult.2
            (QueryTrace.singleton name)
      calc
        PMF.bind (env.query name sec state oracleQuery)
            (fun oracleResult => continueQuery oracleResult.val) =
          PMF.bind
            (RandCosted.valueDist (env.query name sec state oracleQuery))
            continueQuery :=
              bind_value_only (env.query name sec state oracleQuery) continueQuery
        _ =
          PMF.bind
            (RandCosted.valueDist
              ((env.erase.zeroCost M).query name sec state oracleQuery))
            continueQuery := by
              change
                PMF.bind
                    (RandCosted.valueDist
                      (env.query name sec state oracleQuery)) continueQuery =
                  PMF.bind
                    (RandCosted.valueDist
                      (RandCosted.sampleZeroCost M
                        (RandCosted.valueDist
                          (env.query name sec state oracleQuery))))
                    continueQuery
              apply congrArg (fun dist => PMF.bind dist continueQuery)
              exact
                (RandCosted.valueDist_sampleZeroCost M
                  (RandCosted.valueDist
                    (env.query name sec state oracleQuery))).symm
        _ =
          PMF.bind ((env.erase.zeroCost M).query name sec state oracleQuery)
            (fun oracleResult => continueQuery oracleResult.val) :=
              (bind_value_only
                ((env.erase.zeroCost M).query name sec state oracleQuery)
                continueQuery).symm

/-- Erasing internal environment costs preserves the program's value distribution. -/
@[simp] theorem runWithCostedEnv_eq_runWithEnv_erase
    (program : Program issueAlgebra α)
    (sec : Crypto.SecPar)
    (env : CostedOracleEnv.{uCost, uOracle, uQuery, uResponse, uState} M Spec) :
    runWithCostedEnv program sec env = runWithEnv program sec env.erase := by
  simpa only [runWithCostedEnv, runWithEnv, runExactFromInit,
    PMF.bind_pure_comp, Function.comp_apply] using
      bind_runExact_erase program sec env env.init
        (fun value _state _trace => PMF.pure value)

/-- The public exact-cost execution erases to ordinary environment semantics. -/
@[simp] theorem valueDist_runCosted_eq_runWithEnv_erase
    (program : Program issueAlgebra α)
    (sec : Crypto.SecPar)
    (env : CostedOracleEnv.{uCost, uOracle, uQuery, uResponse, uState} M Spec) :
    RandCosted.valueDist (runCosted program sec env) =
      runWithEnv program sec env.erase := by
  rw [valueDist_runCosted, runWithCostedEnv_eq_runWithEnv_erase]

end Program

end Crypto.Infrastructure.Computation.Oracle

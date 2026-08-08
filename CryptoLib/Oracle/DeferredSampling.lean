import CryptoLib.Oracle.Interpreter

namespace CryptoLib.Oracle.OracleEnv

open CryptoLib.Core.Infrastructure.Computation.Cost

universe uCost uOracle uQuery uResponse uSeed uState uValue

variable {M : CostModel.{uCost}}
variable {Spec : OracleSpec.{uOracle, uQuery, uResponse}}
variable {issueCost : (name : Spec.Name) → Spec.Query name → M.Cost}

/-- Fix the hidden seed used by a common-state oracle implementation. -/
noncomputable def withFixedSeed
    {Seed : Type uSeed} {State : Type uState}
    (initialState : State)
    (query : Seed → (name : Spec.Name) → CryptoLib.Core.SecPar → State →
      Spec.Query name → PMF (Spec.Response name × State))
    (seed : Seed) : OracleEnv Spec where
  State := State
  init := initialState
  query := query seed

/-- Sample a hidden seed only when the oracle receives its first query. -/
noncomputable def withDeferredSeed
    {Seed : Type uSeed} {State : Type uState}
    (seedDist : PMF Seed) (initialState : State)
    (query : Seed → (name : Spec.Name) → CryptoLib.Core.SecPar → State →
      Spec.Query name → PMF (Spec.Response name × State)) :
    OracleEnv Spec where
  State := Option (Seed × State)
  init := none
  query := fun name sec state oracleQuery =>
    match state with
    | none =>
        PMF.bind seedDist fun seed =>
          PMF.map (fun result => (result.1, some (seed, result.2)))
            (query seed name sec initialState oracleQuery)
    | some (seed, currentState) =>
        PMF.map (fun result => (result.1, some (seed, result.2)))
          (query seed name sec currentState oracleQuery)

private noncomputable def withMaterializedSeed
    {Seed : Type uSeed} [Nonempty Seed] {State : Type uState}
    (initialState : State)
    (query : Seed → (name : Spec.Name) → CryptoLib.Core.SecPar → State →
      Spec.Query name → PMF (Spec.Response name × State)) :
    OracleEnv Spec where
  State := Seed × State
  init := (Classical.choice inferInstance, initialState)
  query := fun name sec state oracleQuery =>
    PMF.map (fun result => (result.1, (state.1, result.2)))
      (query state.1 name sec state.2 oracleQuery)

private noncomputable def materializeSeed
    {Seed : Type uSeed} {State : Type uState}
    (seedDist : PMF Seed) (initialState : State) :
    Option (Seed × State) → PMF (Seed × State)
  | none => PMF.map (fun seed => (seed, initialState)) seedDist
  | some state => PMF.pure state

/-- Deferring an independent hidden seed until the first oracle query preserves
the value distribution of every adaptive oracle program. -/
theorem runWithEnv_withDeferredSeed
    {Seed : Type uSeed} [Nonempty Seed] {State : Type uState}
    (seedDist : PMF Seed) (initialState : State)
    (query : Seed → (name : Spec.Name) → CryptoLib.Core.SecPar → State →
      Spec.Query name → PMF (Spec.Response name × State))
    {α : Type (max uValue uResponse)}
    (program : Program issueCost α) (sec : CryptoLib.Core.SecPar) :
    Program.runWithEnv program sec
        (withDeferredSeed seedDist initialState query) =
      PMF.bind seedDist fun seed =>
        Program.runWithEnv program sec
          (withFixedSeed initialState query seed) := by
  let deferred := withDeferredSeed seedDist initialState query
  let materialized := withMaterializedSeed initialState query
  let simulation : deferred.State → PMF materialized.State :=
    materializeSeed seedDist initialState
  have querySimulation : ∀ (name : Spec.Name) (querySec : CryptoLib.Core.SecPar)
      (state : deferred.State) (oracleQuery : Spec.Query name),
      (PMF.bind (deferred.query name querySec state oracleQuery) fun result =>
          PMF.bind (simulation result.2) fun simulatedState =>
            PMF.pure (result.1, simulatedState)) =
        PMF.bind (simulation state) fun simulatedState =>
          materialized.query name querySec simulatedState oracleQuery := by
    intro name querySec state oracleQuery
    cases state with
    | none =>
        simp [deferred, materialized, simulation, withDeferredSeed,
          withMaterializedSeed, materializeSeed, PMF.bind_map,
          PMF.bind_bind, Function.comp_def]
        congr 1
    | some state =>
        rcases state with ⟨seed, currentState⟩
        simp [deferred, materialized, simulation, withDeferredSeed,
          withMaterializedSeed, materializeSeed, PMF.bind_map,
          Function.comp_def]
        simpa only [Function.comp_apply] using
          PMF.bind_pure_comp
            (fun result => (result.1, seed, result.2))
            (query seed name querySec currentState oracleQuery)
  have hdeferred := Program.runWithEnvFromState_eq_of_stateSimulation
    deferred materialized simulation querySimulation program sec deferred.init
  rw [Program.runWithEnvFromState_init] at hdeferred
  change Program.runWithEnv program sec
      (withDeferredSeed seedDist initialState query) = _ at hdeferred
  rw [hdeferred]
  change
    PMF.bind (PMF.map (fun seed => (seed, initialState)) seedDist)
        (fun simulatedState =>
          Program.runWithEnvFromState program sec materialized simulatedState) = _
  rw [PMF.bind_map]
  congr 1
  funext seed
  let fixed := withFixedSeed initialState query seed
  let fixedSimulation : fixed.State → PMF materialized.State :=
    fun state => PMF.pure (seed, state)
  have fixedQuerySimulation : ∀ (name : Spec.Name)
      (querySec : CryptoLib.Core.SecPar) (state : fixed.State)
      (oracleQuery : Spec.Query name),
      (PMF.bind (fixed.query name querySec state oracleQuery) fun result =>
          PMF.bind (fixedSimulation result.2) fun simulatedState =>
            PMF.pure (result.1, simulatedState)) =
        PMF.bind (fixedSimulation state) fun simulatedState =>
          materialized.query name querySec simulatedState oracleQuery := by
    intro name querySec state oracleQuery
    simp only [fixed, fixedSimulation, materialized, withFixedSeed,
      withMaterializedSeed, PMF.pure_bind]
    simpa only [Function.comp_apply] using
      PMF.bind_pure_comp
        (fun result => (result.1, seed, result.2))
        (query seed name querySec state oracleQuery)
  have hfixed := Program.runWithEnvFromState_eq_of_stateSimulation
    fixed materialized fixedSimulation fixedQuerySimulation
      program sec fixed.init
  rw [Program.runWithEnvFromState_init] at hfixed
  simpa only [fixed, fixedSimulation, withFixedSeed, PMF.pure_bind] using
    hfixed.symm

/-- Fix the hidden seed used by a one-query oracle. -/
noncomputable def withFixedOneShotSeed
    {Seed : Type uSeed}
    (answer : Seed → (name : Spec.Name) → CryptoLib.Core.SecPar →
      Spec.Query name → PMF (Spec.Response name))
    (after : (name : Spec.Name) → CryptoLib.Core.SecPar →
      Spec.Query name → PMF (Spec.Response name))
    (seed : Seed) : OracleEnv Spec where
  State := Bool
  init := false
  query := fun name sec used query =>
    PMF.map (fun response => (response, true))
      (if used then after name sec query else answer seed name sec query)

/-- Sample the hidden seed when a one-query oracle receives its first query. -/
noncomputable def withLazyOneShotSeed
    {Seed : Type uSeed}
    (seedDist : PMF Seed)
    (answer : Seed → (name : Spec.Name) → CryptoLib.Core.SecPar →
      Spec.Query name → PMF (Spec.Response name))
    (after : (name : Spec.Name) → CryptoLib.Core.SecPar →
      Spec.Query name → PMF (Spec.Response name)) :
    OracleEnv Spec where
  State := Bool
  init := false
  query := fun name sec used query =>
    if used then
      PMF.map (fun response => (response, true)) (after name sec query)
    else
      PMF.bind seedDist fun seed =>
        PMF.map (fun response => (response, true)) (answer seed name sec query)

private noncomputable def withDeferredOneShotSeed
    {Seed : Type uSeed}
    (seedDist : PMF Seed)
    (answer : Seed → (name : Spec.Name) → CryptoLib.Core.SecPar →
      Spec.Query name → PMF (Spec.Response name))
    (after : (name : Spec.Name) → CryptoLib.Core.SecPar →
      Spec.Query name → PMF (Spec.Response name)) :
    OracleEnv Spec where
  State := Option Seed
  init := none
  query := fun name sec state query =>
    match state with
    | none =>
        PMF.bind seedDist fun seed =>
          PMF.map (fun response => (response, some seed))
            (answer seed name sec query)
    | some seed =>
        PMF.map (fun response => (response, some seed))
          (after name sec query)

private noncomputable def withMaterializedOneShotSeed
    {Seed : Type uSeed} [Nonempty Seed]
    (answer : Seed → (name : Spec.Name) → CryptoLib.Core.SecPar →
      Spec.Query name → PMF (Spec.Response name))
    (after : (name : Spec.Name) → CryptoLib.Core.SecPar →
      Spec.Query name → PMF (Spec.Response name)) :
    OracleEnv Spec where
  State := Seed × Bool
  init := (Classical.choice inferInstance, false)
  query := fun name sec state query =>
    PMF.map (fun response => (response, (state.1, true)))
      (if state.2 then after name sec query else answer state.1 name sec query)

/-- Sampling a one-shot oracle's independent hidden seed lazily or before the
adaptive caller starts gives the same value distribution. -/
theorem runWithEnv_withLazyOneShotSeed
    {Seed : Type uSeed} [Nonempty Seed]
    (seedDist : PMF Seed)
    (answer : Seed → (name : Spec.Name) → CryptoLib.Core.SecPar →
      Spec.Query name → PMF (Spec.Response name))
    (after : (name : Spec.Name) → CryptoLib.Core.SecPar →
      Spec.Query name → PMF (Spec.Response name))
    {α : Type (max uValue uResponse)}
    (program : Program issueCost α) (sec : CryptoLib.Core.SecPar) :
    Program.runWithEnv program sec
        (withLazyOneShotSeed seedDist answer after) =
      PMF.bind seedDist fun seed =>
        Program.runWithEnv program sec
          (withFixedOneShotSeed answer after seed) := by
  let deferred := withDeferredOneShotSeed seedDist answer after
  let lazy := withLazyOneShotSeed seedDist answer after
  let forgetSeed : deferred.State → PMF lazy.State
    | none => PMF.pure false
    | some _seed => PMF.pure true
  have deferredToLazy : ∀ (name : Spec.Name) (querySec : CryptoLib.Core.SecPar)
      (state : deferred.State) (query : Spec.Query name),
      (PMF.bind (deferred.query name querySec state query) fun result =>
          PMF.bind (forgetSeed result.2) fun lazyState =>
            PMF.pure (result.1, lazyState)) =
        PMF.bind (forgetSeed state) fun lazyState =>
          lazy.query name querySec lazyState query := by
    intro name querySec state query
    cases state with
    | none =>
        simp [deferred, lazy, forgetSeed, withDeferredOneShotSeed,
          withLazyOneShotSeed, PMF.bind_map, Function.comp_def]
        congr 1
    | some seed =>
        simp [deferred, lazy, forgetSeed, withDeferredOneShotSeed,
          withLazyOneShotSeed, PMF.bind_map, Function.comp_def]
        simpa only [Function.comp_apply] using
          PMF.bind_pure_comp (fun response => (response, true))
            (after name querySec query)
  have hLazy := Program.runWithEnvFromState_eq_of_stateSimulation
    deferred lazy forgetSeed deferredToLazy program sec deferred.init
  have hLazy' : Program.runWithEnv program sec deferred =
      Program.runWithEnv program sec lazy := by
    rw [Program.runWithEnvFromState_init] at hLazy
    simp only [deferred, forgetSeed, withDeferredOneShotSeed,
      PMF.pure_bind] at hLazy
    change Program.runWithEnv program sec deferred =
      Program.runWithEnvFromState program sec lazy lazy.init at hLazy
    rw [Program.runWithEnvFromState_init] at hLazy
    exact hLazy
  let materialized := withMaterializedOneShotSeed answer after
  let materialize : deferred.State → PMF materialized.State
    | none => PMF.map (fun seed => (seed, false)) seedDist
    | some seed => PMF.pure (seed, true)
  have deferredToMaterialized : ∀ (name : Spec.Name)
      (querySec : CryptoLib.Core.SecPar) (state : deferred.State)
      (query : Spec.Query name),
      (PMF.bind (deferred.query name querySec state query) fun result =>
          PMF.bind (materialize result.2) fun materializedState =>
            PMF.pure (result.1, materializedState)) =
        PMF.bind (materialize state) fun materializedState =>
          materialized.query name querySec materializedState query := by
    intro name querySec state query
    cases state with
    | none =>
        simp [deferred, materialized, materialize,
          withDeferredOneShotSeed, withMaterializedOneShotSeed,
          PMF.bind_map, Function.comp_def]
        congr 1
    | some seed =>
        simp [deferred, materialized, materialize,
          withDeferredOneShotSeed, withMaterializedOneShotSeed,
          PMF.bind_map, Function.comp_def]
        simpa only [Function.comp_apply] using
          PMF.bind_pure_comp (fun response => (response, seed, true))
            (after name querySec query)
  have hMaterialized := Program.runWithEnvFromState_eq_of_stateSimulation
    deferred materialized materialize deferredToMaterialized
      program sec deferred.init
  rw [Program.runWithEnvFromState_init] at hMaterialized
  change Program.runWithEnv program sec
      (withDeferredOneShotSeed seedDist answer after) = _ at hMaterialized
  rw [← hLazy', hMaterialized]
  change
    PMF.bind (PMF.map (fun seed => (seed, false)) seedDist)
        (fun state => Program.runWithEnvFromState program sec materialized state) = _
  rw [PMF.bind_map]
  congr 1
  funext seed
  let fixed := withFixedOneShotSeed answer after seed
  let embedState : fixed.State → PMF materialized.State :=
    fun state => PMF.pure (seed, state)
  have fixedToMaterialized : ∀ (name : Spec.Name)
      (querySec : CryptoLib.Core.SecPar) (state : fixed.State)
      (query : Spec.Query name),
      (PMF.bind (fixed.query name querySec state query) fun result =>
          PMF.bind (embedState result.2) fun materializedState =>
            PMF.pure (result.1, materializedState)) =
        PMF.bind (embedState state) fun materializedState =>
          materialized.query name querySec materializedState query := by
    intro name querySec state query
    cases state with
    | false =>
        simp [fixed, materialized, embedState, withFixedOneShotSeed,
          withMaterializedOneShotSeed, PMF.bind_map, Function.comp_def]
        simpa only [Function.comp_apply] using
          PMF.bind_pure_comp (fun response => (response, seed, true))
            (answer seed name querySec query)
    | true =>
        simp [fixed, materialized, embedState, withFixedOneShotSeed,
          withMaterializedOneShotSeed, PMF.bind_map, Function.comp_def]
        simpa only [Function.comp_apply] using
          PMF.bind_pure_comp (fun response => (response, seed, true))
            (after name querySec query)
  have hFixed := Program.runWithEnvFromState_eq_of_stateSimulation
    fixed materialized embedState fixedToMaterialized program sec fixed.init
  rw [Program.runWithEnvFromState_init, PMF.pure_bind] at hFixed
  exact hFixed.symm

end CryptoLib.Oracle.OracleEnv

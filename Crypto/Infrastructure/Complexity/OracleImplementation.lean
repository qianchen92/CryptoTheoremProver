import Crypto.Infrastructure.Asymptotic.Bounds
import Crypto.Infrastructure.Computation.Cost.Measure
import Crypto.Infrastructure.Computation.Oracle.Basic

namespace Crypto.Infrastructure.Complexity

open Crypto.Infrastructure.Asymptotic
open Crypto.Infrastructure.Computation
open Crypto.Infrastructure.Computation.Cost
open Crypto.Infrastructure.Computation.Oracle

universe uCost uIn uOracle uQuery uResponse uState

/--
An exact implementation of an input-indexed oracle family.

This layer stores only the authoritative costed environment.  Its ordinary
probability semantics is obtained by `CostedOracleEnv.erase`; no second
environment implementation is maintained.
-/
structure OracleImplementation
    (M : CostModel.{uCost})
    (Input : Crypto.SecPar → Type uIn)
    (Spec :
      (sec : Crypto.SecPar) → Input sec →
        OracleSpec.{uOracle, uQuery, uResponse}) where
  env :
    (sec : Crypto.SecPar) → (input : Input sec) →
      CostedOracleEnv.{uCost, uOracle, uQuery, uResponse, uState}
        M (Spec sec input)

namespace OracleImplementation

/-- Cost erasure of the same exact environment implementation. -/
noncomputable def eraseEnv
    {M : CostModel.{uCost}}
    {Input : Crypto.SecPar → Type uIn}
    {Spec :
      (sec : Crypto.SecPar) → Input sec →
        OracleSpec.{uOracle, uQuery, uResponse}}
    (implementation :
      OracleImplementation.{uCost, uIn, uOracle, uQuery, uResponse, uState}
        M Input Spec)
    (sec : Crypto.SecPar) (input : Input sec) :
    OracleEnv (Spec sec input) :=
  (implementation.env sec input).erase

end OracleImplementation

/--
An exact oracle implementation with an input-dependent query budget and one
uniform measured runtime for each security parameter.

`repeatBudgetMono` is explicit because an ordered additive monoid need not make
`n • cost` monotone in `n` unless nonnegativity is separately available.
-/
structure TimedOracleImplementation
    (M : CostModel.{uCost}) (measure : NatMeasure M)
    (Input : Crypto.SecPar → Type uIn)
    (Spec :
      (sec : Crypto.SecPar) → Input sec →
        OracleSpec.{uOracle, uQuery, uResponse})
    extends
      OracleImplementation.{uCost, uIn, uOracle, uQuery, uResponse, uState}
        M Input Spec where
  queryBudget : (sec : Crypto.SecPar) → Input sec → M.Cost
  queryRuntime : Crypto.SecPar → Nat
  queryBudget_sound : ∀ sec input,
    (env sec input).QueryCostBoundAt sec (queryBudget sec input)
  queryBudget_le_runtime : ∀ sec input,
    measure (queryBudget sec input) ≤ queryRuntime sec
  repeatBudgetMono : ∀ sec input {first second : Nat}, first ≤ second →
    M.instPartialOrder.le
      (Oracle.Program.repeatCost M first (queryBudget sec input))
      (Oracle.Program.repeatCost M second (queryBudget sec input))

namespace TimedOracleImplementation

/-- Every supported exact query path respects the implementation budget. -/
theorem queryCost_le_budget
    {M : CostModel.{uCost}} {measure : NatMeasure M}
    {Input : Crypto.SecPar → Type uIn}
    {Spec :
      (sec : Crypto.SecPar) → Input sec →
        OracleSpec.{uOracle, uQuery, uResponse}}
    (implementation :
      TimedOracleImplementation.{uCost, uIn, uOracle, uQuery, uResponse, uState}
        M measure Input Spec)
    (sec : Crypto.SecPar) (input : Input sec)
    (name : (Spec sec input).Name)
    (state : (implementation.env sec input).State)
    (query : (Spec sec input).Query name)
    (result :
      Costed M
        ((Spec sec input).Response name ×
          (implementation.env sec input).State))
    (hresult :
      result ∈
        ((implementation.env sec input).query name sec state query).support) :
    M.instPartialOrder.le result.cost (implementation.queryBudget sec input) :=
  implementation.queryBudget_sound sec input name state query result hresult

/-- Measuring a supported query path yields at most the uniform query runtime. -/
theorem measuredQueryCost_le_runtime
    {M : CostModel.{uCost}} {measure : NatMeasure M}
    {Input : Crypto.SecPar → Type uIn}
    {Spec :
      (sec : Crypto.SecPar) → Input sec →
        OracleSpec.{uOracle, uQuery, uResponse}}
    (implementation :
      TimedOracleImplementation.{uCost, uIn, uOracle, uQuery, uResponse, uState}
        M measure Input Spec)
    (sec : Crypto.SecPar) (input : Input sec)
    (name : (Spec sec input).Name)
    (state : (implementation.env sec input).State)
    (query : (Spec sec input).Query name)
    (result :
      Costed M
        ((Spec sec input).Response name ×
          (implementation.env sec input).State))
    (hresult :
      result ∈
        ((implementation.env sec input).query name sec state query).support) :
    measure result.cost ≤ implementation.queryRuntime sec :=
  le_trans
    (measure.monotone_toNat
      (implementation.queryCost_le_budget sec input name state query result hresult))
    (implementation.queryBudget_le_runtime sec input)

end TimedOracleImplementation

/-- An exact oracle implementation whose uniform query runtime is polynomial. -/
structure PPTOracleImplementation
    (M : CostModel.{uCost}) (measure : NatMeasure M)
    (Input : Crypto.SecPar → Type uIn)
    (Spec :
      (sec : Crypto.SecPar) → Input sec →
        OracleSpec.{uOracle, uQuery, uResponse})
    extends
      TimedOracleImplementation.{uCost, uIn, uOracle, uQuery, uResponse, uState}
        M measure Input Spec where
  queryRuntime_isPoly : IsPolyBounded queryRuntime

end Crypto.Infrastructure.Complexity

import CryptoLib.Core.Infrastructure.Computation.Oracle.Program

namespace CryptoLib.Core.Infrastructure.Computation.Oracle

open CryptoLib.Core.Infrastructure.Computation.Algebra
open CryptoLib.Core.Infrastructure.Computation.Cost

universe uCost uOracle uQuery uResponse uState

namespace QueryIssue

/-- A deterministic exact handler from an explicit query-issuance cost function. -/
noncomputable def costAlgebra
    (M : CostModel.{uCost}) (Spec : OracleSpec.{uOracle, uQuery, uResponse})
    (cost : (name : Spec.Name) → Spec.Query name → M.Cost) :
    CostedAlgebra M (signature Spec) where
  exec operation :=
    match operation with
    | .issue name query => RandCosted.liftCosted ⟨(), cost name query⟩

/-- The explicit model in which issuing a query has zero caller-side cost. -/
noncomputable def zeroCostAlgebra
    (M : CostModel.{uCost}) (Spec : OracleSpec.{uOracle, uQuery, uResponse}) :
    CostedAlgebra M (signature Spec) :=
  costAlgebra M Spec (fun _name _query => M.instAddMonoid.zero)

end QueryIssue

/-- A stateful oracle environment with an exact internal cost on every path. -/
structure CostedOracleEnv
    (M : CostModel.{uCost})
    (Spec : OracleSpec.{uOracle, uQuery, uResponse}) where
  State : Type uState
  init : State
  query :
    (name : Spec.Name) →
    CryptoLib.Core.SecPar →
    State →
    Spec.Query name →
    RandCosted M (Spec.Response name × State)

namespace OracleEnv

/-- Lift a semantic environment with an explicitly zero internal query cost. -/
noncomputable def zeroCost
    (M : CostModel.{uCost})
    {Spec : OracleSpec.{uOracle, uQuery, uResponse}}
    (env : OracleEnv.{uOracle, uQuery, uResponse, uState} Spec) :
    CostedOracleEnv.{uCost, uOracle, uQuery, uResponse, uState} M Spec where
  State := env.State
  init := env.init
  query := fun name sec state query =>
    RandCosted.sampleZeroCost M (env.query name sec state query)

end OracleEnv

namespace CostedOracleEnv

variable {M : CostModel.{uCost}}
variable {Spec : OracleSpec.{uOracle, uQuery, uResponse}}

/-- Forget internal query costs without changing response/state distributions. -/
noncomputable def erase
    (env : CostedOracleEnv.{uCost, uOracle, uQuery, uResponse, uState} M Spec) :
    OracleEnv.{uOracle, uQuery, uResponse, uState} Spec where
  State := env.State
  init := env.init
  query := fun name sec state query =>
    RandCosted.valueDist (env.query name sec state query)

@[simp] theorem erase_query
    (env : CostedOracleEnv.{uCost, uOracle, uQuery, uResponse, uState} M Spec)
    (name : Spec.Name) (sec : CryptoLib.Core.SecPar) (state : env.State)
    (query : Spec.Query name) :
    env.erase.query name sec state query =
      RandCosted.valueDist (env.query name sec state query) :=
  rfl

@[simp] theorem erase_zeroCost_query
    (env : OracleEnv.{uOracle, uQuery, uResponse, uState} Spec)
    (name : Spec.Name) (sec : CryptoLib.Core.SecPar) (state : env.State)
    (query : Spec.Query name) :
    (env.zeroCost M).erase.query name sec state query = env.query name sec state query := by
  exact RandCosted.valueDist_sampleZeroCost M (env.query name sec state query)

end CostedOracleEnv

end CryptoLib.Core.Infrastructure.Computation.Oracle

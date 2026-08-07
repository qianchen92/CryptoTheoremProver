import CryptoLib.Core.Infrastructure.SecurityParameter
import Mathlib.Probability.ProbabilityMassFunction.Basic

namespace CryptoLib.Core.Infrastructure.Computation.Oracle

universe uOracle uQuery uResponse uState

/-- A heterogeneous collection of oracle endpoints, indexed by oracle name. -/
structure OracleSpec where
  Name : Type uOracle
  Query : Name → Type uQuery
  Response : (name : Name) → Type uResponse

/-- A stateful probabilistic implementation of every endpoint in an oracle spec. -/
structure OracleEnv (Spec : OracleSpec.{uOracle, uQuery, uResponse}) where
  State : Type uState
  init : State
  query :
    (name : Spec.Name) →
    CryptoLib.Core.SecPar →
    State →
    Spec.Query name →
    PMF (Spec.Response name × State)

end CryptoLib.Core.Infrastructure.Computation.Oracle

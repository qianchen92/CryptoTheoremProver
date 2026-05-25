import Crypto.Complexity.Machine
import Crypto.Complexity.CostBound
import Crypto.Core.Oracle.Interface

namespace Crypto.Complexity

open Crypto.Foundation

universe uIn uOut uOracle uQuery uResponse uState

/-- A probabilistic polynomial-time machine with adaptive access to an oracle environment. -/
structure OraclePPTMachine
    (Input : Type uIn) (Output : Type uOut)
    (Spec : Crypto.Core.Oracle.OracleSpec.{uOracle, uQuery, uResponse}) where
  run :
    Crypto.SecPar →
    Crypto.Core.Oracle.OracleEnv.{uOracle, uQuery, uResponse, uState} Spec →
    Input →
    PMF Output
  runtime : Crypto.SecPar → Nat
  runtime_isPoly : IsPolyBounded runtime
  queryBound : Spec.Name → Crypto.SecPar → Nat
  queryBound_isPoly : ∀ name, IsPolyBounded (queryBound name)

end Crypto.Complexity

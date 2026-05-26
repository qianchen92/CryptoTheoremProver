import Crypto.Infrastructure.Complexity.Machine
import Crypto.Infrastructure.Complexity.CostBound
import Crypto.Infrastructure.Computation.Oracle.Interface

namespace Crypto.Infrastructure.Complexity

open Crypto.Infrastructure.Asymptotic

universe uIn uOut uOracle uQuery uResponse uState

/-- A probabilistic polynomial-time machine with adaptive access to an oracle environment. -/
structure OraclePPTMachine
    (Input : Crypto.SecPar → Type uIn) (Output : Crypto.SecPar → Type uOut)
    (Spec :
      (sec : Crypto.SecPar) →
      Input sec →
      Crypto.Infrastructure.Computation.Oracle.OracleSpec.{uOracle, uQuery, uResponse}) where
  run :
    (sec : Crypto.SecPar) →
    (input : Input sec) →
    Crypto.Infrastructure.Computation.Oracle.OracleEnv.{uOracle, uQuery, uResponse, uState}
      (Spec sec input) →
    PMF (Output sec)
  runtime : Crypto.SecPar → Nat
  runtime_isPoly : IsPolyBounded runtime
  queryBound : (sec : Crypto.SecPar) → (input : Input sec) → (Spec sec input).Name → Nat
  queryBound_polyBound : Crypto.SecPar → Nat
  queryBound_polyBound_isPoly : IsPolyBounded queryBound_polyBound
  queryBound_le_polyBound :
    ∀ sec input name, queryBound sec input name ≤ queryBound_polyBound sec

end Crypto.Infrastructure.Complexity

import Crypto.SecModel.Adversary.PPT
import Crypto.SecModel.Oracle.Interface

namespace Crypto.SecModel.Adversary

open Crypto.Complexity

universe uIn uOut uQuery uResponse

/-- A semantic probabilistic adversary with oracle access. -/
structure ProbabilisticOracleAdversary
    (Input : Type uIn) (Output : Type uOut)
    (Query : Type uQuery) (Response : Type uResponse) where
  run :
    Crypto.SecPar →
    Crypto.SecModel.Oracle.OracleFn Query Response →
    Crypto.SecModel.Oracle.PolyDegreeOracleFn →
    Input →
    PMF Output

/-- A polynomial-time oracle adversary with a polynomial query bound. -/
structure PPTOracleAdversary
    (Input : Type uIn) (Output : Type uOut)
    (Query : Type uQuery) (Response : Type uResponse)
    extends ProbabilisticOracleAdversary Input Output Query Response where
  runtime : Crypto.SecPar → Nat
  runtime_isPoly : IsPolyBounded runtime
  queryBound : Crypto.SecPar → Nat
  queryBound_isPoly : IsPolyBounded queryBound

abbrev DistinguishingOracleAdversary
    (X : Type uIn) (Query : Type uQuery) (Response : Type uResponse) :=
  PPTOracleAdversary X Bool Query Response

end Crypto.SecModel.Adversary

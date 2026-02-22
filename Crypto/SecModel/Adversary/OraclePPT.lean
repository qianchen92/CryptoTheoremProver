import Crypto.SecModel.Adversary.PPT
import Crypto.SecModel.Oracle.Oracle

namespace Crypto.SecModel.Adversary

open Crypto.SecModel
universe uIn uOut uQuery uResponse

abbrev OracleFn := Crypto.SecModel.Oracle.OracleFn
abbrev PolyDegreeOracleFn := Crypto.SecModel.Oracle.PolyDegreeOracleFn

structure ProbabilisticOracleAdversary
    (Input : Type uIn) (Output : Type uOut)
    (Query : Type uQuery) (Response : Type uResponse) where
  run : SecPar → OracleFn Query Response → PolyDegreeOracleFn → Input → PMF Output

structure PPTOracleAdversary
    (Input : Type uIn) (Output : Type uOut)
    (Query : Type uQuery) (Response : Type uResponse)
    extends ProbabilisticOracleAdversary Input Output Query Response where
  runtime : SecPar → Nat
  runtime_isPoly : IsPolyBounded runtime
  queryBound : SecPar → Nat
  queryBound_isPoly : IsPolyBounded queryBound

abbrev DistinguishingOracleAdversary
    (X : Type uIn) (Query : Type uQuery) (Response : Type uResponse) :=
  PPTOracleAdversary X Bool Query Response

end Crypto.SecModel.Adversary

import Crypto.SecModel.Core
import Mathlib.Probability.ProbabilityMassFunction.Basic

namespace Crypto.SecModel.Oracle

open Crypto.SecModel
universe uQuery uResponse

structure OracleFn (Query : Type uQuery) (Response : Type uResponse) where
  State : Type
  init : State
  query : SecPar → State → Query → PMF (Response × State)

abbrev PolyDegreeOracleFn :=
  SecPar → Polynomial Nat → PMF Nat

end Crypto.SecModel.Oracle

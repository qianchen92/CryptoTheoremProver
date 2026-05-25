import Crypto.Foundation.SecurityParameter
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Probability.ProbabilityMassFunction.Basic

namespace Crypto.SecModel.Oracle

universe uQuery uResponse

/-- A stateful probabilistic oracle indexed by the security parameter. -/
structure OracleFn (Query : Type uQuery) (Response : Type uResponse) where
  State : Type
  init : State
  query : Crypto.SecPar → State → Query → PMF (Response × State)

abbrev PolyDegreeOracleFn :=
  Crypto.SecPar → Polynomial Nat → PMF Nat

end Crypto.SecModel.Oracle

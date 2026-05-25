import Crypto.Foundation.SecurityParameter
import Mathlib.Probability.ProbabilityMassFunction.Basic

namespace Crypto.SecModel.Adversary

universe uIn uOut

/-- A semantic probabilistic adversary indexed by the security parameter. -/
structure ProbabilisticAdversary (Input : Type uIn) (Output : Type uOut) where
  run : Crypto.SecPar → Input → PMF Output

end Crypto.SecModel.Adversary

import Crypto.SecModel.Core
import Mathlib.Probability.ProbabilityMassFunction.Basic

namespace Crypto.SecModel.Adversary

open Crypto.SecModel
universe uIn uOut

structure ProbabilisticAdversary (Input : Type uIn) (Output : Type uOut) where
  run : SecPar → Input → PMF Output

structure PPTAdversary (Input : Type uIn) (Output : Type uOut)
    extends ProbabilisticAdversary Input Output where
  runtime : SecPar → Nat
  runtime_isPoly : IsPolyBounded runtime

abbrev DistinguishingAdversary (X : Type uIn) := PPTAdversary X Bool

end Crypto.SecModel.Adversary

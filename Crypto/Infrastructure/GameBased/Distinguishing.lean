import Crypto.Infrastructure.Complexity.Machine
import Crypto.Infrastructure.GameBased.Indistinguishability
import Mathlib.Probability.ProbabilityMassFunction.Monad

namespace Crypto.Infrastructure.GameBased

open Crypto.Infrastructure.Computation.Cost

universe uCost uChallenge

namespace Distinguishing

/-- A distinguishing problem is a pair of challenge distributions. -/
structure Problem (Challenge : Type uChallenge) where
  left : Crypto.SecPar → PMF Challenge
  right : Crypto.SecPar → PMF Challenge

/-- Run a boolean machine on samples from a challenge distribution. -/
noncomputable def securityGame
    {M : CostModel.{uCost}} {Challenge : Type uChallenge}
    (sample : Crypto.SecPar → PMF Challenge)
    (adversary : Crypto.Infrastructure.Complexity.ProbabilisticMachine M
      (fun _sec => Challenge) (fun _sec _challenge => Bool)) :
    Crypto.Infrastructure.Computation.Game Bool :=
  fun sec =>
    PMF.bind (sample sec) fun challenge =>
      adversary.runDist sec challenge

/--
A distinguishing problem is hard relative to an explicit cost model and
natural-number observation when every polynomially annotated and operationally
admitted machine has negligible advantage.
-/
def Hard
    (adversaryModel : CostModel.{uCost})
    (measure : NatMeasure adversaryModel)
    {Challenge : Type uChallenge} (problem : Problem Challenge) : Prop :=
  ∀ adversary : Crypto.Infrastructure.Complexity.PPTMachine
      adversaryModel measure
      (fun _sec => Challenge) (fun _sec _challenge => Bool),
    Indistinguishable
      (securityGame problem.left adversary.toProbabilisticMachine)
      (securityGame problem.right adversary.toProbabilisticMachine)

end Distinguishing

end Crypto.Infrastructure.GameBased

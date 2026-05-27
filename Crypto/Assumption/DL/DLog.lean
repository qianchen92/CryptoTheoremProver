import Crypto.Infrastructure.Computation.Algebra.Group
import Crypto.Infrastructure.Computation.Distribution
import Crypto.Infrastructure.GameBased.Search
import Mathlib.Probability.ProbabilityMassFunction.Monad

namespace Crypto.Assumption.DL

namespace DLog

universe uScalar uGroup

/-- Public parameters for a finite additive-group discrete-log instance. -/
structure PublicParam where
  Scalar : Type uScalar
  Carrier : Type uGroup
  addGroup : AddGroup Carrier
  fintypeCarrier : Fintype Carrier
  nonemptyCarrier : Nonempty Carrier
  decidableEqCarrier : DecidableEq Carrier
  fintypeScalar : Fintype Scalar
  nonemptyScalar : Nonempty Scalar
  mulScalar : Mul Scalar
  smul : SMul Scalar Carrier
  generator : Carrier

attribute [instance] PublicParam.addGroup
attribute [instance] PublicParam.fintypeCarrier
attribute [instance] PublicParam.nonemptyCarrier
attribute [instance] PublicParam.decidableEqCarrier
attribute [instance] PublicParam.fintypeScalar
attribute [instance] PublicParam.nonemptyScalar
attribute [instance] PublicParam.mulScalar
attribute [instance] PublicParam.smul

/-- A security-parameter-indexed family of discrete-log public parameters. -/
structure Family where
  setup : Crypto.SecPar → PMF PublicParam.{uScalar, uGroup}

/-- Input given to a discrete-log adversary: public parameters and a challenge element. -/
abbrev ChallengeInput :=
  Sigma fun pp : PublicParam.{uScalar, uGroup} => pp.Carrier

/-- A candidate discrete-log witness for a challenge. -/
abbrev Witness (challenge : ChallengeInput.{uScalar, uGroup}) :=
  challenge.1.Scalar

/-- A witness solves a challenge if it maps the public generator to the challenge element. -/
def IsSolution
    (challenge : ChallengeInput.{uScalar, uGroup}) (witness : Witness challenge) : Prop :=
  witness • challenge.1.generator = challenge.2

instance instDecidableIsSolution
    (challenge : ChallengeInput.{uScalar, uGroup}) (witness : Witness challenge) :
    Decidable (IsSolution challenge witness) := by
  unfold IsSolution
  infer_instance

/-- The search problem induced by a discrete-log family. -/
noncomputable def dLogProblem (F : Family.{uScalar, uGroup}) :
    Crypto.Infrastructure.GameBased.Search.Problem.{
      max (uScalar + 1) (uGroup + 1), uScalar} ChallengeInput.{uScalar, uGroup} where
  Witness := Witness
  sample :=
    fun sec =>
      PMF.bind (F.setup sec) fun pp =>
        PMF.bind (Crypto.Infrastructure.Computation.Distribution.uniformPMF pp.Scalar) fun secret =>
          PMF.pure ⟨pp, secret • pp.generator⟩
  relation := IsSolution
  decidableRelation := instDecidableIsSolution

/-- The discrete-log assumption for a parameter family. -/
def Assumption (F : Family.{uScalar, uGroup}) : Prop :=
  Crypto.Infrastructure.GameBased.Search.Hard (dLogProblem F)

end DLog

end Crypto.Assumption.DL

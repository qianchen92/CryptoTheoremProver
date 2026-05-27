import Crypto.Infrastructure.Computation.Algebra.Group
import Crypto.Infrastructure.Computation.Distribution
import Crypto.Infrastructure.GameBased.Search
import Mathlib.Probability.ProbabilityMassFunction.Monad

namespace Crypto.Assumption.DL

namespace DLog

universe uParam uScalar uGroup

/-- Input given to a discrete-log adversary: public parameters and a challenge element. -/
abbrev ChallengeInput (Param : Type uParam) (Group : Type uGroup) :=
  Param × Group

/-- A security-parameter-indexed family of finite additive-group discrete-log instances. -/
structure Family
    (Param : Type uParam) (Scalar : Type uScalar) (Group : Type uGroup)
    [AddGroup Group] [Fintype Group] [Nonempty Group] [DecidableEq Group]
    [Fintype Scalar] [Nonempty Scalar] [SMul Scalar Group] where
  setup : Crypto.SecPar → PMF Param
  generator : Param → Group

section

variable {Param : Type uParam} {Scalar : Type uScalar} {Group : Type uGroup}
variable [AddGroup Group] [Fintype Group] [Nonempty Group] [DecidableEq Group]
variable [Fintype Scalar] [Nonempty Scalar] [SMul Scalar Group]

/-- A witness solves a challenge if it maps the public generator to the challenge element. -/
def IsSolution
    (F : Family Param Scalar Group) (challenge : ChallengeInput Param Group)
    (witness : Scalar) : Prop :=
  witness • F.generator challenge.1 = challenge.2

instance instDecidableIsSolution
    (F : Family Param Scalar Group) (challenge : ChallengeInput Param Group) (witness : Scalar) :
    Decidable (IsSolution F challenge witness) := by
  unfold IsSolution
  infer_instance

/-- The search problem induced by a discrete-log family. -/
noncomputable def problem (F : Family Param Scalar Group) :
    Crypto.Infrastructure.GameBased.Search.Problem (ChallengeInput Param Group) Scalar where
  sample :=
    fun sec =>
      PMF.bind (F.setup sec) fun pp =>
        PMF.bind (Crypto.Infrastructure.Computation.Distribution.uniformPMF Scalar) fun secret =>
          PMF.pure (pp, secret • F.generator pp)
  relation := IsSolution F
  decidableRelation := instDecidableIsSolution F

/-- The discrete-log assumption for a parameter family. -/
def Assumption (F : Family Param Scalar Group) : Prop :=
  Crypto.Infrastructure.GameBased.Search.Hard (problem F)

end

end DLog

end Crypto.Assumption.DL

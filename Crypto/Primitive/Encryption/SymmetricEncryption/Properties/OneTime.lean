import Crypto.Primitive.Encryption.SymmetricEncryption.Syntax
import Crypto.Infrastructure.GameBased.OracleDistinguishing
import Mathlib.Probability.ProbabilityMassFunction.Monad

namespace Crypto.Primitive.Encryption.SymmetricEncryption

universe uCost uAdversaryCost uParam uKey uMessage uCiphertext

variable
    {M : Crypto.Infrastructure.Computation.Cost.CostModel.{uCost}}
    {adversaryModel :
      Crypto.Infrastructure.Computation.Cost.CostModel.{uAdversaryCost}}
    {measure : Crypto.Infrastructure.Computation.Cost.NatMeasure adversaryModel}
    {Param : Type uParam}
    {Key : Param → Type uKey}
    {Message : Param → Type uMessage}
    {Ciphertext : Param → Type uCiphertext}
    {E : Scheme M Crypto.SecPar Param Key Message Ciphertext}

abbrev ChallengeQuery (Message : Type uMessage) :=
  Message × Message

abbrev ChallengeResponse (Ciphertext : Type uCiphertext) :=
  Option Ciphertext

inductive OneTimeOracle where
  | challenge

def oneTimeOracleSpec
    (Message : Param → Type uMessage)
    (Ciphertext : Param → Type uCiphertext)
    (_sec : Crypto.SecPar) (pp : Param) :
    Crypto.Infrastructure.Computation.Oracle.OracleSpec where
  Name := OneTimeOracle
  Query
    | OneTimeOracle.challenge => ChallengeQuery (Message pp)
  Response
    | OneTimeOracle.challenge => ChallengeResponse (Ciphertext pp)

/-- A one-use left-or-right encryption oracle. -/
noncomputable def oneTimeEncryptionOracle
    (E : Scheme M Crypto.SecPar Param Key Message Ciphertext)
    (sec : Crypto.SecPar) (pp : Param) (b : Bool) :
    Crypto.Infrastructure.Computation.Oracle.OracleEnv
      (oneTimeOracleSpec Message Ciphertext sec pp) where
  State := Bool
  init := false
  query
    | OneTimeOracle.challenge, _querySec, used, query =>
        if used then
          return ((none : ChallengeResponse (Ciphertext pp)), true)
        else
          let m0 := query.1
          let m1 := query.2
          PMF.bind (E.keygenDist pp) fun key =>
            PMF.bind (E.encryptDist pp key (if b then m1 else m0)) fun ciphertext =>
              PMF.pure
                ((some ciphertext : ChallengeResponse (Ciphertext pp)), true)

/-- The oracle distinguishing problem induced by one-time left-or-right encryption. -/
noncomputable def oneTimeProblem
    (E : Scheme M Crypto.SecPar Param Key Message Ciphertext) :
    Crypto.Infrastructure.GameBased.OracleDistinguishing.Problem
      (fun _ => Param) (oneTimeOracleSpec Message Ciphertext) where
  setup := E.setupDist
  leftEnv := fun sec pp => oneTimeEncryptionOracle E sec pp false
  rightEnv := fun sec pp => oneTimeEncryptionOracle E sec pp true

/-- The one-time indistinguishability security game for a fixed challenge bit. -/
noncomputable def oneTimeSecurityGame
    (E : Scheme M Crypto.SecPar Param Key Message Ciphertext)
    (A : Crypto.Infrastructure.Complexity.OracleMachine adversaryModel
      (fun _ => Param) (fun _sec _input => Bool)
      (oneTimeOracleSpec Message Ciphertext))
    (b : Bool) : Crypto.Infrastructure.Computation.Game Bool :=
  if b then
    Crypto.Infrastructure.GameBased.OracleDistinguishing.rightSecurityGame (oneTimeProblem E) A
  else
    Crypto.Infrastructure.GameBased.OracleDistinguishing.leftSecurityGame (oneTimeProblem E) A

/-- One-time left-or-right distinguishing advantage. -/
noncomputable def OneTimeAdvantage
    (E : Scheme M Crypto.SecPar Param Key Message Ciphertext)
    (A : Crypto.Infrastructure.Complexity.OracleMachine adversaryModel
      (fun _ => Param) (fun _sec _input => Bool)
      (oneTimeOracleSpec Message Ciphertext)) :
    Crypto.SecPar → Real :=
  Crypto.Infrastructure.GameBased.Advantage
    (oneTimeSecurityGame E A false) (oneTimeSecurityGame E A true)

/-- Perfect one-time security against unbounded oracle machines. -/
def PerfectOneTimeSecure
    (adversaryModel :
      Crypto.Infrastructure.Computation.Cost.CostModel.{uAdversaryCost})
    (E : Scheme M Crypto.SecPar Param Key Message Ciphertext) : Prop :=
  ∀ A : Crypto.Infrastructure.Complexity.OracleMachine adversaryModel
      (fun _ => Param) (fun _sec _input => Bool)
      (oneTimeOracleSpec Message Ciphertext),
    OneTimeAdvantage E A = fun _ => 0

/-- One-time security against PPT oracle adversaries. -/
def OneTimeSecure
    (adversaryModel :
      Crypto.Infrastructure.Computation.Cost.CostModel.{uAdversaryCost})
    (measure : Crypto.Infrastructure.Computation.Cost.NatMeasure adversaryModel)
    (E : Scheme M Crypto.SecPar Param Key Message Ciphertext) : Prop :=
  Crypto.Infrastructure.GameBased.OracleDistinguishing.Hard
    adversaryModel measure (oneTimeProblem E)

/-- Perfect one-time security implies PPT one-time security. -/
theorem PerfectOneTimeSecure.toOneTimeSecure :
    PerfectOneTimeSecure adversaryModel E →
      OneTimeSecure adversaryModel measure E := by
  intro hPerfect A
  change Crypto.Infrastructure.Asymptotic.IsNegligible
    (OneTimeAdvantage E A.toOracleMachine)
  rw [hPerfect A.toOracleMachine]
  exact Crypto.Infrastructure.Asymptotic.isNegligible_zero

end Crypto.Primitive.Encryption.SymmetricEncryption

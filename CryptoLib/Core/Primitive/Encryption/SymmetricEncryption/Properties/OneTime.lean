import CryptoLib.Core.Primitive.Encryption.SymmetricEncryption.Syntax
import CryptoLib.Core.Infrastructure.GameBased.OracleDistinguishing
import Mathlib.Probability.ProbabilityMassFunction.Monad

namespace CryptoLib.Core.Primitive.Encryption.SymmetricEncryption

open CryptoLib.Core.Infrastructure.Computation.Cost

universe uCost uAdversaryCost uParam uKey uMessage uCiphertext

variable
    {M : CostModel.{uCost}}
    {adversaryModel : CostModel.{uAdversaryCost}}
    {measure : NatMeasure adversaryModel}
    {Param : Type uParam}
    {Key : Param → Type uKey}
    {Message : Param → Type uMessage}
    {Ciphertext : Param → Type uCiphertext}
    {E : Scheme M CryptoLib.Core.SecPar Param Key Message Ciphertext}

abbrev ChallengeQuery (Message : Type uMessage) :=
  Message × Message

abbrev ChallengeResponse (Ciphertext : Type uCiphertext) :=
  Option Ciphertext

inductive OneTimeOracle where
  | challenge

def oneTimeOracleSpec
    (Message : Param → Type uMessage)
    (Ciphertext : Param → Type uCiphertext)
    (_sec : CryptoLib.Core.SecPar) (pp : Param) :
    CryptoLib.Core.Infrastructure.Computation.Oracle.OracleSpec where
  Name := OneTimeOracle
  Query
    | OneTimeOracle.challenge => ChallengeQuery (Message pp)
  Response
    | OneTimeOracle.challenge => ChallengeResponse (Ciphertext pp)

/-- A one-use left-or-right encryption oracle. -/
noncomputable def oneTimeEncryptionOracle
    (E : Scheme M CryptoLib.Core.SecPar Param Key Message Ciphertext)
    (sec : CryptoLib.Core.SecPar) (pp : Param) (b : Bool) :
    CryptoLib.Core.Infrastructure.Computation.Oracle.OracleEnv
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
    (E : Scheme M CryptoLib.Core.SecPar Param Key Message Ciphertext) :
    CryptoLib.Core.Infrastructure.GameBased.OracleDistinguishing.Problem
      (fun _ => Param) (oneTimeOracleSpec Message Ciphertext) where
  setup := E.setupDist
  leftEnv := fun sec pp => oneTimeEncryptionOracle E sec pp false
  rightEnv := fun sec pp => oneTimeEncryptionOracle E sec pp true

/-- The one-time indistinguishability security game for a fixed challenge bit. -/
noncomputable def oneTimeSecurityGame
    (E : Scheme M CryptoLib.Core.SecPar Param Key Message Ciphertext)
    (A : CryptoLib.Core.Infrastructure.Complexity.OracleMachine adversaryModel
      (fun _ => Param) (fun _sec _input => Bool)
      (oneTimeOracleSpec Message Ciphertext))
    (b : Bool) : CryptoLib.Core.Infrastructure.Computation.Game Bool :=
  if b then
    CryptoLib.Core.Infrastructure.GameBased.OracleDistinguishing.rightSecurityGame (oneTimeProblem E) A
  else
    CryptoLib.Core.Infrastructure.GameBased.OracleDistinguishing.leftSecurityGame (oneTimeProblem E) A

/-- One-time left-or-right distinguishing advantage. -/
noncomputable def OneTimeAdvantage
    (E : Scheme M CryptoLib.Core.SecPar Param Key Message Ciphertext)
    (A : CryptoLib.Core.Infrastructure.Complexity.OracleMachine adversaryModel
      (fun _ => Param) (fun _sec _input => Bool)
      (oneTimeOracleSpec Message Ciphertext)) :
    CryptoLib.Core.SecPar → Real :=
  CryptoLib.Core.Infrastructure.GameBased.Advantage
    (oneTimeSecurityGame E A false) (oneTimeSecurityGame E A true)

section

variable (adversaryModel measure)

/-- Perfect one-time security against unbounded oracle machines. -/
def PerfectOneTimeSecure
    (E : Scheme M CryptoLib.Core.SecPar Param Key Message Ciphertext) : Prop :=
  ∀ A : CryptoLib.Core.Infrastructure.Complexity.OracleMachine adversaryModel
      (fun _ => Param) (fun _sec _input => Bool)
      (oneTimeOracleSpec Message Ciphertext),
    OneTimeAdvantage E A = fun _ => 0

/-- One-time security against PPT oracle adversaries. -/
def OneTimeSecure
    (E : Scheme M CryptoLib.Core.SecPar Param Key Message Ciphertext) : Prop :=
  CryptoLib.Core.Infrastructure.GameBased.OracleDistinguishing.Hard
    adversaryModel measure (oneTimeProblem E)

end

/-- Perfect one-time security implies PPT one-time security. -/
theorem PerfectOneTimeSecure.toOneTimeSecure :
    PerfectOneTimeSecure adversaryModel E →
      OneTimeSecure adversaryModel measure E := by
  intro hPerfect A
  change CryptoLib.Core.Infrastructure.Asymptotic.IsNegligible
    (OneTimeAdvantage E A.toOracleMachine)
  rw [hPerfect A.toOracleMachine]
  exact CryptoLib.Core.Infrastructure.Asymptotic.isNegligible_zero

end CryptoLib.Core.Primitive.Encryption.SymmetricEncryption

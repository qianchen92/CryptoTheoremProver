import Crypto.Infrastructure.Asymptotic.Bounds
import Crypto.Infrastructure.Complexity.Machine
import Crypto.Primitive.Encryption.SymmetricEncryption.Syntax
import Crypto.Infrastructure.GameBased.Advantage
import Mathlib.Probability.ProbabilityMassFunction.Monad

namespace Crypto.Primitive.Encryption.SymmetricEncryption

universe uParam uKey uMessage uCiphertext

abbrev ChallengeQuery (Message : Type uMessage) :=
  Message × Message

abbrev ChallengeResponse (Ciphertext : Type uCiphertext) :=
  Option Ciphertext

inductive OneTimeOracle where
  | challenge

def oneTimeOracleSpec
    {Param : Crypto.SecPar → Type uParam}
    (Message : {sec : Crypto.SecPar} → Param sec → Type uMessage)
    (Ciphertext : {sec : Crypto.SecPar} → Param sec → Type uCiphertext)
    (sec : Crypto.SecPar) (pp : Param sec) :
    Crypto.Infrastructure.Computation.Oracle.OracleSpec where
  Name := OneTimeOracle
  Query
    | OneTimeOracle.challenge => ChallengeQuery (Message pp)
  Response
    | OneTimeOracle.challenge => ChallengeResponse (Ciphertext pp)

/-- A one-use left-or-right encryption oracle. -/
noncomputable def oneTimeEncryptionOracle
    {Param : Crypto.SecPar → Type uParam}
    {Key : {sec : Crypto.SecPar} → Param sec → Type uKey}
    {Message : {sec : Crypto.SecPar} → Param sec → Type uMessage}
    {Ciphertext : {sec : Crypto.SecPar} → Param sec → Type uCiphertext}
    (E : Scheme Param Key Message Ciphertext)
    (sec : Crypto.SecPar) (pp : Param sec) (b : Bool) :
    Crypto.Infrastructure.Computation.Oracle.OracleEnv
      (oneTimeOracleSpec Message Ciphertext sec pp) where
  State := Bool
  init := false
  query
    | OneTimeOracle.challenge, _querySec, used, query =>
        if used then
          PMF.pure ((none : ChallengeResponse (Ciphertext pp)), true)
        else
          let m0 := query.1
          let m1 := query.2
          PMF.bind (E.keygen pp) fun key =>
            PMF.bind (E.encrypt pp key (if b then m1 else m0)) fun ciphertext =>
              PMF.pure (some ciphertext, true)

/-- The one-time indistinguishability game for a fixed challenge bit. -/
noncomputable def oneTimeGame
    {Param : Crypto.SecPar → Type uParam}
    {Key : {sec : Crypto.SecPar} → Param sec → Type uKey}
    {Message : {sec : Crypto.SecPar} → Param sec → Type uMessage}
    {Ciphertext : {sec : Crypto.SecPar} → Param sec → Type uCiphertext}
    (E : Scheme Param Key Message Ciphertext)
    (A : Crypto.Infrastructure.Complexity.ProbabilisticOracleMachine
      Param (fun _ => Bool) (oneTimeOracleSpec Message Ciphertext))
    (b : Bool) : Crypto.Infrastructure.Computation.Game Bool :=
  fun sec =>
    PMF.bind (E.setup sec) fun pp =>
      A.run sec pp (oneTimeEncryptionOracle E sec pp b)

/-- One-time left-or-right distinguishing advantage. -/
noncomputable def OneTimeAdvantage
    {Param : Crypto.SecPar → Type uParam}
    {Key : {sec : Crypto.SecPar} → Param sec → Type uKey}
    {Message : {sec : Crypto.SecPar} → Param sec → Type uMessage}
    {Ciphertext : {sec : Crypto.SecPar} → Param sec → Type uCiphertext}
    (E : Scheme Param Key Message Ciphertext)
    (A : Crypto.Infrastructure.Complexity.ProbabilisticOracleMachine
      Param (fun _ => Bool) (oneTimeOracleSpec Message Ciphertext)) : Crypto.SecPar → Real :=
  Crypto.Infrastructure.GameBased.Advantage (oneTimeGame E A false) (oneTimeGame E A true)

/-- Perfect one-time security against unbounded oracle machines. -/
def PerfectOneTimeSecure
    {Param : Crypto.SecPar → Type uParam}
    {Key : {sec : Crypto.SecPar} → Param sec → Type uKey}
    {Message : {sec : Crypto.SecPar} → Param sec → Type uMessage}
    {Ciphertext : {sec : Crypto.SecPar} → Param sec → Type uCiphertext}
    (E : Scheme Param Key Message Ciphertext) : Prop :=
  ∀ A : Crypto.Infrastructure.Complexity.ProbabilisticOracleMachine
      Param (fun _ => Bool) (oneTimeOracleSpec Message Ciphertext),
    OneTimeAdvantage E A = fun _ => 0

/-- One-time security against PPT oracle adversaries. -/
def OneTimeSecure
    {Param : Crypto.SecPar → Type uParam}
    {Key : {sec : Crypto.SecPar} → Param sec → Type uKey}
    {Message : {sec : Crypto.SecPar} → Param sec → Type uMessage}
    {Ciphertext : {sec : Crypto.SecPar} → Param sec → Type uCiphertext}
    (E : Scheme Param Key Message Ciphertext) : Prop :=
  ∀ A : Crypto.Infrastructure.Complexity.PPTOracleMachine
      Param (fun _ => Bool) (oneTimeOracleSpec Message Ciphertext),
    Crypto.Infrastructure.Asymptotic.IsNegligible
      (OneTimeAdvantage E A.toProbabilisticOracleMachine)

/-- Perfect one-time security implies PPT one-time security. -/
theorem PerfectOneTimeSecure.toOneTimeSecure
    {Param : Crypto.SecPar → Type uParam}
    {Key : {sec : Crypto.SecPar} → Param sec → Type uKey}
    {Message : {sec : Crypto.SecPar} → Param sec → Type uMessage}
    {Ciphertext : {sec : Crypto.SecPar} → Param sec → Type uCiphertext}
    {E : Scheme Param Key Message Ciphertext} :
    PerfectOneTimeSecure E → OneTimeSecure E := by
  intro hPerfect A
  rw [hPerfect A.toProbabilisticOracleMachine]
  exact Crypto.Infrastructure.Asymptotic.isNegligible_zero

end Crypto.Primitive.Encryption.SymmetricEncryption

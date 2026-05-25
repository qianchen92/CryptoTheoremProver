import Crypto.Foundation.Asymptotics
import Crypto.Complexity.PPT
import Crypto.Primitive.Encryption.SymmetricEncryption.Syntax
import Crypto.Security.Advantage
import Mathlib.Probability.ProbabilityMassFunction.Monad

namespace Crypto.Primitive.Encryption.SymmetricEncryption

universe uKey uMessage uCiphertext

abbrev ChallengeQuery (Message : Type uMessage) :=
  Message × Message

abbrev ChallengeResponse (Ciphertext : Type uCiphertext) :=
  Option Ciphertext

inductive OneTimeOracle where
  | challenge

def oneTimeOracleSpec (Message : Type uMessage) (Ciphertext : Type uCiphertext) :
    Crypto.Core.Oracle.OracleSpec where
  Name := OneTimeOracle
  Query
    | OneTimeOracle.challenge => ChallengeQuery Message
  Response
    | OneTimeOracle.challenge => ChallengeResponse Ciphertext

/-- A one-use left-or-right encryption oracle. -/
noncomputable def oneTimeEncryptionOracle
    {Key : Type uKey} {Message : Type uMessage} {Ciphertext : Type uCiphertext}
    (E : Scheme Key Message Ciphertext)
    (validPair : Crypto.SecPar → Message → Message → Prop)
    [∀ sec m0 m1, Decidable (validPair sec m0 m1)] (b : Bool) :
    Crypto.Core.Oracle.OracleEnv (oneTimeOracleSpec Message Ciphertext) where
  State := Bool
  init := false
  query
    | OneTimeOracle.challenge, sec, used, query =>
        if used then
          PMF.pure ((none : ChallengeResponse Ciphertext), true)
        else
          let m0 := query.1
          let m1 := query.2
          if validPair sec m0 m1 then
            PMF.bind (E.keygen sec) fun key =>
              PMF.bind (E.encrypt sec key (if b then m1 else m0)) fun ciphertext =>
                PMF.pure (some ciphertext, true)
          else
            PMF.pure ((none : ChallengeResponse Ciphertext), true)

/-- The one-time indistinguishability game for a fixed challenge bit. -/
noncomputable def oneTimeGame
    {Key : Type uKey} {Message : Type uMessage} {Ciphertext : Type uCiphertext}
    (E : Scheme Key Message Ciphertext)
    (validPair : Crypto.SecPar → Message → Message → Prop)
    [∀ sec m0 m1, Decidable (validPair sec m0 m1)]
    (A : Crypto.Complexity.OraclePPTMachine.{0, 0, 0, uMessage, uCiphertext, 0}
      Unit Bool (oneTimeOracleSpec Message Ciphertext))
    (b : Bool) : Crypto.Core.Game Bool :=
  fun sec =>
    A.run sec (oneTimeEncryptionOracle E validPair b) ()

/-- One-time left-or-right distinguishing advantage. -/
noncomputable def OneTimeAdvantage
    {Key : Type uKey} {Message : Type uMessage} {Ciphertext : Type uCiphertext}
    (E : Scheme Key Message Ciphertext)
    (validPair : Crypto.SecPar → Message → Message → Prop)
    [∀ sec m0 m1, Decidable (validPair sec m0 m1)]
    (A : Crypto.Complexity.OraclePPTMachine.{0, 0, 0, uMessage, uCiphertext, 0}
      Unit Bool (oneTimeOracleSpec Message Ciphertext)) : Crypto.SecPar → Real :=
  Crypto.Security.Advantage (oneTimeGame E validPair A false) (oneTimeGame E validPair A true)

/-- One-time security against PPT oracle adversaries. -/
def OneTimeSecure
    {Key : Type uKey} {Message : Type uMessage} {Ciphertext : Type uCiphertext}
    (E : Scheme Key Message Ciphertext)
    (validPair : Crypto.SecPar → Message → Message → Prop)
    [∀ sec m0 m1, Decidable (validPair sec m0 m1)] : Prop :=
  ∀ A : Crypto.Complexity.OraclePPTMachine.{0, 0, 0, uMessage, uCiphertext, 0}
      Unit Bool (oneTimeOracleSpec Message Ciphertext),
    Crypto.Foundation.IsNegligible (OneTimeAdvantage E validPair A)

end Crypto.Primitive.Encryption.SymmetricEncryption

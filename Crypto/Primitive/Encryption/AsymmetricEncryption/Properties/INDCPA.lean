import Crypto.Infrastructure.GameBased.OracleDistinguishing
import Crypto.Primitive.Encryption.AsymmetricEncryption.Syntax
import Mathlib.Probability.ProbabilityMassFunction.Monad

namespace Crypto.Primitive.Encryption.AsymmetricEncryption

universe uCost uAdversaryCost uParam uPublicKey uSecretKey uMessage uCiphertext

abbrev ChallengeQuery (Message : Type uMessage) :=
  Message × Message

abbrev ChallengeResponse (Ciphertext : Type uCiphertext) :=
  Option Ciphertext

/-- Public information given to an IND-CPA adversary. -/
structure PublicInput
    (Param : Type uParam)
    (PublicKey : Param → Type uPublicKey)
    (sec : Crypto.SecPar) where
  param : Param
  publicKey : PublicKey param

inductive INDCPAOracle where
  | challenge

def indCPAOracleSpec
    {Param : Type uParam}
    {PublicKey : Param → Type uPublicKey}
    (Message : Param → Type uMessage)
    (Ciphertext : Param → Type uCiphertext)
    (sec : Crypto.SecPar) (input : PublicInput Param PublicKey sec) :
    Crypto.Infrastructure.Computation.Oracle.OracleSpec where
  Name := INDCPAOracle
  Query
    | INDCPAOracle.challenge => ChallengeQuery (Message input.param)
  Response
    | INDCPAOracle.challenge => ChallengeResponse (Ciphertext input.param)

/-- A one-use left-or-right public-key encryption oracle. -/
noncomputable def indCPAEncryptionOracle
    {M : Crypto.Infrastructure.Computation.Cost.CostModel.{uCost}}
    {Param : Type uParam}
    {PublicKey : Param → Type uPublicKey}
    {SecretKey : Param → Type uSecretKey}
    {Message : Param → Type uMessage}
    {Ciphertext : Param → Type uCiphertext}
    (E : Scheme M Crypto.SecPar Param PublicKey SecretKey Message Ciphertext)
    (sec : Crypto.SecPar) (input : PublicInput Param PublicKey sec) (b : Bool) :
    Crypto.Infrastructure.Computation.Oracle.OracleEnv
      (indCPAOracleSpec Message Ciphertext sec input) where
  State := Bool
  init := false
  query
    | INDCPAOracle.challenge, _querySec, used, query =>
        if used then
          return ((none : ChallengeResponse (Ciphertext input.param)), true)
        else
          let m0 := query.1
          let m1 := query.2
          PMF.bind (E.encryptDist input.param input.publicKey (if b then m1 else m0))
            fun ciphertext => do
              return ((some ciphertext : ChallengeResponse (Ciphertext input.param)), true)

/-- The oracle distinguishing problem induced by IND-CPA public-key encryption. -/
noncomputable def indCPAProblem
    {M : Crypto.Infrastructure.Computation.Cost.CostModel.{uCost}}
    {Param : Type uParam}
    {PublicKey : Param → Type uPublicKey}
    {SecretKey : Param → Type uSecretKey}
    {Message : Param → Type uMessage}
    {Ciphertext : Param → Type uCiphertext}
    (E : Scheme M Crypto.SecPar Param PublicKey SecretKey Message Ciphertext) :
    Crypto.Infrastructure.GameBased.OracleDistinguishing.Problem
      (PublicInput Param PublicKey) (indCPAOracleSpec Message Ciphertext) where
  setup :=
    fun sec =>
      PMF.bind (E.setupDist sec) fun pp =>
        PMF.bind (E.keygenDist pp) fun keys =>
          PMF.pure ({ param := pp, publicKey := keys.1 } : PublicInput Param PublicKey sec)
  leftEnv := fun sec input => indCPAEncryptionOracle E sec input false
  rightEnv := fun sec input => indCPAEncryptionOracle E sec input true

/-- The IND-CPA security game for a fixed challenge bit. -/
noncomputable def indCPASecurityGame
    {M : Crypto.Infrastructure.Computation.Cost.CostModel.{uCost}}
    {adversaryModel :
      Crypto.Infrastructure.Computation.Cost.CostModel.{uAdversaryCost}}
    {Param : Type uParam}
    {PublicKey : Param → Type uPublicKey}
    {SecretKey : Param → Type uSecretKey}
    {Message : Param → Type uMessage}
    {Ciphertext : Param → Type uCiphertext}
    (E : Scheme M Crypto.SecPar Param PublicKey SecretKey Message Ciphertext)
    (A : Crypto.Infrastructure.Complexity.OracleMachine adversaryModel
      (PublicInput Param PublicKey) (fun _sec _input => Bool)
      (indCPAOracleSpec Message Ciphertext))
    (b : Bool) : Crypto.Infrastructure.Computation.Game Bool :=
  if b then
    Crypto.Infrastructure.GameBased.OracleDistinguishing.rightSecurityGame (indCPAProblem E) A
  else
    Crypto.Infrastructure.GameBased.OracleDistinguishing.leftSecurityGame (indCPAProblem E) A

/-- IND-CPA distinguishing advantage. -/
noncomputable def INDCPAAdvantage
    {M : Crypto.Infrastructure.Computation.Cost.CostModel.{uCost}}
    {adversaryModel :
      Crypto.Infrastructure.Computation.Cost.CostModel.{uAdversaryCost}}
    {Param : Type uParam}
    {PublicKey : Param → Type uPublicKey}
    {SecretKey : Param → Type uSecretKey}
    {Message : Param → Type uMessage}
    {Ciphertext : Param → Type uCiphertext}
    (E : Scheme M Crypto.SecPar Param PublicKey SecretKey Message Ciphertext)
    (A : Crypto.Infrastructure.Complexity.OracleMachine adversaryModel
      (PublicInput Param PublicKey) (fun _sec _input => Bool)
      (indCPAOracleSpec Message Ciphertext)) :
    Crypto.SecPar → Real :=
  Crypto.Infrastructure.GameBased.Advantage
    (indCPASecurityGame E A false) (indCPASecurityGame E A true)

/-- IND-CPA security against PPT oracle adversaries. -/
def INDCPASecure
    {M : Crypto.Infrastructure.Computation.Cost.CostModel.{uCost}}
    {Param : Type uParam}
    {PublicKey : Param → Type uPublicKey}
    {SecretKey : Param → Type uSecretKey}
    {Message : Param → Type uMessage}
    {Ciphertext : Param → Type uCiphertext}
    (adversaryModel :
      Crypto.Infrastructure.Computation.Cost.CostModel.{uAdversaryCost})
    (measure : Crypto.Infrastructure.Computation.Cost.NatMeasure adversaryModel)
    (E : Scheme M Crypto.SecPar Param PublicKey SecretKey Message Ciphertext) : Prop :=
  Crypto.Infrastructure.GameBased.OracleDistinguishing.Hard
    adversaryModel measure (indCPAProblem E)

end Crypto.Primitive.Encryption.AsymmetricEncryption

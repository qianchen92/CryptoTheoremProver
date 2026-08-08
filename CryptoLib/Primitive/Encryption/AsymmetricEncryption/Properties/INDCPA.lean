import CryptoLib.Core.Infrastructure.GameBased.OracleDistinguishing
import CryptoLib.Primitive.Encryption.AsymmetricEncryption.Syntax
import Mathlib.Probability.ProbabilityMassFunction.Monad

namespace CryptoLib.Primitive.Encryption.AsymmetricEncryption

open CryptoLib.Core.Infrastructure.Computation.Cost

universe uCost uAdversaryCost uParam uPublicKey uSecretKey uMessage uCiphertext

variable
    {M : CostModel.{uCost}}
    {adversaryModel : CostModel.{uAdversaryCost}}
    {measure : NatMeasure adversaryModel}
    {Param : Type uParam}
    {PublicKey : Param → Type uPublicKey}
    {SecretKey : Param → Type uSecretKey}
    {Message : Param → Type uMessage}
    {Ciphertext : Param → Type uCiphertext}

abbrev ChallengeQuery (Message : Type uMessage) :=
  Message × Message

abbrev ChallengeResponse (Ciphertext : Type uCiphertext) :=
  Option Ciphertext

/-- Public information given to an IND-CPA adversary. -/
structure PublicInput
    (Param : Type uParam)
    (PublicKey : Param → Type uPublicKey)
    (sec : CryptoLib.Core.SecPar) where
  param : Param
  publicKey : PublicKey param

inductive INDCPAOracle where
  | challenge

def indCPAOracleSpec
    (Message : Param → Type uMessage)
    (Ciphertext : Param → Type uCiphertext)
    (sec : CryptoLib.Core.SecPar) (input : PublicInput Param PublicKey sec) :
    CryptoLib.Oracle.OracleSpec where
  Name := INDCPAOracle
  Query
    | INDCPAOracle.challenge => ChallengeQuery (Message input.param)
  Response
    | INDCPAOracle.challenge => ChallengeResponse (Ciphertext input.param)

/-- A one-use left-or-right public-key encryption oracle. -/
noncomputable def indCPAEncryptionOracle
    (E : Scheme M CryptoLib.Core.SecPar Param PublicKey SecretKey Message Ciphertext)
    (sec : CryptoLib.Core.SecPar) (input : PublicInput Param PublicKey sec) (b : Bool) :
    CryptoLib.Oracle.OracleEnv
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
    (E : Scheme M CryptoLib.Core.SecPar Param PublicKey SecretKey Message Ciphertext) :
    CryptoLib.Core.Infrastructure.GameBased.OracleDistinguishing.Problem
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
    (E : Scheme M CryptoLib.Core.SecPar Param PublicKey SecretKey Message Ciphertext)
    (A : CryptoLib.Oracle.Complexity.OracleMachine adversaryModel
      (PublicInput Param PublicKey) (fun _sec _input => Bool)
      (indCPAOracleSpec Message Ciphertext))
    (b : Bool) : CryptoLib.Core.Infrastructure.Computation.Game Bool :=
  if b then
    CryptoLib.Core.Infrastructure.GameBased.OracleDistinguishing.rightSecurityGame (indCPAProblem E) A
  else
    CryptoLib.Core.Infrastructure.GameBased.OracleDistinguishing.leftSecurityGame (indCPAProblem E) A

/-- IND-CPA distinguishing advantage. -/
noncomputable def INDCPAAdvantage
    (E : Scheme M CryptoLib.Core.SecPar Param PublicKey SecretKey Message Ciphertext)
    (A : CryptoLib.Oracle.Complexity.OracleMachine adversaryModel
      (PublicInput Param PublicKey) (fun _sec _input => Bool)
      (indCPAOracleSpec Message Ciphertext)) :
    CryptoLib.Core.SecPar → Real :=
  CryptoLib.Core.Infrastructure.GameBased.Advantage
    (indCPASecurityGame E A false) (indCPASecurityGame E A true)

section

variable (adversaryModel measure)

/-- IND-CPA security against PPT oracle adversaries. -/
def INDCPASecure
    (E : Scheme M CryptoLib.Core.SecPar Param PublicKey SecretKey Message Ciphertext) : Prop :=
  CryptoLib.Core.Infrastructure.GameBased.OracleDistinguishing.Hard
    adversaryModel measure (indCPAProblem E)

end

end CryptoLib.Primitive.Encryption.AsymmetricEncryption

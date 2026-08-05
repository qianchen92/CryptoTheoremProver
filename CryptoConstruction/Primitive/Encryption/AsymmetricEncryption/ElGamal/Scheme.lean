import CryptoConstruction.Primitive.Encryption.AsymmetricEncryption.ElGamal.Construction
import Crypto.Infrastructure.Computation.FirstOrder.Builder
import Crypto.Infrastructure.Computation.FirstOrder.Semantics
import Crypto.Primitive.Encryption.AsymmetricEncryption.Syntax

namespace CryptoConstruction.Primitive.Encryption.AsymmetricEncryption.ElGamal

open Crypto.Infrastructure.Computation
open Crypto.Infrastructure.Computation.Algebra
open Crypto.Infrastructure.Computation.Cost
open Crypto.Primitive.Encryption.AsymmetricEncryption
open scoped DDHParameter
open scoped Crypto.Infrastructure.Computation.FirstOrder

universe uCost uScalar uGroup

variable {M : CostModel.{uCost}}

/-- ElGamal key generation over the DDH parameter's sole exact algebra. -/
def keygenProgram (pp : PublicParam.{uCost, uScalar, uGroup} M) :
    Crypto.Infrastructure.Computation.FirstOrder.Program
      (Language.interpret pp) Language.signature .unit
      (.prod Language.carrierTy Language.scalarTy) where
  body := first_order input do
    let secretKey ← call .sampleScalar with unit
    let publicKey ←
      call .smul with (secretKey, value(Language.generator pp))
    return (publicKey, secretKey)

/-- ElGamal encryption over the DDH parameter's sole exact algebra. -/
def encryptProgram (pp : PublicParam.{uCost, uScalar, uGroup} M) :
    Crypto.Infrastructure.Computation.FirstOrder.Program
      (Language.interpret pp) Language.signature
      (.prod Language.carrierTy Language.carrierTy)
      (.prod Language.carrierTy Language.carrierTy) where
  body := first_order input do
    let nonce ← call .sampleScalar with unit
    let firstComponent ←
      call .smul with (nonce, value(Language.generator pp))
    let shared ← call .smul with (nonce, fst(input))
    let secondComponent ← call .add with (snd(input), shared)
    return (firstComponent, secondComponent)

/-- ElGamal decryption over the same exact DDH algebra. -/
def decryptProgram (pp : PublicParam.{uCost, uScalar, uGroup} M) :
    Crypto.Infrastructure.Computation.FirstOrder.Program
      (Language.interpret pp) Language.signature
      (.prod Language.scalarTy
        (.prod Language.carrierTy Language.carrierTy))
      Language.carrierTy where
  body := first_order input do
    let shared ← call .smul with (fst(input), fst(snd(input)))
    let message ← call .sub with (snd(snd(input)), shared)
    return message

/-- ElGamal executes setup, key generation, encryption, and decryption only through Programs. -/
noncomputable def scheme (F : Family.{uCost, uScalar, uGroup} M) :
    Scheme M Crypto.SecPar (PublicParam.{uCost, uScalar, uGroup} M)
      PublicKey SecretKey Message Ciphertext where
  setup := fun sec =>
    Program.runCosted (Crypto.Assumption.DL.DDH.setupProgram F) sec
  keygen := fun pp =>
    RandCosted.map (Language.keyPairDown pp)
      (Crypto.Infrastructure.Computation.FirstOrder.Program.runCosted
        (Language.algebra pp) (keygenProgram pp) (ULift.up ()))
  encrypt := fun pp publicKey message =>
    RandCosted.map (Language.carrierPairDown pp)
      (Crypto.Infrastructure.Computation.FirstOrder.Program.runCosted
        (Language.algebra pp) (encryptProgram pp)
        (Language.liftCarrier pp publicKey, Language.liftCarrier pp message))
  decrypt := fun pp secretKey ciphertext =>
    RandCosted.map ULift.down
      (Crypto.Infrastructure.Computation.FirstOrder.Program.runCosted
        (Language.algebra pp) (decryptProgram pp)
        (Language.liftScalar pp secretKey,
          (Language.liftCarrier pp ciphertext.1,
            Language.liftCarrier pp ciphertext.2)))

end CryptoConstruction.Primitive.Encryption.AsymmetricEncryption.ElGamal

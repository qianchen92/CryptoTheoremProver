import Crypto.Infrastructure.Computation.Program.Basic
import Crypto.Infrastructure.Computation.FirstOrder.Builder
import Crypto.Infrastructure.Computation.FirstOrder.Semantics
import CryptoConstruction.Primitive.Encryption.SymmetricEncryption.OneTimePad.Construction
import Crypto.Primitive.Encryption.SymmetricEncryption.Syntax

namespace CryptoConstruction.Primitive.Encryption.SymmetricEncryption.OneTimePad

open Crypto.Infrastructure.Computation
open Crypto.Infrastructure.Computation.Cost
open Crypto.Primitive.Encryption.SymmetricEncryption
open scoped Crypto.Infrastructure.Computation.FirstOrder

universe uCost uGroup

variable {M : CostModel.{uCost}}

/-- OTP setup as a typed family-level program. -/
def setupProgram (F : Family.{uCost, uGroup} M) :
    Program (familyAlgebra F) Crypto.SecPar
      (PublicParam.{uCost, uGroup} M) where
  body sec := .call (.setup sec)

/-- Uniform key generation over the parameter's sole exact algebra. -/
def keygenProgram (pp : PublicParam M) :
    Crypto.Infrastructure.Computation.FirstOrder.Program
      (Language.interpret pp) Language.signature
      .unit Language.carrierTy where
  body := first_order input do
    let key ← call .sampleKey with unit
    return key

/-- One-addition OTP encryption over the parameter's sole exact algebra. -/
def encryptProgram (pp : PublicParam M) :
    Crypto.Infrastructure.Computation.FirstOrder.Program
      (Language.interpret pp) Language.signature
      (.prod Language.carrierTy Language.carrierTy) Language.carrierTy where
  body := first_order input do
    let ciphertext ← call .add with (fst(input), snd(input))
    return ciphertext

/-- Negation-then-addition OTP decryption. -/
def decryptProgram (pp : PublicParam M) :
    Crypto.Infrastructure.Computation.FirstOrder.Program
      (Language.interpret pp) Language.signature
      (.prod Language.carrierTy Language.carrierTy) Language.carrierTy where
  body := first_order input do
    let negatedKey ← call .neg with fst(input)
    let message ← call .add with (negatedKey, snd(input))
    return message

/-- The OTP scheme executes setup and its three parameter operations only through Programs. -/
noncomputable def scheme (F : Family M) :
    Scheme M Crypto.SecPar (PublicParam M)
      (fun pp => pp.Carrier) (fun pp => pp.Carrier) (fun pp => pp.Carrier) where
  setup := fun sec => Program.runCosted (setupProgram F) sec
  keygen := fun pp =>
    Crypto.Infrastructure.Computation.FirstOrder.Program.runCosted
      (Language.algebra pp) (keygenProgram pp) (ULift.up ())
  encrypt := fun pp key message =>
    Crypto.Infrastructure.Computation.FirstOrder.Program.runCosted
      (Language.algebra pp) (encryptProgram pp) (key, message)
  decrypt := fun pp key ciphertext =>
    Crypto.Infrastructure.Computation.FirstOrder.Program.runCosted
      (Language.algebra pp) (decryptProgram pp) (key, ciphertext)

end CryptoConstruction.Primitive.Encryption.SymmetricEncryption.OneTimePad

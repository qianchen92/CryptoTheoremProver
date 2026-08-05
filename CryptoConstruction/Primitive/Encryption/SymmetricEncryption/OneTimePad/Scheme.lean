import Crypto.Infrastructure.Computation.Program.Basic
import CryptoFirstOrder.Builder
import CryptoFirstOrder.Semantics
import CryptoConstruction.Primitive.Encryption.SymmetricEncryption.OneTimePad.Construction
import Crypto.Primitive.Encryption.SymmetricEncryption.Syntax

namespace CryptoConstruction.Primitive.Encryption.SymmetricEncryption.OneTimePad

open scoped CryptoFirstOrder

universe uCost uGroup

variable
  {M : Crypto.Infrastructure.Computation.Cost.CostModel.{uCost}}
  (F : Family.{uCost, uGroup} M)
  (pp : PublicParam.{uCost, uGroup} M)

/-- OTP setup as a typed family-level program. -/
def setupProgram :
    Crypto.Infrastructure.Computation.Program
      (familyAlgebra F) Crypto.SecPar
      (PublicParam.{uCost, uGroup} M) where
  body sec := .call (.setup sec)

/-- Uniform key generation over the parameter's sole exact algebra. -/
def keygenProgram :
    CryptoFirstOrder.Program.NAry
      (Language.interpret pp) Language.signature [] Language.keyTy where
  body := first_order () do
    let key ← unifSamp Language.carrierTy
    return key

/-- One-addition OTP encryption over the parameter's sole exact algebra. -/
def encryptProgram :
    CryptoFirstOrder.Program.NAry
      (Language.interpret pp) Language.signature
      [Language.keyTy, Language.messageTy] Language.ciphertextTy where
  body := first_order (key, message) do
    let ciphertext ← key + message
    return ciphertext

/-- Negation-then-addition OTP decryption. -/
def decryptProgram :
    CryptoFirstOrder.Program.NAry
      (Language.interpret pp) Language.signature
      [Language.keyTy, Language.ciphertextTy] Language.messageTy where
  body := first_order (key, ciphertext) do
    let negatedKey ← -key
    let message ← negatedKey + ciphertext
    return message

/-- The OTP scheme executes setup and its three parameter operations only through Programs. -/
noncomputable def scheme (F : Family M) :
    Crypto.Primitive.Encryption.SymmetricEncryption.Scheme
      M Crypto.SecPar (PublicParam M)
      (fun pp => pp.Carrier) (fun pp => pp.Carrier) (fun pp => pp.Carrier) where
  setup := fun sec =>
    Crypto.Infrastructure.Computation.Program.runCosted (setupProgram F) sec
  keygen := fun pp =>
    CryptoFirstOrder.Program.runCosted
      (Language.algebra pp) (keygenProgram pp)
      (CryptoFirstOrder.Builder.representValue ())
  encrypt := fun pp key message =>
    CryptoFirstOrder.Program.runCosted
      (Language.algebra pp) (encryptProgram pp) (key, message)
  decrypt := fun pp key ciphertext =>
    CryptoFirstOrder.Program.runCosted
      (Language.algebra pp) (decryptProgram pp) (key, ciphertext)

end CryptoConstruction.Primitive.Encryption.SymmetricEncryption.OneTimePad

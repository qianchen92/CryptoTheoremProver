import CryptoLib.Core.Infrastructure.Computation.Program.Basic
import CryptoLib.Program.Builder
import CryptoLib.Program.Semantics
import CryptoLib.Instantiation.Primitive.Encryption.SymmetricEncryption.OneTimePad.Construction
import CryptoLib.Core.Primitive.Encryption.SymmetricEncryption.Syntax

namespace CryptoLib.Instantiation.Primitive.Encryption.SymmetricEncryption.OneTimePad

open scoped CryptoLib.Program

universe uCost uGroup

variable
  {M : CryptoLib.Core.Infrastructure.Computation.Cost.CostModel.{uCost}}
  (F : Family.{uCost, uGroup} M)
  (pp : PublicParam.{uCost, uGroup} M)

/-- OTP setup as a typed family-level program. -/
def setupProgram :
    CryptoLib.Core.Infrastructure.Computation.Program
      (familyAlgebra F) CryptoLib.Core.SecPar
      (PublicParam.{uCost, uGroup} M) where
  body sec := .call (.setup sec)

/-- Uniform key generation over the parameter's sole exact algebra. -/
def keygenProgram :
    CryptoLib.Program.Procedure.NAry
      (Language.interpret pp) Language.signature [] Language.keyTy where
  body := first_order () do
    let key ← unifSamp Language.carrierTy
    return key

/-- One-addition OTP encryption over the parameter's sole exact algebra. -/
def encryptProgram :
    CryptoLib.Program.Procedure.NAry
      (Language.interpret pp) Language.signature
      [Language.keyTy, Language.messageTy] Language.ciphertextTy where
  body := first_order (key, message) do
    let ciphertext ← key + message
    return ciphertext

/-- Negation-then-addition OTP decryption. -/
def decryptProgram :
    CryptoLib.Program.Procedure.NAry
      (Language.interpret pp) Language.signature
      [Language.keyTy, Language.ciphertextTy] Language.messageTy where
  body := first_order (key, ciphertext) do
    let negatedKey ← -key
    let message ← negatedKey + ciphertext
    return message

/-- The OTP scheme executes setup and its three parameter operations only through Programs. -/
noncomputable def scheme (F : Family M) :
    CryptoLib.Core.Primitive.Encryption.SymmetricEncryption.Scheme
      M CryptoLib.Core.SecPar (PublicParam M)
      (fun pp => pp.Carrier) (fun pp => pp.Carrier) (fun pp => pp.Carrier) where
  setup := fun sec =>
    CryptoLib.Core.Infrastructure.Computation.Program.runCosted (setupProgram F) sec
  keygen := fun pp =>
    CryptoLib.Program.Procedure.runCosted
      (Language.algebra pp) (keygenProgram pp)
      (CryptoLib.Program.Builder.representValue ())
  encrypt := fun pp key message =>
    CryptoLib.Program.Procedure.runCosted
      (Language.algebra pp) (encryptProgram pp) (key, message)
  decrypt := fun pp key ciphertext =>
    CryptoLib.Program.Procedure.runCosted
      (Language.algebra pp) (decryptProgram pp) (key, ciphertext)

end CryptoLib.Instantiation.Primitive.Encryption.SymmetricEncryption.OneTimePad

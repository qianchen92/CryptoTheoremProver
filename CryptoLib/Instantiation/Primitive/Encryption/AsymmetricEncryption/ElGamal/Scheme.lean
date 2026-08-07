import CryptoLib.Instantiation.Primitive.Encryption.AsymmetricEncryption.ElGamal.Construction
import CryptoLib.Program.Builder
import CryptoLib.Program.Semantics
import CryptoLib.Core.Primitive.Encryption.AsymmetricEncryption.Syntax

namespace CryptoLib.Instantiation.Primitive.Encryption.AsymmetricEncryption.ElGamal

open scoped CryptoLib.Program DDHParameter DDHGroup

universe uCost uParameter uScalar uGroup

variable
  {M : CryptoLib.Core.Infrastructure.Computation.Cost.CostModel.{uCost}}
  {Parameter : Type uParameter}
  {Scalar : Type uScalar}
  {Carrier : Type uGroup}
  (F : Family M Parameter Scalar Carrier)
  (pp : PublicParam.{uCost, uScalar, uGroup} M Scalar Carrier)

/--
ElGamal's construction-local setup program delegates to the authoritative DDH
family setup rather than defining a second parameter-generation algorithm.
-/
def setupProgram :
    CryptoLib.Core.Infrastructure.Computation.Program
      (CryptoLib.Core.Assumption.DL.DDH.familyAlgebra F) CryptoLib.Core.SecPar
      (ULift.{max uScalar uGroup} Parameter) :=
  CryptoLib.Core.Assumption.DL.DDH.setupProgram F

/-- ElGamal key generation over the DDH parameter's sole exact algebra. -/
def keygenProgram :
    CryptoLib.Program.Procedure.NAryPair
      (Language.interpret pp) Language.signature
      []
      Language.publicKeyTy Language.secretKeyTy where
  body := first_order () do
    let sk ← unifSamp Language.scalarTy
    let pk ← ⦋sk⦌
    return (pk, sk)

/-- ElGamal encryption over the DDH parameter's sole exact algebra. -/
def encryptProgram :
    CryptoLib.Program.Procedure.NAry
      (Language.interpret pp) Language.signature
      [Language.publicKeyTy, Language.messageTy] Language.ciphertextTy where
  body := first_order (pk, m) do
    let r ← unifSamp Language.scalarTy
    let C₁ ← ⦋r⦌
    let C₂ ← m + (r • pk)
    return (C₁, C₂)

/-- ElGamal decryption over the same exact DDH algebra. -/
def decryptProgram :
    CryptoLib.Program.Procedure.NAry
      (Language.interpret pp) Language.signature
      [Language.secretKeyTy, Language.ciphertextTy] Language.messageTy where
  body := first_order (sk, ciphertext) do
    let shared ← sk • fst(ciphertext)
    let message ← snd(ciphertext) - shared
    return message

/-- ElGamal executes setup, key generation, encryption, and decryption only through Programs. -/
noncomputable def scheme :
    CryptoLib.Core.Primitive.Encryption.AsymmetricEncryption.Scheme
      M CryptoLib.Core.SecPar Parameter
      (PublicKey (Carrier := Carrier))
      (SecretKey (Scalar := Scalar))
      (Message (Carrier := Carrier))
      (Ciphertext (Carrier := Carrier)) where
  setup := fun sec =>
    CryptoLib.Core.Infrastructure.Computation.Cost.RandCosted.map ULift.down
      (CryptoLib.Core.Infrastructure.Computation.Program.runCosted
        (setupProgram F) sec)
  keygen := fun parameter =>
    let pp := F.publicParam parameter
    CryptoLib.Program.Builder.runCosted
      (Language.algebra pp) (keygenProgram pp) ()
  encrypt := fun parameter pk message =>
    let pp := F.publicParam parameter
    CryptoLib.Program.Builder.runCosted
      (Language.algebra pp) (encryptProgram pp) (pk, message)
  decrypt := fun parameter sk ciphertext =>
    let pp := F.publicParam parameter
    CryptoLib.Program.Builder.runCosted
      (Language.algebra pp) (decryptProgram pp)
      (sk, (ciphertext.1, ciphertext.2))

end CryptoLib.Instantiation.Primitive.Encryption.AsymmetricEncryption.ElGamal

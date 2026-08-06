import CryptoConstruction.Primitive.Encryption.AsymmetricEncryption.ElGamal.Construction
import CryptoFirstOrder.Builder
import CryptoFirstOrder.Semantics
import Crypto.Primitive.Encryption.AsymmetricEncryption.Syntax

namespace CryptoConstruction.Primitive.Encryption.AsymmetricEncryption.ElGamal

open scoped CryptoFirstOrder DDHParameter DDHGroup

universe uCost uParameter uScalar uGroup

variable
  {M : Crypto.Infrastructure.Computation.Cost.CostModel.{uCost}}
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
    Crypto.Infrastructure.Computation.Program
      (Crypto.Assumption.DL.DDH.familyAlgebra F) Crypto.SecPar
      (ULift.{max uScalar uGroup} Parameter) :=
  Crypto.Assumption.DL.DDH.setupProgram F

/-- ElGamal key generation over the DDH parameter's sole exact algebra. -/
def keygenProgram :
    CryptoFirstOrder.Program.NAryPair
      (Language.interpret pp) Language.signature
      []
      Language.publicKeyTy Language.secretKeyTy where
  body := first_order () do
    let sk ← unifSamp Language.scalarTy
    let pk ← ⦋sk⦌
    return (pk, sk)

/-- ElGamal encryption over the DDH parameter's sole exact algebra. -/
def encryptProgram :
    CryptoFirstOrder.Program.NAry
      (Language.interpret pp) Language.signature
      [Language.publicKeyTy, Language.messageTy] Language.ciphertextTy where
  body := first_order (pk, m) do
    let r ← unifSamp Language.scalarTy
    let C₁ ← ⦋r⦌
    let C₂ ← m + (r • pk)
    return (C₁, C₂)

/-- ElGamal decryption over the same exact DDH algebra. -/
def decryptProgram :
    CryptoFirstOrder.Program.NAry
      (Language.interpret pp) Language.signature
      [Language.secretKeyTy, Language.ciphertextTy] Language.messageTy where
  body := first_order (sk, ciphertext) do
    let shared ← sk • fst(ciphertext)
    let message ← snd(ciphertext) - shared
    return message

/-- ElGamal executes setup, key generation, encryption, and decryption only through Programs. -/
noncomputable def scheme :
    Crypto.Primitive.Encryption.AsymmetricEncryption.Scheme
      M Crypto.SecPar Parameter
      (PublicKey (Carrier := Carrier))
      (SecretKey (Scalar := Scalar))
      (Message (Carrier := Carrier))
      (Ciphertext (Carrier := Carrier)) where
  setup := fun sec =>
    Crypto.Infrastructure.Computation.Cost.RandCosted.map ULift.down
      (Crypto.Infrastructure.Computation.Program.runCosted
        (setupProgram F) sec)
  keygen := fun parameter =>
    let pp := F.publicParam parameter
    CryptoFirstOrder.Builder.runCosted
      (Language.algebra pp) (keygenProgram pp) ()
  encrypt := fun parameter pk message =>
    let pp := F.publicParam parameter
    CryptoFirstOrder.Builder.runCosted
      (Language.algebra pp) (encryptProgram pp) (pk, message)
  decrypt := fun parameter sk ciphertext =>
    let pp := F.publicParam parameter
    CryptoFirstOrder.Builder.runCosted
      (Language.algebra pp) (decryptProgram pp)
      (sk, (ciphertext.1, ciphertext.2))

end CryptoConstruction.Primitive.Encryption.AsymmetricEncryption.ElGamal

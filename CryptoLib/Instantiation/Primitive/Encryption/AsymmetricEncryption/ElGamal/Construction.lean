import CryptoLib.Assumption.DL.DDH
import CryptoLib.Assumption.Program.DL.DDH

namespace CryptoLib.Instantiation.Primitive.Encryption.AsymmetricEncryption.ElGamal

open scoped CryptoLib.Program

universe uCost uParameter uScalar uGroup

variable
  (M : CryptoLib.Core.Infrastructure.Computation.Cost.CostModel.{uCost})
  (Parameter : Type uParameter)
  (Scalar : Type uScalar)
  (Carrier : Type uGroup)

/-- ElGamal parameter families are the underlying DLog/DDH families. -/
abbrev Family :=
  CryptoLib.Assumption.DL.DDH.Family M Parameter Scalar Carrier

/-- The exact DDH backend selected by one ElGamal family parameter. -/
abbrev PublicParam :=
  CryptoLib.Assumption.DL.DDH.PublicParam M Scalar Carrier

variable {M Parameter Scalar Carrier}

/-- Public keys use the family's fixed group representation. -/
abbrev PublicKey (_parameter : Parameter) := Carrier

/-- Secret keys use the family's fixed scalar representation. -/
abbrev SecretKey (_parameter : Parameter) := Scalar

/-- Messages use the family's fixed group representation. -/
abbrev Message (_parameter : Parameter) := Carrier

/-- Ciphertexts use two values in the family's fixed group representation. -/
abbrev Ciphertext (_parameter : Parameter) := Carrier × Carrier

/- The scalar and group carriers available to reified ElGamal algorithms. -/
namespace Language

export CryptoLib.Assumption.Program.DL.DDH
  (Base scalarTy carrierTy interpret ScalarValue CarrierValue liftScalar
    liftCarrier carrierScalarPairDown carrierPairDown Operation signature algebra)

/-- Object-language type of an ElGamal public key. -/
abbrev publicKeyTy := carrierTy

/-- Object-language type of an ElGamal secret key. -/
abbrev secretKeyTy := scalarTy

/-- Object-language type of an ElGamal message. -/
abbrev messageTy := carrierTy

/-- Object-language type of an ElGamal ciphertext. -/
abbrev ciphertextTy := carrierTy ×ₜ carrierTy

abbrev keyPairDown
    (pp : PublicParam.{uCost, uScalar, uGroup} M Scalar Carrier) :
    CarrierValue pp × ScalarValue pp → pp.Carrier × pp.Scalar :=
  carrierScalarPairDown pp

namespace Operation

export CryptoLib.Assumption.Program.DL.DDH.Operation
  (sampleScalar smul add sub)

end Operation

end Language

end CryptoLib.Instantiation.Primitive.Encryption.AsymmetricEncryption.ElGamal

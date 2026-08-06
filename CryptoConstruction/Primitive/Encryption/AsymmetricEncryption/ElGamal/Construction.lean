import Crypto.Assumption.DL.DDH
import CryptoFirstOrder.Assumption.DL.DDH

namespace CryptoConstruction.Primitive.Encryption.AsymmetricEncryption.ElGamal

open scoped CryptoFirstOrder

universe uCost uParameter uScalar uGroup

variable
  (M : Crypto.Infrastructure.Computation.Cost.CostModel.{uCost})
  (Parameter : Type uParameter)
  (Scalar : Type uScalar)
  (Carrier : Type uGroup)

/-- ElGamal parameter families are the underlying DLog/DDH families. -/
abbrev Family :=
  Crypto.Assumption.DL.DDH.Family M Parameter Scalar Carrier

/-- The exact DDH backend selected by one ElGamal family parameter. -/
abbrev PublicParam :=
  Crypto.Assumption.DL.DDH.PublicParam M Scalar Carrier

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

export CryptoFirstOrder.Assumption.DL.DDH
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

export CryptoFirstOrder.Assumption.DL.DDH.Operation
  (sampleScalar smul add sub)

end Operation

end Language

end CryptoConstruction.Primitive.Encryption.AsymmetricEncryption.ElGamal

import Crypto.Infrastructure.Computation.Algebra.Group
import Crypto.Infrastructure.Computation.Distribution
import Crypto.Primitive.Encryption.SymmetricEncryption.Syntax

namespace Crypto.Primitive.Encryption.SymmetricEncryption.Instantiations.OneTimePad

universe uGroup

open Crypto.Primitive.Encryption.SymmetricEncryption

/-- Public parameters for a concrete group selected by the security parameter. -/
def publicParam
    (GroupFamily : Crypto.SecPar → Type uGroup)
    [∀ sec, AddGroup (GroupFamily sec)] [∀ sec, Fintype (GroupFamily sec)]
    [∀ sec, Nonempty (GroupFamily sec)]
    (sec : Crypto.SecPar) :
    Crypto.Infrastructure.Computation.Algebra.Group.AdditiveGroupParam where
  Carrier := GroupFamily sec
  addGroup := inferInstance
  fintype := inferInstance
  nonempty := inferInstance

/-- One-time pad over a finite nonempty additive group selected during setup. -/
noncomputable def scheme
    (GroupFamily : Crypto.SecPar → Type uGroup)
    [∀ sec, AddGroup (GroupFamily sec)] [∀ sec, Fintype (GroupFamily sec)]
    [∀ sec, Nonempty (GroupFamily sec)] :
    Scheme
      (fun _ => Crypto.Infrastructure.Computation.Algebra.Group.AdditiveGroupParam.{uGroup})
      (fun pp => pp.Carrier)
      (fun pp => pp.Carrier)
      (fun pp => pp.Carrier) where
  setup := fun sec => do
    return publicParam GroupFamily sec
  keygen := fun pp => Crypto.Infrastructure.Computation.Distribution.uniformPMF pp.Carrier
  encrypt := fun _pp key message => do
    let ciphertext := key + message
    return ciphertext
  decrypt := fun _pp key ciphertext => -key + ciphertext

end Crypto.Primitive.Encryption.SymmetricEncryption.Instantiations.OneTimePad

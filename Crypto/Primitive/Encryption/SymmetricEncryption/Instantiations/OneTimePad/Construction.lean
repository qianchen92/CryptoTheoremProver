import Crypto.Core.Algebra.Group
import Crypto.Core.Distribution
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
    Crypto.Core.Algebra.Group.AdditiveGroupParam where
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
      (fun _ => Crypto.Core.Algebra.Group.AdditiveGroupParam.{uGroup})
      (fun pp => pp.Carrier)
      (fun pp => pp.Carrier)
      (fun pp => pp.Carrier) where
  setup := fun sec => PMF.pure (publicParam GroupFamily sec)
  keygen := fun pp => Crypto.Core.Distribution.uniformPMF pp.Carrier
  encrypt := fun _pp key message => PMF.pure (key + message)
  decrypt := fun _pp key ciphertext => -key + ciphertext

end Crypto.Primitive.Encryption.SymmetricEncryption.Instantiations.OneTimePad

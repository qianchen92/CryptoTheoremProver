import Crypto.Infrastructure.Computation.Algebra.Group
import Crypto.Infrastructure.Computation.Distribution
import Crypto.Primitive.Encryption.SymmetricEncryption.Syntax

namespace Crypto.Primitive.Encryption.SymmetricEncryption.Instantiations.OneTimePad

universe uGroup

open Crypto.Primitive.Encryption.SymmetricEncryption

/-- Public parameters for one-time pad encryption. -/
abbrev PublicParam :=
  Crypto.Infrastructure.Computation.Algebra.Group.AdditiveGroupParam.{uGroup}

/-- A security-parameter-indexed family of one-time-pad public parameters. -/
structure Family where
  setup : Crypto.SecPar → PMF PublicParam.{uGroup}

/-- Public parameters for a concrete group selected by the security parameter. -/
def publicParam
    (GroupFamily : Crypto.SecPar → Type uGroup)
    [∀ sec, AddGroup (GroupFamily sec)] [∀ sec, Fintype (GroupFamily sec)]
    [∀ sec, Nonempty (GroupFamily sec)]
    (sec : Crypto.SecPar) :
    PublicParam.{uGroup} where
  Carrier := GroupFamily sec
  addGroup := inferInstance
  fintype := inferInstance
  nonempty := inferInstance

/-- The one-time-pad family induced by a type-level group family. -/
noncomputable def Family.ofGroupFamily
    (GroupFamily : Crypto.SecPar → Type uGroup)
    [∀ sec, AddGroup (GroupFamily sec)] [∀ sec, Fintype (GroupFamily sec)]
    [∀ sec, Nonempty (GroupFamily sec)] : Family.{uGroup} where
  setup := fun sec => PMF.pure (publicParam GroupFamily sec)

/-- One-time pad over a finite nonempty additive group family. -/
noncomputable def scheme (F : Family.{uGroup}) :
    Scheme
      Crypto.SecPar
      PublicParam.{uGroup}
      (fun pp => pp.Carrier)
      (fun pp => pp.Carrier)
      (fun pp => pp.Carrier) where
  setup := F.setup
  keygen := fun pp => Crypto.Infrastructure.Computation.Distribution.uniformPMF pp.Carrier
  encrypt := fun _pp key message => do
    let ciphertext := key + message
    return ciphertext
  decrypt := fun _pp key ciphertext => -key + ciphertext

end Crypto.Primitive.Encryption.SymmetricEncryption.Instantiations.OneTimePad

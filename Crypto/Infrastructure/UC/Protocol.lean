import Crypto.Infrastructure.UC.Execution
import Mathlib.Data.Finset.Basic

namespace Crypto.Infrastructure.UC

universe uEntity uInput uOutput uState

/-- The corruption mode attached to a UC component. -/
inductive CorruptionMode where
  | incorruptible
  | static
  | dynamicWithErasures
  deriving DecidableEq, Repr

/-- A corruption policy is a mode plus a predicate for eligible corruptions. -/
structure CorruptionPolicy (Entity : Type uEntity) where
  mode : CorruptionMode
  eligible : Finset Entity → Prop

namespace CorruptionPolicy

/-- An incorruptible component allows only the empty corruption set. -/
def incorruptible (Entity : Type uEntity) : CorruptionPolicy Entity where
  mode := CorruptionMode.incorruptible
  eligible := fun corrupted => corrupted = ∅

end CorruptionPolicy

/--
A generic UC protocol as a family of machines indexed by participating entities.

The `Input` and `Output` types may depend on both the security parameter and the
entity, leaving concrete network and scheduling syntax to later refinements.
-/
structure Protocol where
  Entity : Type uEntity
  Input : Crypto.SecPar → Entity → Type uInput
  Output : Crypto.SecPar → Entity → Type uOutput
  corruptionPolicy : CorruptionPolicy Entity
  machine :
    (entity : Entity) →
    InteractiveSystem
      (fun sec => Input sec entity)
      (fun sec => Output sec entity)

/-- Ideal functionalities currently have the same generic structure as protocols. -/
abbrev IdealFunctionality :=
  Protocol

end Crypto.Infrastructure.UC

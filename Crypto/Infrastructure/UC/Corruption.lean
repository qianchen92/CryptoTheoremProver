import Crypto.Infrastructure.UC.Message
import Mathlib.Data.Finset.Basic

namespace Crypto.Infrastructure.UC

universe uAddress

/--
An invariant and transition rule for the evolving set of corrupted addresses.

Erasure is intentionally absent: it belongs to the state transition semantics
of an ITM, while this policy only determines which corruption events are legal.
-/
structure CorruptionPolicy (Address : Type uAddress) [DecidableEq Address] where
  Admissible : Finset Address → Prop
  mayCorrupt : Finset Address → Address → Prop
  decidableMayCorrupt : ∀ corrupted target, Decidable (mayCorrupt corrupted target)
  fresh : ∀ {corrupted target}, mayCorrupt corrupted target → target ∉ corrupted
  preserves : ∀ {corrupted target},
    Admissible corrupted → mayCorrupt corrupted target →
      Admissible (insert target corrupted)

namespace CorruptionPolicy

variable {Address : Type uAddress} [DecidableEq Address]

/-- No address can ever be corrupted. -/
def incorruptible : CorruptionPolicy Address where
  Admissible := fun corrupted => corrupted = ∅
  mayCorrupt := fun _ _ => False
  decidableMayCorrupt := fun _ _ => inferInstance
  fresh := by
    intro corrupted target h
    exact h.elim
  preserves := by
    intro corrupted target _ h
    exact h.elim

/-- A fixed initially corrupted set with no adaptive corruption transitions. -/
def static (initial : Finset Address) : CorruptionPolicy Address where
  Admissible := fun corrupted => corrupted = initial
  mayCorrupt := fun _ _ => False
  decidableMayCorrupt := fun _ _ => inferInstance
  fresh := by
    intro corrupted target h
    exact h.elim
  preserves := by
    intro corrupted target _ h
    exact h.elim

/--
Adaptive corruption constrained by a predicate on the complete updated set.
-/
def dynamic
    (eligible : Finset Address → Prop)
    (decidableEligible : ∀ corrupted, Decidable (eligible corrupted)) :
    CorruptionPolicy Address where
  Admissible := eligible
  mayCorrupt := fun corrupted target =>
    target ∉ corrupted ∧ eligible (insert target corrupted)
  decidableMayCorrupt := fun corrupted target => by
    letI := decidableEligible (insert target corrupted)
    exact inferInstance
  fresh := fun h => h.1
  preserves := fun _ h => h.2

end CorruptionPolicy

end Crypto.Infrastructure.UC

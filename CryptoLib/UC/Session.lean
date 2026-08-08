import CryptoLib.Core.Infrastructure.SecurityParameter

namespace CryptoLib.UC

universe uTag uName

/--
A hierarchical UC session identifier.

The root separates independent top-level executions.  The path records nested
subroutine sessions without identifying a child from a different root.
-/
structure SID (Tag : Type uTag) where
  root : Tag
  path : List Tag
  deriving DecidableEq, Repr

namespace SID

variable {Tag : Type uTag}

/-- Allocate a direct child session under an existing session. -/
def child (sid : SID Tag) (tag : Tag) : SID Tag :=
  ⟨sid.root, sid.path ++ [tag]⟩

/-- `ancestor` is a prefix relation restricted to one top-level root. -/
def Ancestor (left right : SID Tag) : Prop :=
  left.root = right.root ∧ left.path.IsPrefix right.path

@[refl] theorem ancestor_refl (sid : SID Tag) : sid.Ancestor sid := by
  exact ⟨rfl, List.prefix_refl _⟩

theorem ancestor_trans {first second third : SID Tag}
    (hfirst : first.Ancestor second) (hsecond : second.Ancestor third) :
    first.Ancestor third := by
  exact ⟨hfirst.1.trans hsecond.1, hfirst.2.trans hsecond.2⟩

theorem ancestor_child (sid : SID Tag) (tag : Tag) :
    sid.Ancestor (sid.child tag) := by
  refine ⟨rfl, ?_⟩
  exact List.prefix_append _ _

end SID

/-- The address of one interactive machine instance in a session. -/
structure Address (Tag : Type uTag) (Name : Type uName) where
  sid : SID Tag
  name : Name
  deriving DecidableEq, Repr

end CryptoLib.UC

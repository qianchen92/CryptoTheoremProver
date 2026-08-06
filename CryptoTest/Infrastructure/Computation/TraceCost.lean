import Crypto.Infrastructure.Computation.Cost.Measure

namespace CryptoTest.Infrastructure.Computation

open Crypto.Infrastructure.Computation.Cost

universe uEvent

variable {Event : Type uEvent}

/-- A sequential resource whose exact value is the ordered event trace. -/
structure TraceCost (Event : Type uEvent) where
  events : List Event
deriving DecidableEq, Repr

namespace TraceCost

def empty (Event : Type uEvent) : TraceCost Event :=
  ⟨[]⟩

def append (left right : TraceCost Event) : TraceCost Event :=
  ⟨left.events ++ right.events⟩

end TraceCost

instance : Zero (TraceCost Event) :=
  ⟨TraceCost.empty Event⟩

instance : Add (TraceCost Event) :=
  ⟨TraceCost.append⟩

instance : AddMonoid (TraceCost Event) where
  add_assoc left middle right := by
    cases left with | mk leftEvents =>
      cases middle with | mk middleEvents =>
        cases right with | mk rightEvents =>
          exact congrArg TraceCost.mk
            (List.append_assoc leftEvents middleEvents rightEvents)
  zero_add cost := by cases cost; rfl
  add_zero cost := by
    cases cost with | mk events =>
      exact congrArg TraceCost.mk (List.append_nil events)
  nsmul := nsmulRec
  nsmul_zero _cost := rfl
  nsmul_succ _count _cost := rfl

/-- Equality order is sufficient for exact-path regression tests. -/
instance : LE (TraceCost Event) where
  le left right := left = right

instance : PartialOrder (TraceCost Event) where
  le_refl := fun _ => rfl
  le_trans := by
    intro left middle right leftMiddle middleRight
    change left = middle at leftMiddle
    change middle = right at middleRight
    exact leftMiddle.trans middleRight
  le_antisymm := by
    intro left right leftRight _rightLeft
    exact leftRight

instance : AddLeftMono (TraceCost Event) where
  elim := fun fixed _left _right leftRight =>
    congrArg (fun value => fixed + value) leftRight

instance : AddRightMono (TraceCost Event) where
  elim := fun fixed _left _right leftRight =>
    congrArg (fun value => value + fixed) leftRight

namespace TraceCost

/-- The reusable noncommutative exact-trace cost model. -/
abbrev costModel (Event : Type uEvent) : CostModel where
  Cost := TraceCost Event
  instAddMonoid := inferInstance
  instPartialOrder := inferInstance
  instAddLeftMono := inferInstance
  instAddRightMono := inferInstance

def singleton (event : Event) : TraceCost Event :=
  ⟨[event]⟩

/-- Runtime projection counting charged trace events. -/
def lengthMeasure (Event : Type uEvent) : NatMeasure (costModel Event) where
  toNat :=
    { toFun := fun cost => cost.events.length
      map_zero' := rfl
      map_add' := by
        intro left right
        change (left.events ++ right.events).length =
          left.events.length + right.events.length
        exact List.length_append }
  monotone_toNat := by
    intro left right hle
    change left = right at hle
    subst right
    rfl

end TraceCost

end CryptoTest.Infrastructure.Computation

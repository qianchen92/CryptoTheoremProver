import Crypto.Infrastructure.GameBased.Hybrid

namespace CryptoTest.Infrastructure.GameBased.Hybrid

open Crypto.Infrastructure.GameBased

/-- A deterministic Boolean game used to exercise the generic sequence API. -/
noncomputable def constantGame (value : Bool) :
    Crypto.Infrastructure.Computation.Game Bool :=
  fun _sec => PMF.pure value

/-- An arbitrary fixed number of identity transitions. -/
noncomputable def repeatedSequence (transitionCount : Nat) : Hybrid Bool :=
  Hybrid.ofList (constantGame false)
    (List.replicate transitionCount (constantGame false))

example (transitionCount : Nat) :
    (repeatedSequence transitionCount).length = transitionCount := by
  simp [repeatedSequence]

example :
    (Hybrid.ofList (constantGame false) []).first =
      (Hybrid.ofList (constantGame false) []).last :=
  rfl

theorem repeatedSequence_stepwise (transitionCount : Nat) :
    (repeatedSequence transitionCount).Stepwise (· = ·) := by
  rw [repeatedSequence, Hybrid.ofList_stepwise_iff_isChain]
  simp [List.isChain_cons_eq_iff_eq_replicate]

example (transitionCount : Nat) :
    (repeatedSequence transitionCount).first =
      (repeatedSequence transitionCount).last := by
  apply Hybrid.endpoints_related (relation := (· = ·))
  · exact fun _game => rfl
  · exact fun hleft hright => hleft.trans hright
  · exact repeatedSequence_stepwise transitionCount

end CryptoTest.Infrastructure.GameBased.Hybrid

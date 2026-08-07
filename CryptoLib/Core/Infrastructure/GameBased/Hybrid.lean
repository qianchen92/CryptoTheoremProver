import CryptoLib.Core.Infrastructure.GameBased.Indistinguishability
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.List.Chain

namespace CryptoLib.Core.Infrastructure.GameBased

universe uOutcome

/--
A finite hybrid sequence with `length` transitions and `length + 1` games.

Using a finite index makes the declared length part of the interface rather
than leaving games outside the hybrid's range observable.
-/
structure Hybrid (Outcome : Type uOutcome) where
  length : Nat
  securityGame : Fin (length + 1) → CryptoLib.Core.Infrastructure.Computation.Game Outcome

namespace Hybrid

variable {Outcome : Type uOutcome}

/-- Build an arbitrary fixed-length game sequence from its first game and the
remaining games. The resulting sequence has `games.length` transitions. -/
def ofList
    (firstGame : CryptoLib.Core.Infrastructure.Computation.Game Outcome)
    (games : List (CryptoLib.Core.Infrastructure.Computation.Game Outcome)) :
    Hybrid Outcome where
  length := games.length
  securityGame := fun index => (firstGame :: games).get index

@[simp] theorem ofList_length
    (firstGame : CryptoLib.Core.Infrastructure.Computation.Game Outcome)
    (games : List (CryptoLib.Core.Infrastructure.Computation.Game Outcome)) :
    (ofList firstGame games).length = games.length :=
  rfl

@[simp] theorem ofList_securityGame
    (firstGame : CryptoLib.Core.Infrastructure.Computation.Game Outcome)
    (games : List (CryptoLib.Core.Infrastructure.Computation.Game Outcome))
    (index : Fin (games.length + 1)) :
    (ofList firstGame games).securityGame index =
      (firstGame :: games).get index :=
  rfl

/-- The first game in a finite hybrid sequence. -/
def first (hybrid : Hybrid Outcome) :
    CryptoLib.Core.Infrastructure.Computation.Game Outcome :=
  hybrid.securityGame 0

/-- The last game in a finite hybrid sequence. -/
def last (hybrid : Hybrid Outcome) :
    CryptoLib.Core.Infrastructure.Computation.Game Outcome :=
  hybrid.securityGame (Fin.last hybrid.length)

/-- The game immediately before one transition. -/
def before (hybrid : Hybrid Outcome) (step : Fin hybrid.length) :
    CryptoLib.Core.Infrastructure.Computation.Game Outcome :=
  hybrid.securityGame step.castSucc

/-- The game immediately after one transition. -/
def after (hybrid : Hybrid Outcome) (step : Fin hybrid.length) :
    CryptoLib.Core.Infrastructure.Computation.Game Outcome :=
  hybrid.securityGame step.succ

@[simp] theorem ofList_first
    (firstGame : CryptoLib.Core.Infrastructure.Computation.Game Outcome)
    (games : List (CryptoLib.Core.Infrastructure.Computation.Game Outcome)) :
    (ofList firstGame games).first = firstGame :=
  rfl

@[simp] theorem ofList_last
    (firstGame : CryptoLib.Core.Infrastructure.Computation.Game Outcome)
    (games : List (CryptoLib.Core.Infrastructure.Computation.Game Outcome)) :
    (ofList firstGame games).last =
      (firstGame :: games).getLast (by simp) := by
  exact (List.getLast_eq_getElem _).symm

/-- A relation holds at every adjacent transition of a game sequence. -/
def Stepwise
    (hybrid : Hybrid Outcome)
    (relation :
      CryptoLib.Core.Infrastructure.Computation.Game Outcome →
        CryptoLib.Core.Infrastructure.Computation.Game Outcome → Prop) : Prop :=
  ∀ step : Fin hybrid.length,
    relation (hybrid.before step) (hybrid.after step)

/-- For list-built sequences, indexed adjacent steps are exactly `List.IsChain`. -/
theorem ofList_stepwise_iff_isChain
    (firstGame : CryptoLib.Core.Infrastructure.Computation.Game Outcome)
    (games : List (CryptoLib.Core.Infrastructure.Computation.Game Outcome))
    (relation :
      CryptoLib.Core.Infrastructure.Computation.Game Outcome →
        CryptoLib.Core.Infrastructure.Computation.Game Outcome → Prop) :
    (ofList firstGame games).Stepwise relation ↔
      (firstGame :: games).IsChain relation := by
  constructor
  · intro hsteps
    rw [List.isChain_iff_getElem]
    intro index hindex
    have hgames : index < games.length := by
      simpa using hindex
    simpa [Stepwise, before, after, ofList] using
      hsteps ⟨index, hgames⟩
  · intro hchain step
    have hindex : step.val + 1 < (firstGame :: games).length :=
      Nat.add_lt_add_right step.isLt 1
    simpa [Stepwise, before, after, ofList] using
      hchain.getElem step.val hindex

/-- Adjacent steps for a reflexive transitive relation connect the first game
to every indexed game. -/
theorem first_related_securityGame
    (hybrid : Hybrid Outcome)
    (relation :
      CryptoLib.Core.Infrastructure.Computation.Game Outcome →
        CryptoLib.Core.Infrastructure.Computation.Game Outcome → Prop)
    (hrefl : ∀ game, relation game game)
    (htrans : ∀ {left middle right},
      relation left middle → relation middle right → relation left right)
    (hsteps : hybrid.Stepwise relation)
    (index : Fin (hybrid.length + 1)) :
    relation hybrid.first (hybrid.securityGame index) := by
  induction index using Fin.induction with
  | zero => exact hrefl hybrid.first
  | succ step ih => exact htrans ih (hsteps step)

/-- Adjacent steps for a reflexive transitive relation connect the endpoints. -/
theorem endpoints_related
    (hybrid : Hybrid Outcome)
    (relation :
      CryptoLib.Core.Infrastructure.Computation.Game Outcome →
        CryptoLib.Core.Infrastructure.Computation.Game Outcome → Prop)
    (hrefl : ∀ game, relation game game)
    (htrans : ∀ {left middle right},
      relation left middle → relation middle right → relation left right)
    (hsteps : hybrid.Stepwise relation) :
    relation hybrid.first hybrid.last := by
  exact hybrid.first_related_securityGame relation hrefl htrans hsteps
    (Fin.last hybrid.length)

/-- Every adjacent pair in a Boolean hybrid sequence is indistinguishable. -/
def StepIndistinguishable (hybrid : Hybrid Bool) : Prop :=
  hybrid.Stepwise Indistinguishable

/-- For list-built Boolean hybrids, adjacent indistinguishability is exactly a
chain of indistinguishable games. -/
theorem ofList_stepIndistinguishable_iff
    (firstGame : CryptoLib.Core.Infrastructure.Computation.Game Bool)
    (games : List (CryptoLib.Core.Infrastructure.Computation.Game Bool)) :
    (ofList firstGame games).StepIndistinguishable ↔
      (firstGame :: games).IsChain Indistinguishable :=
  ofList_stepwise_iff_isChain firstGame games Indistinguishable

/-- Adjacent indistinguishability connects the first game to any indexed game. -/
theorem first_indistinguishable_securityGame
    (hybrid : Hybrid Bool) (hsteps : hybrid.StepIndistinguishable)
    (index : Fin (hybrid.length + 1)) :
    Indistinguishable hybrid.first (hybrid.securityGame index) := by
  exact hybrid.first_related_securityGame Indistinguishable
    Indistinguishable.refl (fun hleft hright => hleft.trans hright)
    hsteps index

/-- A finite sequence of indistinguishable adjacent games has indistinguishable endpoints. -/
theorem endpoints_indistinguishable
    (hybrid : Hybrid Bool) (hsteps : hybrid.StepIndistinguishable) :
    Indistinguishable hybrid.first hybrid.last := by
  exact hybrid.endpoints_related Indistinguishable
    Indistinguishable.refl (fun hleft hright => hleft.trans hright) hsteps

private theorem endpointAdvantage_le_sum_aux
    (length : Nat)
    (games : Fin (length + 1) → CryptoLib.Core.Infrastructure.Computation.Game Bool)
    (sec : CryptoLib.Core.SecPar) :
    Advantage (games 0) (games (Fin.last length)) sec ≤
      ∑ step : Fin length,
        Advantage (games step.castSucc) (games step.succ) sec := by
  induction length with
  | zero =>
      simp [Advantage]
  | succ length ih =>
      let prefixGames : Fin (length + 1) →
          CryptoLib.Core.Infrastructure.Computation.Game Bool :=
        fun index => games index.castSucc
      calc
        Advantage (games 0) (games (Fin.last (length + 1))) sec ≤
            Advantage (games 0) (games (Fin.last length).castSucc) sec +
              Advantage (games (Fin.last length).castSucc)
                (games (Fin.last (length + 1))) sec :=
          Advantage.triangle sec
        _ ≤ (∑ step : Fin length,
              Advantage (prefixGames step.castSucc) (prefixGames step.succ) sec) +
              Advantage (games (Fin.last length).castSucc)
                (games (Fin.last (length + 1))) sec := by
          apply add_le_add
          · simpa [prefixGames] using ih prefixGames
          · exact le_rfl
        _ = ∑ step : Fin (length + 1),
              Advantage (games step.castSucc) (games step.succ) sec := by
          rw [Fin.sum_univ_castSucc]
          simp [prefixGames, Fin.succ_last]

/-- The endpoint advantage of any finite hybrid sequence is at most the sum of
its adjacent-step advantages. -/
theorem endpointAdvantage_le_sum
    (hybrid : Hybrid Bool) (sec : CryptoLib.Core.SecPar) :
    Advantage hybrid.first hybrid.last sec ≤
      ∑ step : Fin hybrid.length,
        Advantage (hybrid.before step) (hybrid.after step) sec := by
  simpa [first, last, before, after] using
    endpointAdvantage_le_sum_aux hybrid.length hybrid.securityGame sec

end Hybrid

end CryptoLib.Core.Infrastructure.GameBased

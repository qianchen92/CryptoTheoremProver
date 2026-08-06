import Crypto.Infrastructure.GameBased.Indistinguishability
import Mathlib.Algebra.BigOperators.Fin

namespace Crypto.Infrastructure.GameBased

universe uOutcome

/--
A finite hybrid sequence with `length` transitions and `length + 1` games.

Using a finite index makes the declared length part of the interface rather
than leaving games outside the hybrid's range observable.
-/
structure Hybrid (Outcome : Type uOutcome) where
  length : Nat
  securityGame : Fin (length + 1) → Crypto.Infrastructure.Computation.Game Outcome

namespace Hybrid

variable {Outcome : Type uOutcome}

/-- The first game in a finite hybrid sequence. -/
def first (hybrid : Hybrid Outcome) :
    Crypto.Infrastructure.Computation.Game Outcome :=
  hybrid.securityGame 0

/-- The last game in a finite hybrid sequence. -/
def last (hybrid : Hybrid Outcome) :
    Crypto.Infrastructure.Computation.Game Outcome :=
  hybrid.securityGame (Fin.last hybrid.length)

/-- The game immediately before one transition. -/
def before (hybrid : Hybrid Outcome) (step : Fin hybrid.length) :
    Crypto.Infrastructure.Computation.Game Outcome :=
  hybrid.securityGame step.castSucc

/-- The game immediately after one transition. -/
def after (hybrid : Hybrid Outcome) (step : Fin hybrid.length) :
    Crypto.Infrastructure.Computation.Game Outcome :=
  hybrid.securityGame step.succ

/-- Every adjacent pair in a Boolean hybrid sequence is indistinguishable. -/
def StepIndistinguishable (hybrid : Hybrid Bool) : Prop :=
  ∀ step : Fin hybrid.length,
    Indistinguishable (hybrid.before step) (hybrid.after step)

/-- Adjacent indistinguishability connects the first game to any indexed game. -/
theorem first_indistinguishable_securityGame
    (hybrid : Hybrid Bool) (hsteps : hybrid.StepIndistinguishable)
    (index : Fin (hybrid.length + 1)) :
    Indistinguishable hybrid.first (hybrid.securityGame index) := by
  induction index using Fin.induction with
  | zero =>
      exact Indistinguishable.refl hybrid.first
  | succ step ih =>
      exact ih.trans (hsteps step)

/-- A finite sequence of indistinguishable adjacent games has indistinguishable endpoints. -/
theorem endpoints_indistinguishable
    (hybrid : Hybrid Bool) (hsteps : hybrid.StepIndistinguishable) :
    Indistinguishable hybrid.first hybrid.last := by
  exact hybrid.first_indistinguishable_securityGame hsteps (Fin.last hybrid.length)

private theorem endpointAdvantage_le_sum_aux
    (length : Nat)
    (games : Fin (length + 1) → Crypto.Infrastructure.Computation.Game Bool)
    (sec : Crypto.SecPar) :
    Advantage (games 0) (games (Fin.last length)) sec ≤
      ∑ step : Fin length,
        Advantage (games step.castSucc) (games step.succ) sec := by
  induction length with
  | zero =>
      simp [Advantage]
  | succ length ih =>
      let prefixGames : Fin (length + 1) →
          Crypto.Infrastructure.Computation.Game Bool :=
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
    (hybrid : Hybrid Bool) (sec : Crypto.SecPar) :
    Advantage hybrid.first hybrid.last sec ≤
      ∑ step : Fin hybrid.length,
        Advantage (hybrid.before step) (hybrid.after step) sec := by
  simpa [first, last, before, after] using
    endpointAdvantage_le_sum_aux hybrid.length hybrid.securityGame sec

end Hybrid

end Crypto.Infrastructure.GameBased

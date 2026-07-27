import Crypto.Infrastructure.Computation.Game

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

end Crypto.Infrastructure.GameBased

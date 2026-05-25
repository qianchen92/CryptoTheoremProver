import Crypto.Core.Game

namespace Crypto.Security

universe uOutcome

/-- A finite hybrid sequence of games indexed by natural numbers. -/
structure Hybrid (Outcome : Type uOutcome) where
  length : Nat
  game : Nat → Crypto.Core.Game Outcome

end Crypto.Security

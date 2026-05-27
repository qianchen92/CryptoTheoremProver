import Crypto.Infrastructure.Computation.Game

namespace Crypto.Infrastructure.GameBased

universe uOutcome

/-- A finite hybrid sequence of games indexed by natural numbers. -/
structure Hybrid (Outcome : Type uOutcome) where
  length : Nat
  securityGame : Nat → Crypto.Infrastructure.Computation.Game Outcome

end Crypto.Infrastructure.GameBased

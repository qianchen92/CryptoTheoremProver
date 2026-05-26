import Crypto.Infrastructure.Computation.Game
import Mathlib.Data.Real.Basic

namespace Crypto.Infrastructure.GameBased

/-- Acceptance probability of a boolean game. -/
noncomputable def AcceptProb
    (G : Crypto.Infrastructure.Computation.Game Bool) (sec : Crypto.SecPar) : Real :=
  (G sec true).toReal

/-- Absolute difference between two boolean games' acceptance probabilities. -/
noncomputable def Advantage
    (G₀ G₁ : Crypto.Infrastructure.Computation.Game Bool) (sec : Crypto.SecPar) : Real :=
  |AcceptProb G₀ sec - AcceptProb G₁ sec|

end Crypto.Infrastructure.GameBased

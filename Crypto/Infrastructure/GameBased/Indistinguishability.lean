import Crypto.Infrastructure.Asymptotic.Bounds
import Crypto.Infrastructure.GameBased.Advantage

namespace Crypto.Infrastructure.GameBased

/-- Two boolean games are indistinguishable when their advantage is negligible. -/
def Indistinguishable (G₀ G₁ : Crypto.Infrastructure.Computation.Game Bool) : Prop :=
  Crypto.Infrastructure.Asymptotic.IsNegligible (Advantage G₀ G₁)

end Crypto.Infrastructure.GameBased

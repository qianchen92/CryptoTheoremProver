import Crypto.Foundation.Asymptotics
import Crypto.Security.Advantage

namespace Crypto.Security

/-- Two boolean games are indistinguishable when their advantage is negligible. -/
def Indistinguishable (G₀ G₁ : Crypto.Core.Game Bool) : Prop :=
  Crypto.Foundation.IsNegligible (Advantage G₀ G₁)

end Crypto.Security

import Crypto.Infrastructure.Asymptotic.Bounds
import Crypto.Infrastructure.GameBased.Advantage

namespace Crypto.Infrastructure.GameBased

/-- Two boolean games are indistinguishable when their advantage is negligible. -/
def Indistinguishable
    (left right : Crypto.Infrastructure.Computation.Game Bool) : Prop :=
  Crypto.Infrastructure.Asymptotic.IsNegligible (Advantage left right)

end Crypto.Infrastructure.GameBased

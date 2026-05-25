import Crypto.Core.Computation
import Crypto.Foundation.Asymptotics

namespace Crypto.Complexity

universe uIn uOut

/-- A computation whose path costs are uniformly bounded by a polynomial. -/
def IsPolyCost {Input : Type uIn} {Output : Type uOut}
    (C : Crypto.Core.Computation Input Output) : Prop :=
  ∃ bound : Crypto.SecPar → Nat,
    Crypto.Core.Computation.CostBound C bound ∧ Crypto.Foundation.IsPolyBounded bound

end Crypto.Complexity

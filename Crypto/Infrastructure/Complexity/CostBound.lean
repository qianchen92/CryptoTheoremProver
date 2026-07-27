import Crypto.Infrastructure.Computation.Randomized
import Crypto.Infrastructure.Asymptotic.Bounds

namespace Crypto.Infrastructure.Complexity

universe uIn uOut

/-- A computation whose path costs are uniformly bounded by a polynomial. -/
def IsPolyCost {Input : Type uIn} {Output : Type uOut}
    (C : Crypto.Infrastructure.Computation.RandomizedComputation Input Output) : Prop :=
  ∃ bound : Crypto.SecPar → Nat,
    Crypto.Infrastructure.Computation.RandomizedComputation.CostBound C bound ∧
      Crypto.Infrastructure.Asymptotic.IsPolyBounded bound

/-- A dependent computation whose path costs are uniformly bounded by a polynomial. -/
def IsPolyDependentCost
    {Input : Type uIn} {Output : Input → Type uOut}
    (C : Crypto.Infrastructure.Computation.DependentRandomizedComputation Input Output) : Prop :=
  ∃ bound : Crypto.SecPar → Nat,
    Crypto.Infrastructure.Computation.DependentRandomizedComputation.CostBound C bound ∧
      Crypto.Infrastructure.Asymptotic.IsPolyBounded bound

end Crypto.Infrastructure.Complexity

import Crypto.Infrastructure.Asymptotic.SecurityParameter
import Crypto.Infrastructure.Computation.Cost.Distribution

namespace Crypto.Infrastructure.Computation

universe uIn uOut

/-- A reusable randomized computation indexed by the security parameter with costed output. -/
abbrev RandomizedComputation (Input : Type uIn) (Output : Type uOut) :=
  Crypto.SecPar → Input → Crypto.Infrastructure.Computation.Cost.RandCosted Output

namespace RandomizedComputation

/-- The ordinary output distribution induced by a costed computation. -/
noncomputable def valueDist {Input : Type uIn} {Output : Type uOut}
    (C : RandomizedComputation Input Output) (sec : Crypto.SecPar) (input : Input) :
    PMF Output :=
  Crypto.Infrastructure.Computation.Cost.RandCosted.valueDist (C sec input)

/-- The cost distribution induced by a costed computation. -/
noncomputable def costDist {Input : Type uIn} {Output : Type uOut}
    (C : RandomizedComputation Input Output) (sec : Crypto.SecPar) (input : Input) :
    PMF Crypto.Infrastructure.Computation.Cost.Cost :=
  Crypto.Infrastructure.Computation.Cost.RandCosted.costDist (C sec input)

/-- A uniform upper bound on every execution path cost of a computation. -/
def CostBound {Input : Type uIn} {Output : Type uOut}
    (C : RandomizedComputation Input Output) (bound : Crypto.SecPar → Nat) : Prop :=
  ∀ sec input result, result ∈ (C sec input).support → result.cost ≤ bound sec

end RandomizedComputation

end Crypto.Infrastructure.Computation

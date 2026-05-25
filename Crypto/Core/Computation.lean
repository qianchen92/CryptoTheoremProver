import Crypto.Foundation.SecurityParameter
import Crypto.Core.Cost.Distribution

namespace Crypto.Core

universe uIn uOut

/-- A reusable randomized computation indexed by the security parameter with costed output. -/
abbrev Computation (Input : Type uIn) (Output : Type uOut) :=
  Crypto.SecPar → Input → Crypto.Core.Cost.RandCosted Output

namespace Computation

/-- The ordinary output distribution induced by a costed computation. -/
noncomputable def valueDist {Input : Type uIn} {Output : Type uOut}
    (C : Computation Input Output) (sec : Crypto.SecPar) (input : Input) : PMF Output :=
  Crypto.Core.Cost.RandCosted.valueDist (C sec input)

/-- The cost distribution induced by a costed computation. -/
noncomputable def costDist {Input : Type uIn} {Output : Type uOut}
    (C : Computation Input Output) (sec : Crypto.SecPar) (input : Input) :
    PMF Crypto.Core.Cost.Cost :=
  Crypto.Core.Cost.RandCosted.costDist (C sec input)

/-- A uniform upper bound on every execution path cost of a computation. -/
def CostBound {Input : Type uIn} {Output : Type uOut}
    (C : Computation Input Output) (bound : Crypto.SecPar → Nat) : Prop :=
  ∀ sec input result, result ∈ (C sec input).support → result.cost ≤ bound sec

end Computation

end Crypto.Core

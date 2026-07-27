import Crypto.Infrastructure.Asymptotic.SecurityParameter
import Crypto.Infrastructure.Computation.Cost.Distribution

namespace Crypto.Infrastructure.Computation

open Crypto.Infrastructure.Computation.Cost

universe uIn uOut

/-- A reusable randomized computation indexed by the security parameter with costed output. -/
abbrev RandomizedComputation (Input : Type uIn) (Output : Type uOut) :=
  Crypto.SecPar → Input → RandCosted Output

namespace RandomizedComputation

/-- The ordinary output distribution induced by a costed computation. -/
noncomputable def valueDist {Input : Type uIn} {Output : Type uOut}
    (C : RandomizedComputation Input Output) (sec : Crypto.SecPar) (input : Input) :
    PMF Output :=
  RandCosted.valueDist (C sec input)

/-- The cost distribution induced by a costed computation. -/
noncomputable def costDist {Input : Type uIn} {Output : Type uOut}
    (C : RandomizedComputation Input Output) (sec : Crypto.SecPar) (input : Input) :
    PMF Cost :=
  RandCosted.costDist (C sec input)

/-- A uniform upper bound on every execution path cost of a computation. -/
def CostBound {Input : Type uIn} {Output : Type uOut}
    (C : RandomizedComputation Input Output) (bound : Crypto.SecPar → Cost) : Prop :=
  ∀ sec input result, result ∈ (C sec input).support → result.cost ≤ bound sec

end RandomizedComputation

/--
A reusable randomized computation whose output type may depend on its input.

As with `RandomizedComputation`, every execution path carries an explicit cost.
-/
abbrev DependentRandomizedComputation
    (Input : Type uIn) (Output : Input → Type uOut) :=
  (sec : Crypto.SecPar) → (input : Input) →
    RandCosted (Output input)

namespace DependentRandomizedComputation

/-- The ordinary output distribution induced by a dependent costed computation. -/
noncomputable def valueDist
    {Input : Type uIn} {Output : Input → Type uOut}
    (C : DependentRandomizedComputation Input Output)
    (sec : Crypto.SecPar) (input : Input) :
    PMF (Output input) :=
  RandCosted.valueDist (C sec input)

/-- The cost distribution induced by a dependent costed computation. -/
noncomputable def costDist
    {Input : Type uIn} {Output : Input → Type uOut}
    (C : DependentRandomizedComputation Input Output)
    (sec : Crypto.SecPar) (input : Input) :
    PMF Cost :=
  RandCosted.costDist (C sec input)

/-- A uniform upper bound on every execution path of a dependent computation. -/
def CostBound
    {Input : Type uIn} {Output : Input → Type uOut}
    (C : DependentRandomizedComputation Input Output)
    (bound : Crypto.SecPar → Cost) : Prop :=
  ∀ sec input result, result ∈ (C sec input).support → result.cost ≤ bound sec

end DependentRandomizedComputation

end Crypto.Infrastructure.Computation

import Crypto.Infrastructure.Asymptotic.SecurityParameter
import Crypto.Infrastructure.Computation.Cost.Basic

namespace Crypto.Infrastructure.Computation

open Crypto.Infrastructure.Computation.Cost

universe uCost uIn uOut

/-- A security-parameter-indexed randomized computation over an exact cost model. -/
abbrev RandomizedComputationT (M : CostModel.{uCost})
    (Input : Type uIn) (Output : Type uOut) :=
  Crypto.SecPar → Input → RandCostedT M Output

namespace RandomizedComputationT

/-- The ordinary output distribution induced by a generic costed computation. -/
noncomputable def valueDist {M : CostModel.{uCost}}
    {Input : Type uIn} {Output : Type uOut}
    (C : RandomizedComputationT M Input Output)
    (sec : Crypto.SecPar) (input : Input) : PMF Output :=
  RandCostedT.valueDist (C sec input)

/-- The exact resource distribution induced by a generic costed computation. -/
noncomputable def costDist {M : CostModel.{uCost}}
    {Input : Type uIn} {Output : Type uOut}
    (C : RandomizedComputationT M Input Output)
    (sec : Crypto.SecPar) (input : Input) : PMF M.Cost :=
  RandCostedT.costDist (C sec input)

/-- A uniform upper bound on every exact execution-path cost. -/
def CostBound {M : CostModel.{uCost}}
    {Input : Type uIn} {Output : Type uOut}
    (C : RandomizedComputationT M Input Output)
    (bound : Crypto.SecPar → M.Cost) : Prop :=
  ∀ sec input result, result ∈ (C sec input).support →
    M.instPartialOrder.le result.cost (bound sec)

end RandomizedComputationT

/-- A reusable randomized computation indexed by the security parameter with costed output. -/
abbrev RandomizedComputation (Input : Type uIn) (Output : Type uOut) :=
  RandomizedComputationT natCostModel Input Output

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
abbrev DependentRandomizedComputationT (M : CostModel.{uCost})
    (Input : Type uIn) (Output : Input → Type uOut) :=
  (sec : Crypto.SecPar) → (input : Input) →
    RandCostedT M (Output input)

namespace DependentRandomizedComputationT

/-- The value distribution of a dependent generic-cost computation. -/
noncomputable def valueDist {M : CostModel.{uCost}}
    {Input : Type uIn} {Output : Input → Type uOut}
    (C : DependentRandomizedComputationT M Input Output)
    (sec : Crypto.SecPar) (input : Input) : PMF (Output input) :=
  RandCostedT.valueDist (C sec input)

/-- The exact cost distribution of a dependent generic-cost computation. -/
noncomputable def costDist {M : CostModel.{uCost}}
    {Input : Type uIn} {Output : Input → Type uOut}
    (C : DependentRandomizedComputationT M Input Output)
    (sec : Crypto.SecPar) (input : Input) : PMF M.Cost :=
  RandCostedT.costDist (C sec input)

/-- A uniform bound on every path of a dependent generic-cost computation. -/
def CostBound {M : CostModel.{uCost}}
    {Input : Type uIn} {Output : Input → Type uOut}
    (C : DependentRandomizedComputationT M Input Output)
    (bound : Crypto.SecPar → M.Cost) : Prop :=
  ∀ sec input result, result ∈ (C sec input).support →
    M.instPartialOrder.le result.cost (bound sec)

end DependentRandomizedComputationT

abbrev DependentRandomizedComputation
    (Input : Type uIn) (Output : Input → Type uOut) :=
  DependentRandomizedComputationT natCostModel Input Output

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

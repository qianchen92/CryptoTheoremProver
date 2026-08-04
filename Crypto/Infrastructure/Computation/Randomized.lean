import Crypto.Infrastructure.SecurityParameter
import Crypto.Infrastructure.Computation.Cost.PathBound

namespace Crypto.Infrastructure.Computation

open Crypto.Infrastructure.Computation.Cost

universe uCost uIn uOut uMapped

/--
A security-parameter-indexed randomized computation over one exact cost model.

Both the input type and the output family may depend on the security parameter;
the output may additionally depend on the concrete input.  This is the sole
randomized-computation core used by ordinary and dependent machines.
-/
abbrev RandomizedComputation
    (M : CostModel.{uCost})
    (Input : Crypto.SecPar → Type uIn)
    (Output : (sec : Crypto.SecPar) → Input sec → Type uOut) :=
  (sec : Crypto.SecPar) → (input : Input sec) →
    RandCosted M (Output sec input)

namespace RandomizedComputation

noncomputable section

/-- Forget exact costs and expose the ordinary dependent output distribution. -/
def valueDist {M : CostModel.{uCost}}
    {Input : Crypto.SecPar → Type uIn}
    {Output : (sec : Crypto.SecPar) → Input sec → Type uOut}
    (computation : RandomizedComputation M Input Output)
    (sec : Crypto.SecPar) (input : Input sec) :
    PMF (Output sec input) :=
  RandCosted.valueDist (computation sec input)

/-- Expose the exact resource distribution at one security parameter and input. -/
def costDist {M : CostModel.{uCost}}
    {Input : Crypto.SecPar → Type uIn}
    {Output : (sec : Crypto.SecPar) → Input sec → Type uOut}
    (computation : RandomizedComputation M Input Output)
    (sec : Crypto.SecPar) (input : Input sec) : PMF M.Cost :=
  RandCosted.costDist (computation sec input)

/-- A deterministic dependent function viewed as a zero-cost computation. -/
def pure
    (M : CostModel.{uCost})
    {Input : Crypto.SecPar → Type uIn}
    {Output : (sec : Crypto.SecPar) → Input sec → Type uOut}
    (value : (sec : Crypto.SecPar) → (input : Input sec) → Output sec input) :
    RandomizedComputation M Input Output :=
  fun sec input => RandCosted.pure M (value sec input)

/-- Apply a security-parameter- and input-dependent value map without changing costs. -/
def map {M : CostModel.{uCost}}
    {Input : Crypto.SecPar → Type uIn}
    {Output : (sec : Crypto.SecPar) → Input sec → Type uOut}
    {Mapped : (sec : Crypto.SecPar) → Input sec → Type uMapped}
    (transform :
      (sec : Crypto.SecPar) → (input : Input sec) →
        Output sec input → Mapped sec input)
    (computation : RandomizedComputation M Input Output) :
    RandomizedComputation M Input Mapped :=
  fun sec input => RandCosted.map (transform sec input) (computation sec input)

@[simp] theorem valueDist_pure
    (M : CostModel.{uCost})
    {Input : Crypto.SecPar → Type uIn}
    {Output : (sec : Crypto.SecPar) → Input sec → Type uOut}
    (value : (sec : Crypto.SecPar) → (input : Input sec) → Output sec input)
    (sec : Crypto.SecPar) (input : Input sec) :
    valueDist (pure M value) sec input = PMF.pure (value sec input) := by
  exact RandCosted.valueDist_pure M (value sec input)

@[simp] theorem valueDist_map {M : CostModel.{uCost}}
    {Input : Crypto.SecPar → Type uIn}
    {Output : (sec : Crypto.SecPar) → Input sec → Type uOut}
    {Mapped : (sec : Crypto.SecPar) → Input sec → Type uMapped}
    (transform :
      (sec : Crypto.SecPar) → (input : Input sec) →
        Output sec input → Mapped sec input)
    (computation : RandomizedComputation M Input Output)
    (sec : Crypto.SecPar) (input : Input sec) :
    valueDist (map transform computation) sec input =
      PMF.map (transform sec input) (valueDist computation sec input) := by
  exact RandCosted.valueDist_map (transform sec input) (computation sec input)

end

end RandomizedComputation

end Crypto.Infrastructure.Computation

import Crypto.Core.Protocol.Computation

namespace Crypto.Core.Protocol

universe uIn uOut

/-- A uniform upper bound on every execution path cost of a protocol computation. -/
def CostBound {Input : Type uIn} {Output : Type uOut}
    (C : Computation Input Output) (bound : Crypto.SecPar → Nat) : Prop :=
  ∀ sec input result, result ∈ (C sec input).support → result.cost ≤ bound sec

abbrev RuntimeBound {Input : Type uIn} {Output : Type uOut}
    (C : Computation Input Output) (bound : Crypto.SecPar → Nat) : Prop :=
  CostBound C bound

end Crypto.Core.Protocol

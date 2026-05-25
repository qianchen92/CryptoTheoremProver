import Crypto.Foundation.SecurityParameter
import Crypto.Core.Cost.Distribution

namespace Crypto.Core.Protocol

universe uIn uOut

/-- A protocol computation indexed by security parameter with randomized costed output. -/
abbrev Computation (Input : Type uIn) (Output : Type uOut) :=
  Crypto.SecPar → Input → Crypto.Core.Cost.RandCosted Output

namespace Computation

/-- The ordinary output distribution induced by a costed protocol computation. -/
noncomputable def valueDist {Input : Type uIn} {Output : Type uOut}
    (C : Computation Input Output) (sec : Crypto.SecPar) (input : Input) : PMF Output :=
  Crypto.Core.Cost.RandCosted.valueDist (C sec input)

/-- The cost distribution induced by a costed protocol computation. -/
noncomputable def costDist {Input : Type uIn} {Output : Type uOut}
    (C : Computation Input Output) (sec : Crypto.SecPar) (input : Input) :
    PMF Crypto.Core.Cost.Cost :=
  Crypto.Core.Cost.RandCosted.costDist (C sec input)

end Computation

end Crypto.Core.Protocol

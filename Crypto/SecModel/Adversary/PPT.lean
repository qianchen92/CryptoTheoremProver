import Crypto.Complexity.Machine
import Crypto.SecModel.Adversary.Probabilistic

namespace Crypto.SecModel.Adversary

open Crypto.Complexity

universe uIn uOut

/-- A polynomial-time probabilistic adversary. -/
structure PPTAdversary (Input : Type uIn) (Output : Type uOut)
    extends ProbabilisticAdversary Input Output where
  runtime : Crypto.SecPar → Nat
  runtime_isPoly : IsPolyBounded runtime

namespace PPTAdversary

variable {Input : Type uIn} {Output : Type uOut}

/-- Forget the adversary-specific wrapper and view a PPT adversary as a semantic PPT machine. -/
def toPPTMachine (Adv : PPTAdversary Input Output) :
    Crypto.Complexity.PPTMachine Input Output where
  run := Adv.run
  runtime := Adv.runtime
  runtime_isPoly := Adv.runtime_isPoly

/-- Use a semantic PPT machine as a PPT adversary. -/
def ofPPTMachine (M : Crypto.Complexity.PPTMachine Input Output) : PPTAdversary Input Output where
  run := M.run
  runtime := M.runtime
  runtime_isPoly := M.runtime_isPoly

@[simp] theorem toPPTMachine_run (Adv : PPTAdversary Input Output)
    (sec : Crypto.SecPar) (input : Input) :
    Adv.toPPTMachine.run sec input = Adv.run sec input :=
  rfl

@[simp] theorem ofPPTMachine_run (M : Crypto.Complexity.PPTMachine Input Output)
    (sec : Crypto.SecPar) (input : Input) :
    (ofPPTMachine M).run sec input = M.run sec input :=
  rfl

@[simp] theorem toPPTMachine_runtime (Adv : PPTAdversary Input Output) :
    Adv.toPPTMachine.runtime = Adv.runtime :=
  rfl

@[simp] theorem ofPPTMachine_runtime (M : Crypto.Complexity.PPTMachine Input Output) :
    (ofPPTMachine M).runtime = M.runtime :=
  rfl

end PPTAdversary

abbrev DistinguishingAdversary (X : Type uIn) := PPTAdversary X Bool

end Crypto.SecModel.Adversary

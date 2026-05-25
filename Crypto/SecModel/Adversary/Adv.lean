namespace Crypto.SecModel.Adversary
universe uIn uOut

structure Adversary (In : Type uIn) (Out : Type uOut) where
  run : In → Out

end Crypto.SecModel.Adversary

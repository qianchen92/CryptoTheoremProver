namespace Crypto.SecModel.Adversary

universe uIn uOut

/-- A deterministic adversary without security-parameter or randomness structure. -/
structure Adversary (In : Type uIn) (Out : Type uOut) where
  run : In → Out

end Crypto.SecModel.Adversary

import Mathlib.Probability.ProbabilityMassFunction.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Basic

namespace LinearFunctionFamily

universe uDomain uCoDomain uKey uScalar

structure LFF
    (𝔽 : Type uScalar) [Field 𝔽] [Fintype 𝔽]
    (Domain : Type uDomain) [AddCommGroup Domain] [Module 𝔽 Domain]
    [FiniteDimensional 𝔽 Domain]
    (CoDomain : Type uCoDomain) [AddCommGroup CoDomain] [Module 𝔽 CoDomain]
    [FiniteDimensional 𝔽 CoDomain] where
  keySet : Type uKey
  [instKey : Fintype keySet]
  setup : Nat → PMF keySet
  evalF : keySet → Domain →  CoDomain
  Linearity : ∀ k : keySet, ∀ s : 𝔽, ∀ x : Domain, ∀ y : Domain,
  evalF k (s • x + y) = s • (evalF k x) + evalF k y
end LinearFunctionFamily

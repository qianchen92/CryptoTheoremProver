import Mathlib.Probability.ProbabilityMassFunction.Basic
import Mathlib.Probability.Distributions.Uniform
import Mathlib.Probability.ProbabilityMassFunction.Monad
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Crypto.SecModel.Adversary.Basic

namespace LinearFunctionFamily
open Crypto.SecModel
universe uDomain uCoDomain uKey uScalar

class FiniteLinearSpace (𝔽 : Type uScalar) [Field 𝔽] (V : Type _) extends
    AddCommGroup V, Module 𝔽 V, FiniteDimensional 𝔽 V, Fintype V

structure LFF
    (𝔽 : Type uScalar) [Field 𝔽] [Fintype 𝔽]
    (Domain : Type uDomain) [FiniteLinearSpace 𝔽 Domain] [Nonempty Domain]
    (CoDomain : Type uCoDomain) [FiniteLinearSpace 𝔽 CoDomain] [Nonempty CoDomain]
    (SecPar : Nat) where
  keySet : Type uKey
  [instKey : Fintype keySet]
  Setup : Nat → PMF keySet
  EvalF : keySet → Domain →  CoDomain
  Linearity : ∀ k : keySet, ∀ s : 𝔽, ∀ x : Domain, ∀ y : Domain,
  EvalF k (s • x + y) = s • (EvalF k x) + EvalF k y
  RealDist : PMF CoDomain := by
    exact (do
      let k ← Setup SecPar
      let x ← PMF.uniformOfFintype Domain
      pure (EvalF k x)
    )
  RandDist : PMF CoDomain := PMF.uniformOfFintype CoDomain
  KeyIndistinguishability : ∀ Adv : Adversary.PPTAdversary CoDomain (ULift Bool),
    (do
      let x ← RealDist
      Adv.run SecPar x
    ) ⟨true⟩
    =
    (do
      let x ← RandDist
      Adv.run SecPar x
    ) ⟨true⟩

end LinearFunctionFamily

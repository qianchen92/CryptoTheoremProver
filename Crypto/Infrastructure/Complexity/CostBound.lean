import Crypto.Infrastructure.Asymptotic.Bounds
import Crypto.Infrastructure.Computation.Cost.Measure
import Crypto.Infrastructure.Computation.Randomized

namespace Crypto.Infrastructure.Complexity

open Crypto.Infrastructure.Asymptotic
open Crypto.Infrastructure.Computation
open Crypto.Infrastructure.Computation.Cost

universe uCost uIn uOut uMapped

/--
An exact, input-dependent path-cost certificate for one randomized computation.

The certificate refers to the existing computation rather than storing another
copy of its execution semantics.
-/
structure ExactCostCertificate
    {M : CostModel.{uCost}}
    {Input : Crypto.SecPar → Type uIn}
    {Output : (sec : Crypto.SecPar) → Input sec → Type uOut}
    (run : RandomizedComputation M Input Output) where
  budget : (sec : Crypto.SecPar) → Input sec → M.Cost
  sound : ∀ sec input,
    RandCosted.CostBound (run sec input) (budget sec input)

namespace ExactCostCertificate

variable
    {M : CostModel.{uCost}}
    {Input : Crypto.SecPar → Type uIn}
    {Output : (sec : Crypto.SecPar) → Input sec → Type uOut}
    {run : RandomizedComputation M Input Output}

/-- The certified exact budget bounds each concrete execution path. -/
theorem cost_le_budget
    (certificate : ExactCostCertificate run)
    (sec : Crypto.SecPar) (input : Input sec)
    (result : Costed M (Output sec input))
    (hresult : result ∈ (run sec input).support) :
    M.instPartialOrder.le result.cost (certificate.budget sec input) :=
  certificate.sound sec input result hresult

/-- A zero-cost pure computation has the sequential identity as exact budget. -/
noncomputable def pure
    (M : CostModel.{uCost})
    {Input : Crypto.SecPar → Type uIn}
    {Output : (sec : Crypto.SecPar) → Input sec → Type uOut}
    (value : (sec : Crypto.SecPar) → (input : Input sec) → Output sec input) :
    ExactCostCertificate (RandomizedComputation.pure M value) where
  budget := fun _sec _input => M.instAddMonoid.zero
  sound := fun sec input => RandCosted.CostBound.pure (value sec input)

/-- Value-only dependent maps preserve an exact cost certificate. -/
noncomputable def map
    {Mapped : (sec : Crypto.SecPar) → Input sec → Type uMapped}
    (transform :
      (sec : Crypto.SecPar) → (input : Input sec) →
        Output sec input → Mapped sec input)
    (certificate : ExactCostCertificate run) :
    ExactCostCertificate (RandomizedComputation.map transform run) where
  budget := certificate.budget
  sound := fun sec input =>
    RandCosted.CostBound.map (certificate.sound sec input) (transform sec input)

end ExactCostCertificate

/--
An exact cost certificate together with one uniform natural-number runtime.

`NatMeasure` is used only at this boundary; the underlying computation keeps
its original exact costs.
-/
structure RuntimeCertificate
    {M : CostModel.{uCost}}
    (measure : NatMeasure M)
    {Input : Crypto.SecPar → Type uIn}
    {Output : (sec : Crypto.SecPar) → Input sec → Type uOut}
    (run : RandomizedComputation M Input Output)
    extends ExactCostCertificate run where
  runtime : Crypto.SecPar → Nat
  budget_le_runtime : ∀ sec input,
    measure (budget sec input) ≤ runtime sec

namespace RuntimeCertificate

variable
    {M : CostModel.{uCost}} {measure : NatMeasure M}
    {Input : Crypto.SecPar → Type uIn}
    {Output : (sec : Crypto.SecPar) → Input sec → Type uOut}
    {run : RandomizedComputation M Input Output}

/-- Every concrete exact path maps below the declared runtime. -/
theorem measuredCost_le_runtime
    (certificate : RuntimeCertificate measure run)
    (sec : Crypto.SecPar) (input : Input sec)
    (result : Costed M (Output sec input))
    (hresult : result ∈ (run sec input).support) :
    measure result.cost ≤ certificate.runtime sec :=
  le_trans
    (measure.monotone_toNat
      (certificate.cost_le_budget sec input result hresult))
    (certificate.budget_le_runtime sec input)

/-- A pure computation has zero exact budget and zero measured runtime. -/
noncomputable def pure
    (M : CostModel.{uCost}) (measure : NatMeasure M)
    {Input : Crypto.SecPar → Type uIn}
    {Output : (sec : Crypto.SecPar) → Input sec → Type uOut}
    (value : (sec : Crypto.SecPar) → (input : Input sec) → Output sec input) :
    RuntimeCertificate measure (RandomizedComputation.pure M value) where
  toExactCostCertificate := ExactCostCertificate.pure M value
  runtime := fun _sec => 0
  budget_le_runtime := by
    intro sec input
    simp [ExactCostCertificate.pure]

/-- Value-only dependent maps preserve exact and measured runtime certificates. -/
noncomputable def map
    {Mapped : (sec : Crypto.SecPar) → Input sec → Type uMapped}
    (transform :
      (sec : Crypto.SecPar) → (input : Input sec) →
        Output sec input → Mapped sec input)
    (certificate : RuntimeCertificate measure run) :
    RuntimeCertificate measure (RandomizedComputation.map transform run) where
  toExactCostCertificate :=
    certificate.toExactCostCertificate.map transform
  runtime := certificate.runtime
  budget_le_runtime := certificate.budget_le_runtime

end RuntimeCertificate

/-- A runtime certificate whose natural-number runtime is polynomially bounded. -/
structure PolyRuntimeCertificate
    {M : CostModel.{uCost}}
    (measure : NatMeasure M)
    {Input : Crypto.SecPar → Type uIn}
    {Output : (sec : Crypto.SecPar) → Input sec → Type uOut}
    (run : RandomizedComputation M Input Output)
    extends RuntimeCertificate measure run where
  runtime_isPoly : IsPolyBounded runtime

namespace PolyRuntimeCertificate

variable
    {M : CostModel.{uCost}} {measure : NatMeasure M}
    {Input : Crypto.SecPar → Type uIn}
    {Output : (sec : Crypto.SecPar) → Input sec → Type uOut}
    {run : RandomizedComputation M Input Output}

/-- A pure computation has polynomial zero runtime. -/
noncomputable def pure
    (M : CostModel.{uCost}) (measure : NatMeasure M)
    {Input : Crypto.SecPar → Type uIn}
    {Output : (sec : Crypto.SecPar) → Input sec → Type uOut}
    (value : (sec : Crypto.SecPar) → (input : Input sec) → Output sec input) :
    PolyRuntimeCertificate measure (RandomizedComputation.pure M value) where
  toRuntimeCertificate := RuntimeCertificate.pure M measure value
  runtime_isPoly := IsPolyBounded.zero

/-- Value-only dependent maps preserve polynomial runtime certificates. -/
noncomputable def map
    {Mapped : (sec : Crypto.SecPar) → Input sec → Type uMapped}
    (transform :
      (sec : Crypto.SecPar) → (input : Input sec) →
        Output sec input → Mapped sec input)
    (certificate : PolyRuntimeCertificate measure run) :
    PolyRuntimeCertificate measure (RandomizedComputation.map transform run) where
  toRuntimeCertificate :=
    certificate.toRuntimeCertificate.map transform
  runtime_isPoly := certificate.runtime_isPoly

end PolyRuntimeCertificate

end Crypto.Infrastructure.Complexity

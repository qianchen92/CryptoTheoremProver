import Crypto.Infrastructure.Computation.Algebra.Costed
import Crypto.Infrastructure.Computation.Cost.Distribution
import Crypto.Infrastructure.Computation.Distribution
import Mathlib.Algebra.Group.Defs

namespace Crypto.Infrastructure.Computation.Algebra

open Crypto.Infrastructure.Computation.Cost

universe uScalar uCarrier uSample uValue

/--
An explicit implementation of multiplication whose result carries its local
cost.

The specification connects the implementation result to the mathematical
multiplication.  Runtime bounds remain separate so that the same
implementation can support several analyses.
-/
structure MultiplicativeBackend
    (Value : Type uValue) [Mul Value] where
  mul : Value → Value → Costed Value
  mul_spec : ∀ left right, (mul left right).val = left * right

namespace MultiplicativeBackend

variable {Value : Type uValue} [Mul Value]

/-- Derive a multiplicative backend from the selected multiplication cost model. -/
def ofCostModel [MulCost Value] : MultiplicativeBackend Value where
  mul := Costed.mul
  mul_spec := by
    intros
    rfl

/-- Build multiplication directly from a cost assigned to each pair of operands. -/
def ofCostFunction
    (mulCost : Value → Value → Cost) : MultiplicativeBackend Value where
  mul := fun left right => ⟨left * right, mulCost left right⟩
  mul_spec := by
    intros
    rfl

/-- Build ordinary multiplication with the same local cost on every call. -/
def ofConstantCost (mulCost : Cost) : MultiplicativeBackend Value :=
  ofCostFunction fun _left _right => mulCost

@[simp] theorem mul_val
    (backend : MultiplicativeBackend Value) (left right : Value) :
    (backend.mul left right).val = left * right :=
  backend.mul_spec left right

end MultiplicativeBackend

/-- A uniform local-cost bound for a multiplicative backend. -/
structure MultiplicativeCostBounds
    {Value : Type uValue} [Mul Value]
    (backend : MultiplicativeBackend Value) where
  mulBudget : Cost
  mulCost_le : ∀ left right, (backend.mul left right).cost ≤ mulBudget

namespace MultiplicativeCostBounds

variable {Value : Type uValue} [Mul Value]

/-- Exact uniform bound for a multiplicative backend built with one constant cost. -/
def ofConstantCost (mulCost : Cost) :
    MultiplicativeCostBounds
      (MultiplicativeBackend.ofConstantCost (Value := Value) mulCost) where
  mulBudget := mulCost
  mulCost_le := by
    intros
    rfl

end MultiplicativeCostBounds

/--
An explicit implementation of the additive operations used by a computation.

Each operation returns its mathematical value together with its local cost.
The specification fields connect the returned value to the corresponding
mathematical operation.  Local costs do not include the cost of producing the
operands.
-/
structure AdditiveBackend
    (Scalar : Type uScalar) (Carrier : Type uCarrier)
    [AddGroup Carrier] [SMul Scalar Carrier] where
  add : Carrier → Carrier → Costed Carrier
  add_spec : ∀ left right, (add left right).val = left + right
  neg : Carrier → Costed Carrier
  neg_spec : ∀ value, (neg value).val = -value
  sub : Carrier → Carrier → Costed Carrier
  sub_spec : ∀ left right, (sub left right).val = left - right
  smul : Scalar → Carrier → Costed Carrier
  smul_spec : ∀ scalar value, (smul scalar value).val = scalar • value

namespace AdditiveBackend

variable
    {Scalar : Type uScalar} {Carrier : Type uCarrier}
    [AddGroup Carrier] [SMul Scalar Carrier]

/--
Use the ordinary algebraic operations together with the existing companion
cost typeclasses as an explicit backend.
-/
def ofCostModel
    [AddCost Carrier] [NegCost Carrier] [SubCost Carrier]
    [SMulCost Scalar Carrier] :
    AdditiveBackend Scalar Carrier where
  add := Costed.add
  add_spec := by
    intros
    rfl
  neg := Costed.neg
  neg_spec := by
    intro
    rfl
  sub := Costed.sub
  sub_spec := by
    intros
    rfl
  smul := Costed.smul
  smul_spec := by
    intros
    rfl

/--
Build the ordinary additive operations from explicit operand-dependent cost
functions.
-/
def ofCostFunctions
    (addCost : Carrier → Carrier → Cost)
    (negCost : Carrier → Cost)
    (subCost : Carrier → Carrier → Cost)
    (smulCost : Scalar → Carrier → Cost) :
    AdditiveBackend Scalar Carrier where
  add := fun left right => ⟨left + right, addCost left right⟩
  add_spec := by
    intros
    rfl
  neg := fun value => ⟨-value, negCost value⟩
  neg_spec := by
    intro
    rfl
  sub := fun left right => ⟨left - right, subCost left right⟩
  sub_spec := by
    intros
    rfl
  smul := fun scalar value => ⟨scalar • value, smulCost scalar value⟩
  smul_spec := by
    intros
    rfl

/--
Build the ordinary additive operations with one fixed local cost for each
operation kind.
-/
def ofConstantCosts
    (addCost negCost subCost smulCost : Cost) :
    AdditiveBackend Scalar Carrier :=
  ofCostFunctions
    (fun _left _right => addCost)
    (fun _value => negCost)
    (fun _left _right => subCost)
    (fun _scalar _value => smulCost)

/-- A backend addition has the mathematical value of addition. -/
@[simp] theorem add_val
    (backend : AdditiveBackend Scalar Carrier) (left right : Carrier) :
    (backend.add left right).val = left + right :=
  backend.add_spec left right

/-- A backend negation has the mathematical value of negation. -/
@[simp] theorem neg_val
    (backend : AdditiveBackend Scalar Carrier) (value : Carrier) :
    (backend.neg value).val = -value :=
  backend.neg_spec value

/-- A backend subtraction has the mathematical value of subtraction. -/
@[simp] theorem sub_val
    (backend : AdditiveBackend Scalar Carrier) (left right : Carrier) :
    (backend.sub left right).val = left - right :=
  backend.sub_spec left right

/-- A backend scalar multiplication has its mathematical value. -/
@[simp] theorem smul_val
    (backend : AdditiveBackend Scalar Carrier) (scalar : Scalar) (value : Carrier) :
    (backend.smul scalar value).val = scalar • value :=
  backend.smul_spec scalar value

end AdditiveBackend

/--
Uniform local-cost bounds for an additive backend.

This record is deliberately separate from `AdditiveBackend`: the backend fixes
the exact local costs, while a caller may prove several useful upper bounds for
different analyses.
-/
structure AdditiveCostBounds
    {Scalar : Type uScalar} {Carrier : Type uCarrier}
    [AddGroup Carrier] [SMul Scalar Carrier]
    (backend : AdditiveBackend Scalar Carrier) where
  addBudget : Cost
  addCost_le : ∀ left right, (backend.add left right).cost ≤ addBudget
  negBudget : Cost
  negCost_le : ∀ value, (backend.neg value).cost ≤ negBudget
  subBudget : Cost
  subCost_le : ∀ left right, (backend.sub left right).cost ≤ subBudget
  smulBudget : Cost
  smulCost_le : ∀ scalar value, (backend.smul scalar value).cost ≤ smulBudget

namespace AdditiveCostBounds

variable
    {Scalar : Type uScalar} {Carrier : Type uCarrier}
    [AddGroup Carrier] [SMul Scalar Carrier]

/-- Exact uniform bounds for an additive backend built from fixed operation costs. -/
def ofConstantCosts
    (addCost negCost subCost smulCost : Cost) :
    AdditiveCostBounds
      (AdditiveBackend.ofConstantCosts
        (Scalar := Scalar) (Carrier := Carrier)
        addCost negCost subCost smulCost) where
  addBudget := addCost
  addCost_le := by
    intros
    rfl
  negBudget := negCost
  negCost_le := by
    intro
    rfl
  subBudget := subCost
  subCost_le := by
    intros
    rfl
  smulBudget := smulCost
  smulCost_le := by
    intros
    rfl

end AdditiveCostBounds

/--
An exact costed sampler from a finite nonempty type.

This record contains only the executable joint value/cost distribution.
Uniformity and resource bounds are independent certificates below, so neither
mathematical semantics nor a chosen upper bound is stored twice in the exact
handler.
-/
structure UniformSampler
    (Sample : Type uSample) [Fintype Sample] [Nonempty Sample] where
  sample : RandCosted Sample

namespace UniformSampler

variable {Sample : Type uSample} [Fintype Sample] [Nonempty Sample]

/-- Build the canonical uniform sampler from an explicit local cost function. -/
noncomputable def ofCost
    (sampleCost : Sample → Cost) :
    UniformSampler Sample where
  sample :=
    RandCosted.sampleWithCost
      (Crypto.Infrastructure.Computation.Distribution.uniformPMF Sample)
      sampleCost

/-- Build the canonical uniform sampler with the same local cost for every outcome. -/
noncomputable def ofConstantCost (sampleCost : Cost) :
    UniformSampler Sample :=
  ofCost fun _value => sampleCost

end UniformSampler

/--
The cost-erased uniformity law for one exact sampler.

This layer is intentionally separate from `UniformSampler`: exact execution,
distributional specification, and asymptotic/resource certificates can evolve
independently.
-/
structure UniformSamplerLaws
    {Sample : Type uSample} [Fintype Sample] [Nonempty Sample]
    (sampler : UniformSampler Sample) where
  sample_spec :
    RandCosted.valueDist sampler.sample =
      Crypto.Infrastructure.Computation.Distribution.uniformPMF Sample

namespace UniformSamplerLaws

variable {Sample : Type uSample} [Fintype Sample] [Nonempty Sample]

/-- Erasing path costs from a certified sampler gives the uniform distribution. -/
@[simp] theorem valueDist_sample
    {sampler : UniformSampler Sample} (laws : UniformSamplerLaws sampler) :
    RandCosted.valueDist sampler.sample =
      Crypto.Infrastructure.Computation.Distribution.uniformPMF Sample :=
  laws.sample_spec

/-- Uniformity law for the canonical sampler with an explicit cost function. -/
noncomputable def ofCost (sampleCost : Sample → Cost) :
    UniformSamplerLaws (UniformSampler.ofCost sampleCost) where
  sample_spec := RandCosted.valueDist_sampleWithCost _ _

/-- Uniformity law for the canonical constant-cost sampler. -/
noncomputable def ofConstantCost (sampleCost : Cost) :
    UniformSamplerLaws
      (UniformSampler.ofConstantCost (Sample := Sample) sampleCost) :=
  ofCost (Sample := Sample) (fun _value => sampleCost)

end UniformSamplerLaws

/--
A uniform path-cost bound for one exact uniform sampler.

This certificate is separate from `UniformSampler`: exact randomized semantics
therefore do not depend on a chosen static budget, and several analyses may
attach different sound bounds to the same sampler.
-/
structure UniformSamplerBounds
    {Sample : Type uSample} [Fintype Sample] [Nonempty Sample]
    (sampler : UniformSampler Sample) where
  sampleBudget : Cost
  cost_le :
    ∀ result, result ∈ sampler.sample.support → result.cost ≤ sampleBudget

namespace UniformSamplerBounds

variable {Sample : Type uSample} [Fintype Sample] [Nonempty Sample]

/--
The direct bound for a canonical sampler built from an operand-dependent cost
function.
-/
noncomputable def ofCost
    (sampleCost : Sample → Cost)
    (sampleBudget : Cost)
    (sampleCost_le : ∀ value, sampleCost value ≤ sampleBudget) :
    UniformSamplerBounds (UniformSampler.ofCost sampleCost) where
  sampleBudget := sampleBudget
  cost_le := by
    intro result hresult
    simp only [UniformSampler.ofCost, RandCosted.sampleWithCost,
      RandCostedT.sampleWithCost] at hresult
    rw [PMF.mem_support_map_iff] at hresult
    rcases hresult with ⟨value, _hvalue, hresult⟩
    subst result
    exact sampleCost_le value

/-- Exact bound for a canonical sampler with one constant local cost. -/
noncomputable def ofConstantCost (sampleCost : Cost) :
    UniformSamplerBounds
      (UniformSampler.ofConstantCost (Sample := Sample) sampleCost) :=
  ofCost (Sample := Sample) (fun _value => sampleCost) sampleCost (by
    intro
    rfl)

end UniformSamplerBounds

end Crypto.Infrastructure.Computation.Algebra

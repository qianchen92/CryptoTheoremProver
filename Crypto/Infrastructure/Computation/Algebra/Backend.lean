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
A costed implementation of uniform sampling from a finite nonempty type.

The sampler itself is a `RandCosted` computation, so its cost is part of each
execution path.  In particular, distinct internal paths may return the same
value with different costs.  `sampleBudget` is the uniform path bound used by
compositional static budgets.
-/
structure UniformSampler
    (Sample : Type uSample) [Fintype Sample] [Nonempty Sample] where
  sample : RandCosted Sample
  sample_spec :
    RandCosted.valueDist sample =
      Crypto.Infrastructure.Computation.Distribution.uniformPMF Sample
  sampleBudget : Cost
  cost_le :
    ∀ result, result ∈ sample.support → result.cost ≤ sampleBudget

namespace UniformSampler

variable {Sample : Type uSample} [Fintype Sample] [Nonempty Sample]

/-- Erasing path costs from a sampler gives the uniform distribution. -/
@[simp] theorem valueDist_sample (sampler : UniformSampler Sample) :
    RandCosted.valueDist sampler.sample =
      Crypto.Infrastructure.Computation.Distribution.uniformPMF Sample :=
  sampler.sample_spec

/-- Build the canonical uniform sampler from an explicit local cost function and bound. -/
noncomputable def ofCost
    (sampleCost : Sample → Cost)
    (sampleBudget : Cost)
    (sampleCost_le : ∀ value, sampleCost value ≤ sampleBudget) :
    UniformSampler Sample where
  sample :=
    RandCosted.sampleWithCost
      (Crypto.Infrastructure.Computation.Distribution.uniformPMF Sample)
      sampleCost
  sample_spec := RandCosted.valueDist_sampleWithCost _ _
  sampleBudget := sampleBudget
  cost_le := by
    intro result hresult
    simp only [RandCosted.sampleWithCost] at hresult
    rw [PMF.mem_support_map_iff] at hresult
    rcases hresult with ⟨value, _hvalue, hresult⟩
    subst result
    exact sampleCost_le value

/-- Build the canonical uniform sampler with the same local cost for every outcome. -/
noncomputable def ofConstantCost (sampleCost : Cost) :
    UniformSampler Sample :=
  ofCost (fun _value => sampleCost) sampleCost (by
    intro
    rfl)

end UniformSampler

end Crypto.Infrastructure.Computation.Algebra

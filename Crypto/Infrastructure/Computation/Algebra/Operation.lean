import Crypto.Infrastructure.Computation.Algebra.Signature
import Crypto.Infrastructure.Computation.Algebra.Handler
import Crypto.Infrastructure.Computation.Algebra.Laws
import Crypto.Infrastructure.Computation.Algebra.Bounds

namespace Crypto.Infrastructure.Computation.Algebra

open Crypto.Infrastructure.Computation.Cost

universe uCost uScalar uCarrier uSample uValue

/-- A typed primitive addition call. -/
inductive AddOperation (Carrier : Type uCarrier) :
    Type uCarrier → Type (uCarrier + 1) where
  | add (left right : Carrier) : AddOperation Carrier Carrier

namespace AddOperation

/-- The single-operation signature for addition. -/
def signature (Carrier : Type uCarrier) :
    Signature.{uCarrier, uCarrier + 1} where
  Op := AddOperation Carrier

variable (M : CostModel.{uCost}) {Carrier : Type uCarrier} [Add Carrier]

/-- Interpret mathematical addition with an exact cost in an arbitrary model. -/
noncomputable def algebra
    (addCost : Carrier → Carrier → M.Cost) :
    CostedAlgebra M (signature Carrier) where
  exec operation :=
    match operation with
    | .add left right =>
        RandCosted.liftCosted
          (⟨left + right, addCost left right⟩ : Costed M Carrier)

/-- The cost-erased addition handler agrees with mathematical addition. -/
noncomputable def laws
    (addCost : Carrier → Carrier → M.Cost) :
    AlgebraLaws (algebra M addCost) where
  semantics operation :=
    match operation with
    | .add left right => PMF.pure (left + right)
  exec_spec operation := by
    cases operation with
    | add left right => simp [algebra]

/-- An independently chosen bound for the exact addition handler. -/
noncomputable def bounds
    (addCost addBudget : Carrier → Carrier → M.Cost)
    (addCost_le : ∀ left right,
      M.instPartialOrder.le
        (addCost left right) (addBudget left right)) :
    OperationBounds (algebra M addCost) where
  budget operation :=
    match operation with
    | .add left right => addBudget left right
  cost_le operation result hresult := by
    cases operation with
    | add left right =>
        simp only [algebra, RandCosted.liftCosted] at hresult
        rw [PMF.mem_support_pure_iff] at hresult
        subst result
        exact addCost_le left right

end AddOperation

/-- A typed primitive negation call. -/
inductive NegOperation (Carrier : Type uCarrier) :
    Type uCarrier → Type (uCarrier + 1) where
  | neg (value : Carrier) : NegOperation Carrier Carrier

namespace NegOperation

/-- The single-operation signature for negation. -/
def signature (Carrier : Type uCarrier) :
    Signature.{uCarrier, uCarrier + 1} where
  Op := NegOperation Carrier

variable (M : CostModel.{uCost}) {Carrier : Type uCarrier} [Neg Carrier]

/-- Interpret mathematical negation with an exact cost in an arbitrary model. -/
noncomputable def algebra
    (negCost : Carrier → M.Cost) :
    CostedAlgebra M (signature Carrier) where
  exec operation :=
    match operation with
    | .neg value =>
        RandCosted.liftCosted
          (⟨-value, negCost value⟩ : Costed M Carrier)

/-- The cost-erased negation handler agrees with mathematical negation. -/
noncomputable def laws
    (negCost : Carrier → M.Cost) :
    AlgebraLaws (algebra M negCost) where
  semantics operation :=
    match operation with
    | .neg value => PMF.pure (-value)
  exec_spec operation := by
    cases operation with
    | neg value => simp [algebra]

/-- An independently chosen bound for the exact negation handler. -/
noncomputable def bounds
    (negCost negBudget : Carrier → M.Cost)
    (negCost_le : ∀ value,
      M.instPartialOrder.le (negCost value) (negBudget value)) :
    OperationBounds (algebra M negCost) where
  budget operation :=
    match operation with
    | .neg value => negBudget value
  cost_le operation result hresult := by
    cases operation with
    | neg value =>
        simp only [algebra, RandCosted.liftCosted] at hresult
        rw [PMF.mem_support_pure_iff] at hresult
        subst result
        exact negCost_le value

end NegOperation

/-- A typed primitive subtraction call. -/
inductive SubOperation (Carrier : Type uCarrier) :
    Type uCarrier → Type (uCarrier + 1) where
  | sub (left right : Carrier) : SubOperation Carrier Carrier

namespace SubOperation

/-- The single-operation signature for subtraction. -/
def signature (Carrier : Type uCarrier) :
    Signature.{uCarrier, uCarrier + 1} where
  Op := SubOperation Carrier

variable (M : CostModel.{uCost}) {Carrier : Type uCarrier} [Sub Carrier]

/-- Interpret mathematical subtraction with an exact cost in an arbitrary model. -/
noncomputable def algebra
    (subCost : Carrier → Carrier → M.Cost) :
    CostedAlgebra M (signature Carrier) where
  exec operation :=
    match operation with
    | .sub left right =>
        RandCosted.liftCosted
          (⟨left - right, subCost left right⟩ : Costed M Carrier)

/-- The cost-erased subtraction handler agrees with mathematical subtraction. -/
noncomputable def laws
    (subCost : Carrier → Carrier → M.Cost) :
    AlgebraLaws (algebra M subCost) where
  semantics operation :=
    match operation with
    | .sub left right => PMF.pure (left - right)
  exec_spec operation := by
    cases operation with
    | sub left right => simp [algebra]

/-- An independently chosen bound for the exact subtraction handler. -/
noncomputable def bounds
    (subCost subBudget : Carrier → Carrier → M.Cost)
    (subCost_le : ∀ left right,
      M.instPartialOrder.le
        (subCost left right) (subBudget left right)) :
    OperationBounds (algebra M subCost) where
  budget operation :=
    match operation with
    | .sub left right => subBudget left right
  cost_le operation result hresult := by
    cases operation with
    | sub left right =>
        simp only [algebra, RandCosted.liftCosted] at hresult
        rw [PMF.mem_support_pure_iff] at hresult
        subst result
        exact subCost_le left right

end SubOperation

/-- A typed primitive scalar-multiplication call. -/
inductive SMulOperation
    (Scalar : Type uScalar) (Carrier : Type uCarrier) :
    Type uCarrier → Type (max uScalar (uCarrier + 1)) where
  | smul (scalar : Scalar) (value : Carrier) :
      SMulOperation Scalar Carrier Carrier

namespace SMulOperation

/-- The single-operation signature for scalar multiplication. -/
def signature (Scalar : Type uScalar) (Carrier : Type uCarrier) :
    Signature.{uCarrier, max uScalar (uCarrier + 1)} where
  Op := SMulOperation Scalar Carrier

variable
    (M : CostModel.{uCost})
    {Scalar : Type uScalar} {Carrier : Type uCarrier}
    [SMul Scalar Carrier]

/-- Interpret scalar multiplication with an exact cost in an arbitrary model. -/
noncomputable def algebra
    (smulCost : Scalar → Carrier → M.Cost) :
    CostedAlgebra M (signature Scalar Carrier) where
  exec operation :=
    match operation with
    | .smul scalar value =>
        RandCosted.liftCosted
          (⟨scalar • value, smulCost scalar value⟩ : Costed M Carrier)

/-- The cost-erased handler agrees with mathematical scalar multiplication. -/
noncomputable def laws
    (smulCost : Scalar → Carrier → M.Cost) :
    AlgebraLaws (algebra M smulCost) where
  semantics operation :=
    match operation with
    | .smul scalar value => PMF.pure (scalar • value)
  exec_spec operation := by
    cases operation with
    | smul scalar value => simp [algebra]

/-- An independently chosen bound for the exact scalar-multiplication handler. -/
noncomputable def bounds
    (smulCost smulBudget : Scalar → Carrier → M.Cost)
    (smulCost_le : ∀ scalar value,
      M.instPartialOrder.le
        (smulCost scalar value) (smulBudget scalar value)) :
    OperationBounds (algebra M smulCost) where
  budget operation :=
    match operation with
    | .smul scalar value => smulBudget scalar value
  cost_le operation result hresult := by
    cases operation with
    | smul scalar value =>
        simp only [algebra, RandCosted.liftCosted] at hresult
        rw [PMF.mem_support_pure_iff] at hresult
        subst result
        exact smulCost_le scalar value

end SMulOperation

/-- A typed primitive multiplication call. -/
inductive MulOperation (Value : Type uValue) :
    Type uValue → Type (uValue + 1) where
  | mul (left right : Value) : MulOperation Value Value

namespace MulOperation

/-- The single-operation signature for multiplication. -/
def signature (Value : Type uValue) :
    Signature.{uValue, uValue + 1} where
  Op := MulOperation Value

variable (M : CostModel.{uCost}) {Value : Type uValue} [Mul Value]

/-- Interpret mathematical multiplication with an exact cost in an arbitrary model. -/
noncomputable def algebra
    (mulCost : Value → Value → M.Cost) :
    CostedAlgebra M (signature Value) where
  exec operation :=
    match operation with
    | .mul left right =>
        RandCosted.liftCosted
          (⟨left * right, mulCost left right⟩ : Costed M Value)

/-- The cost-erased multiplication handler agrees with mathematical multiplication. -/
noncomputable def laws
    (mulCost : Value → Value → M.Cost) :
    AlgebraLaws (algebra M mulCost) where
  semantics operation :=
    match operation with
    | .mul left right => PMF.pure (left * right)
  exec_spec operation := by
    cases operation with
    | mul left right => simp [algebra]

/-- An independently chosen bound for the exact multiplication handler. -/
noncomputable def bounds
    (mulCost mulBudget : Value → Value → M.Cost)
    (mulCost_le : ∀ left right,
      M.instPartialOrder.le
        (mulCost left right) (mulBudget left right)) :
    OperationBounds (algebra M mulCost) where
  budget operation :=
    match operation with
    | .mul left right => mulBudget left right
  cost_le operation result hresult := by
    cases operation with
    | mul left right =>
        simp only [algebra, RandCosted.liftCosted] at hresult
        rw [PMF.mem_support_pure_iff] at hresult
        subst result
        exact mulCost_le left right

end MulOperation

/-- A typed primitive call to one exact sampler. -/
inductive SampleOperation (Sample : Type uSample) :
    Type uSample → Type (uSample + 1) where
  | sample : SampleOperation Sample Sample

namespace SampleOperation

/-- The single-operation signature for sampling. -/
def signature (Sample : Type uSample) :
    Signature.{uSample, uSample + 1} where
  Op := SampleOperation Sample

variable (M : CostModel.{uCost}) {Sample : Type uSample}

/-- Interpret sampling through an arbitrary exact joint value/cost distribution. -/
noncomputable def algebra
    (sample : RandCosted M Sample) :
    CostedAlgebra M (signature Sample) where
  exec operation :=
    match operation with
    | .sample => sample

/-- A cost-erased mathematical specification for one exact sampler. -/
noncomputable def laws
    (sample : RandCosted M Sample)
    (semantics : PMF Sample)
    (sample_spec : RandCosted.valueDist sample = semantics) :
    AlgebraLaws (algebra M sample) where
  semantics operation :=
    match operation with
    | .sample => semantics
  exec_spec operation := by
    cases operation
    exact sample_spec

/-- An independently chosen path-cost bound for one exact sampler. -/
noncomputable def bounds
    (sample : RandCosted M Sample)
    (sampleBudget : M.Cost)
    (cost_le : ∀ result, result ∈ sample.support →
      M.instPartialOrder.le result.cost sampleBudget) :
    OperationBounds (algebra M sample) where
  budget _operation := sampleBudget
  cost_le operation result hresult := by
    cases operation
    exact cost_le result hresult

end SampleOperation

end Crypto.Infrastructure.Computation.Algebra

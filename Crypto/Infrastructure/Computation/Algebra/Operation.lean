import Crypto.Infrastructure.Computation.Algebra.Backend
import Crypto.Infrastructure.Computation.Algebra.Signature

namespace Crypto.Infrastructure.Computation.Algebra

open Crypto.Infrastructure.Computation.Cost

universe uScalar uCarrier uSample uValue

/-- A typed primitive addition call. -/
inductive AddOperation (Carrier : Type uCarrier) :
    Type uCarrier → Type (uCarrier + 1) where
  | add (left right : Carrier) : AddOperation Carrier Carrier

namespace AddOperation

/-- The single-operation signature for addition. -/
def signature (Carrier : Type uCarrier) :
    Signature.{uCarrier, uCarrier + 1} where
  Op := AddOperation Carrier

/-- Interpret addition exactly through an existing natural-cost backend. -/
noncomputable def algebra
    {Scalar : Type uScalar} {Carrier : Type uCarrier}
    [AddGroup Carrier] [SMul Scalar Carrier]
    (backend : AdditiveBackend Scalar Carrier) :
    CostedAlgebra natCostModel (signature Carrier) where
  exec operation :=
    match operation with
    | .add left right => RandCosted.liftCosted (backend.add left right)

/-- The cost-erased addition handler agrees with mathematical addition. -/
noncomputable def laws
    {Scalar : Type uScalar} {Carrier : Type uCarrier}
    [AddGroup Carrier] [SMul Scalar Carrier]
    (backend : AdditiveBackend Scalar Carrier) :
    AlgebraLaws (algebra backend) where
  semantics operation :=
    match operation with
    | .add left right => PMF.pure (left + right)
  exec_spec operation := by
    cases operation with
    | add left right => simp [algebra]

/-- An independently chosen bound for the exact addition handler. -/
def bounds
    {Scalar : Type uScalar} {Carrier : Type uCarrier}
    [AddGroup Carrier] [SMul Scalar Carrier]
    {backend : AdditiveBackend Scalar Carrier}
    (backendBounds : AdditiveCostBounds backend) :
    OperationBounds (algebra backend) where
  budget operation :=
    match operation with
    | .add _ _ => backendBounds.addBudget
  cost_le operation result hresult := by
    cases operation with
    | add left right =>
        simp only [algebra] at hresult
        rw [PMF.mem_support_pure_iff] at hresult
        subst result
        exact backendBounds.addCost_le left right

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

/-- Interpret negation exactly through an existing natural-cost backend. -/
noncomputable def algebra
    {Scalar : Type uScalar} {Carrier : Type uCarrier}
    [AddGroup Carrier] [SMul Scalar Carrier]
    (backend : AdditiveBackend Scalar Carrier) :
    CostedAlgebra natCostModel (signature Carrier) where
  exec operation :=
    match operation with
    | .neg value => RandCosted.liftCosted (backend.neg value)

/-- The cost-erased negation handler agrees with mathematical negation. -/
noncomputable def laws
    {Scalar : Type uScalar} {Carrier : Type uCarrier}
    [AddGroup Carrier] [SMul Scalar Carrier]
    (backend : AdditiveBackend Scalar Carrier) :
    AlgebraLaws (algebra backend) where
  semantics operation :=
    match operation with
    | .neg value => PMF.pure (-value)
  exec_spec operation := by
    cases operation with
    | neg value => simp [algebra]

/-- An independently chosen bound for the exact negation handler. -/
def bounds
    {Scalar : Type uScalar} {Carrier : Type uCarrier}
    [AddGroup Carrier] [SMul Scalar Carrier]
    {backend : AdditiveBackend Scalar Carrier}
    (backendBounds : AdditiveCostBounds backend) :
    OperationBounds (algebra backend) where
  budget operation :=
    match operation with
    | .neg _ => backendBounds.negBudget
  cost_le operation result hresult := by
    cases operation with
    | neg value =>
        simp only [algebra] at hresult
        rw [PMF.mem_support_pure_iff] at hresult
        subst result
        exact backendBounds.negCost_le value

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

/-- Interpret subtraction exactly through an existing natural-cost backend. -/
noncomputable def algebra
    {Scalar : Type uScalar} {Carrier : Type uCarrier}
    [AddGroup Carrier] [SMul Scalar Carrier]
    (backend : AdditiveBackend Scalar Carrier) :
    CostedAlgebra natCostModel (signature Carrier) where
  exec operation :=
    match operation with
    | .sub left right => RandCosted.liftCosted (backend.sub left right)

/-- The cost-erased subtraction handler agrees with mathematical subtraction. -/
noncomputable def laws
    {Scalar : Type uScalar} {Carrier : Type uCarrier}
    [AddGroup Carrier] [SMul Scalar Carrier]
    (backend : AdditiveBackend Scalar Carrier) :
    AlgebraLaws (algebra backend) where
  semantics operation :=
    match operation with
    | .sub left right => PMF.pure (left - right)
  exec_spec operation := by
    cases operation with
    | sub left right => simp [algebra]

/-- An independently chosen bound for the exact subtraction handler. -/
def bounds
    {Scalar : Type uScalar} {Carrier : Type uCarrier}
    [AddGroup Carrier] [SMul Scalar Carrier]
    {backend : AdditiveBackend Scalar Carrier}
    (backendBounds : AdditiveCostBounds backend) :
    OperationBounds (algebra backend) where
  budget operation :=
    match operation with
    | .sub _ _ => backendBounds.subBudget
  cost_le operation result hresult := by
    cases operation with
    | sub left right =>
        simp only [algebra] at hresult
        rw [PMF.mem_support_pure_iff] at hresult
        subst result
        exact backendBounds.subCost_le left right

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

/-- Interpret scalar multiplication exactly through an existing natural-cost backend. -/
noncomputable def algebra
    {Scalar : Type uScalar} {Carrier : Type uCarrier}
    [AddGroup Carrier] [SMul Scalar Carrier]
    (backend : AdditiveBackend Scalar Carrier) :
    CostedAlgebra natCostModel (signature Scalar Carrier) where
  exec operation :=
    match operation with
    | .smul scalar value => RandCosted.liftCosted (backend.smul scalar value)

/-- The cost-erased handler agrees with mathematical scalar multiplication. -/
noncomputable def laws
    {Scalar : Type uScalar} {Carrier : Type uCarrier}
    [AddGroup Carrier] [SMul Scalar Carrier]
    (backend : AdditiveBackend Scalar Carrier) :
    AlgebraLaws (algebra backend) where
  semantics operation :=
    match operation with
    | .smul scalar value => PMF.pure (scalar • value)
  exec_spec operation := by
    cases operation with
    | smul scalar value => simp [algebra]

/-- An independently chosen bound for the exact scalar-multiplication handler. -/
def bounds
    {Scalar : Type uScalar} {Carrier : Type uCarrier}
    [AddGroup Carrier] [SMul Scalar Carrier]
    {backend : AdditiveBackend Scalar Carrier}
    (backendBounds : AdditiveCostBounds backend) :
    OperationBounds (algebra backend) where
  budget operation :=
    match operation with
    | .smul _ _ => backendBounds.smulBudget
  cost_le operation result hresult := by
    cases operation with
    | smul scalar value =>
        simp only [algebra] at hresult
        rw [PMF.mem_support_pure_iff] at hresult
        subst result
        exact backendBounds.smulCost_le scalar value

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

/-- Interpret multiplication exactly through an existing natural-cost backend. -/
noncomputable def algebra
    {Value : Type uValue} [Mul Value]
    (backend : MultiplicativeBackend Value) :
    CostedAlgebra natCostModel (signature Value) where
  exec operation :=
    match operation with
    | .mul left right => RandCosted.liftCosted (backend.mul left right)

/-- The cost-erased multiplication handler agrees with mathematical multiplication. -/
noncomputable def laws
    {Value : Type uValue} [Mul Value]
    (backend : MultiplicativeBackend Value) :
    AlgebraLaws (algebra backend) where
  semantics operation :=
    match operation with
    | .mul left right => PMF.pure (left * right)
  exec_spec operation := by
    cases operation with
    | mul left right => simp [algebra]

/-- An independently chosen bound for the exact multiplication handler. -/
def bounds
    {Value : Type uValue} [Mul Value]
    {backend : MultiplicativeBackend Value}
    (backendBounds : MultiplicativeCostBounds backend) :
    OperationBounds (algebra backend) where
  budget operation :=
    match operation with
    | .mul _ _ => backendBounds.mulBudget
  cost_le operation result hresult := by
    cases operation with
    | mul left right =>
        simp only [algebra] at hresult
        rw [PMF.mem_support_pure_iff] at hresult
        subst result
        exact backendBounds.mulCost_le left right

end MulOperation

/-- A typed primitive call to one exact finite sampler. -/
inductive SampleOperation (Sample : Type uSample) :
    Type uSample → Type (uSample + 1) where
  | sample : SampleOperation Sample Sample

namespace SampleOperation

/-- The single-operation signature for sampling. -/
def signature (Sample : Type uSample) :
    Signature.{uSample, uSample + 1} where
  Op := SampleOperation Sample

/-- Interpret sampling through the sampler's exact randomized computation. -/
noncomputable def algebra
    {Sample : Type uSample} [Fintype Sample] [Nonempty Sample]
    (sampler : UniformSampler Sample) :
    CostedAlgebra natCostModel (signature Sample) where
  exec operation :=
    match operation with
    | .sample => sampler.sample

/-- The cost-erased sampling handler is the uniform distribution. -/
noncomputable def laws
    {Sample : Type uSample} [Fintype Sample] [Nonempty Sample]
    (sampler : UniformSampler Sample)
    (samplerLaws : UniformSamplerLaws sampler) :
    AlgebraLaws (algebra sampler) where
  semantics operation :=
    match operation with
    | .sample =>
        Crypto.Infrastructure.Computation.Distribution.uniformPMF Sample
  exec_spec operation := by
    cases operation
    exact samplerLaws.sample_spec

/-- An independently chosen bound for the exact sampling handler. -/
noncomputable def bounds
    {Sample : Type uSample} [Fintype Sample] [Nonempty Sample]
    {sampler : UniformSampler Sample}
    (samplerBounds : UniformSamplerBounds sampler) :
    OperationBounds (algebra sampler) where
  budget _operation := samplerBounds.sampleBudget
  cost_le operation result hresult := by
    cases operation
    exact samplerBounds.cost_le result hresult

end SampleOperation

end Crypto.Infrastructure.Computation.Algebra

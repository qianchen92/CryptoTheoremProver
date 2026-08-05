import CryptoFirstOrder.Algebra
import Crypto.Infrastructure.Computation.Cost.PathBound
import Crypto.Infrastructure.Probability.Uniform

namespace CryptoFirstOrder

open Crypto.Infrastructure.Computation.Cost

universe uCost uBase uValue uOp uSourceOp

/-- A first-order primitive addition operation. -/
inductive AddOperation {Base : Type uBase} (carrier : Ty Base) :
    Ty Base → Ty Base → Type uBase where
  | add : AddOperation carrier (.prod carrier carrier) carrier

namespace AddOperation

def signature {Base : Type uBase} (carrier : Ty Base) : Signature Base where
  Op := AddOperation carrier

noncomputable def algebra
    (M : CostModel.{uCost})
    {Base : Type uBase} (interpret : Base → Type uValue)
    (carrier : Ty Base) [Add (Ty.denote interpret carrier)]
    (cost : M.Cost) :
    CostedAlgebra M interpret (signature carrier) where
  exec operation args :=
    match operation with
    | .add =>
        RandCosted.liftCosted
          (⟨args.1 + args.2, cost⟩ : Costed M (Ty.denote interpret carrier))

theorem costBound_exec
    (M : CostModel.{uCost})
    {Base : Type uBase} (interpret : Base → Type uValue)
    (carrier : Ty Base) [Add (Ty.denote interpret carrier)]
    (cost : M.Cost)
    {Args Result : Ty Base}
    (operation : (signature carrier).Op Args Result)
    (args : Ty.denote interpret Args) :
    RandCosted.CostBound
      ((algebra M interpret carrier cost).exec operation args) cost := by
  letI := M.instPartialOrder
  cases operation
  intro result hresult
  simp only [algebra, RandCosted.liftCosted] at hresult
  rw [PMF.mem_support_pure_iff] at hresult
  subst result
  exact le_refl cost

end AddOperation

/-- A first-order primitive negation operation. -/
inductive NegOperation {Base : Type uBase} (carrier : Ty Base) :
    Ty Base → Ty Base → Type uBase where
  | neg : NegOperation carrier carrier carrier

namespace NegOperation

def signature {Base : Type uBase} (carrier : Ty Base) : Signature Base where
  Op := NegOperation carrier

noncomputable def algebra
    (M : CostModel.{uCost})
    {Base : Type uBase} (interpret : Base → Type uValue)
    (carrier : Ty Base) [Neg (Ty.denote interpret carrier)]
    (cost : M.Cost) :
    CostedAlgebra M interpret (signature carrier) where
  exec operation args :=
    match operation with
    | .neg =>
        RandCosted.liftCosted
          (⟨-args, cost⟩ : Costed M (Ty.denote interpret carrier))

theorem costBound_exec
    (M : CostModel.{uCost})
    {Base : Type uBase} (interpret : Base → Type uValue)
    (carrier : Ty Base) [Neg (Ty.denote interpret carrier)]
    (cost : M.Cost)
    {Args Result : Ty Base}
    (operation : (signature carrier).Op Args Result)
    (args : Ty.denote interpret Args) :
    RandCosted.CostBound
      ((algebra M interpret carrier cost).exec operation args) cost := by
  letI := M.instPartialOrder
  cases operation
  intro result hresult
  simp only [algebra, RandCosted.liftCosted] at hresult
  rw [PMF.mem_support_pure_iff] at hresult
  subst result
  exact le_refl cost

end NegOperation

/-- A first-order primitive subtraction operation. -/
inductive SubOperation {Base : Type uBase} (carrier : Ty Base) :
    Ty Base → Ty Base → Type uBase where
  | sub : SubOperation carrier (.prod carrier carrier) carrier

namespace SubOperation

def signature {Base : Type uBase} (carrier : Ty Base) : Signature Base where
  Op := SubOperation carrier

noncomputable def algebra
    (M : CostModel.{uCost})
    {Base : Type uBase} (interpret : Base → Type uValue)
    (carrier : Ty Base) [Sub (Ty.denote interpret carrier)]
    (cost : M.Cost) :
    CostedAlgebra M interpret (signature carrier) where
  exec operation args :=
    match operation with
    | .sub =>
        RandCosted.liftCosted
          (⟨args.1 - args.2, cost⟩ : Costed M (Ty.denote interpret carrier))

theorem costBound_exec
    (M : CostModel.{uCost})
    {Base : Type uBase} (interpret : Base → Type uValue)
    (carrier : Ty Base) [Sub (Ty.denote interpret carrier)]
    (cost : M.Cost)
    {Args Result : Ty Base}
    (operation : (signature carrier).Op Args Result)
    (args : Ty.denote interpret Args) :
    RandCosted.CostBound
      ((algebra M interpret carrier cost).exec operation args) cost := by
  letI := M.instPartialOrder
  cases operation
  intro result hresult
  simp only [algebra, RandCosted.liftCosted] at hresult
  rw [PMF.mem_support_pure_iff] at hresult
  subst result
  exact le_refl cost

end SubOperation

/-- A first-order primitive scalar-multiplication operation. -/
inductive SMulOperation
    {Base : Type uBase} (scalar carrier : Ty Base) :
    Ty Base → Ty Base → Type uBase where
  | smul : SMulOperation scalar carrier (.prod scalar carrier) carrier

namespace SMulOperation

def signature
    {Base : Type uBase} (scalar carrier : Ty Base) : Signature Base where
  Op := SMulOperation scalar carrier

noncomputable def algebra
    (M : CostModel.{uCost})
    {Base : Type uBase} (interpret : Base → Type uValue)
    (scalar carrier : Ty Base)
    [SMul (Ty.denote interpret scalar) (Ty.denote interpret carrier)]
    (cost : M.Cost) :
    CostedAlgebra M interpret (signature scalar carrier) where
  exec operation args :=
    match operation with
    | .smul =>
        RandCosted.liftCosted
          (⟨args.1 • args.2, cost⟩ : Costed M (Ty.denote interpret carrier))

theorem costBound_exec
    (M : CostModel.{uCost})
    {Base : Type uBase} (interpret : Base → Type uValue)
    (scalar carrier : Ty Base)
    [SMul (Ty.denote interpret scalar) (Ty.denote interpret carrier)]
    (cost : M.Cost)
    {Args Result : Ty Base}
    (operation : (signature scalar carrier).Op Args Result)
    (args : Ty.denote interpret Args) :
    RandCosted.CostBound
      ((algebra M interpret scalar carrier cost).exec operation args) cost := by
  letI := M.instPartialOrder
  cases operation
  intro result hresult
  simp only [algebra, RandCosted.liftCosted] at hresult
  rw [PMF.mem_support_pure_iff] at hresult
  subst result
  exact le_refl cost

end SMulOperation

/-- A first-order primitive multiplication operation. -/
inductive MulOperation {Base : Type uBase} (value : Ty Base) :
    Ty Base → Ty Base → Type uBase where
  | mul : MulOperation value (.prod value value) value

namespace MulOperation

def signature {Base : Type uBase} (value : Ty Base) : Signature Base where
  Op := MulOperation value

noncomputable def algebra
    (M : CostModel.{uCost})
    {Base : Type uBase} (interpret : Base → Type uValue)
    (value : Ty Base) [Mul (Ty.denote interpret value)]
    (cost : M.Cost) :
    CostedAlgebra M interpret (signature value) where
  exec operation args :=
    match operation with
    | .mul =>
        RandCosted.liftCosted
          (⟨args.1 * args.2, cost⟩ : Costed M (Ty.denote interpret value))

theorem costBound_exec
    (M : CostModel.{uCost})
    {Base : Type uBase} (interpret : Base → Type uValue)
    (value : Ty Base) [Mul (Ty.denote interpret value)]
    (cost : M.Cost)
    {Args Result : Ty Base}
    (operation : (signature value).Op Args Result)
    (args : Ty.denote interpret Args) :
    RandCosted.CostBound
      ((algebra M interpret value cost).exec operation args) cost := by
  letI := M.instPartialOrder
  cases operation
  intro result hresult
  simp only [algebra, RandCosted.liftCosted] at hresult
  rw [PMF.mem_support_pure_iff] at hresult
  subst result
  exact le_refl cost

end MulOperation

/-- A first-order request to sample uniformly from one finite carrier. -/
inductive UniformSampleOperation {Base : Type uBase} (sample : Ty Base) :
    Ty Base → Ty Base → Type uBase where
  | sample : UniformSampleOperation sample .unit sample

namespace UniformSampleOperation

def signature {Base : Type uBase} (sample : Ty Base) : Signature Base where
  Op := UniformSampleOperation sample

/--
The built-in finite sampler. Every outcome has the same declared exact cost;
the value distribution is uniform over the interpreted finite carrier.
-/
noncomputable def algebra
    (M : CostModel.{uCost})
    {Base : Type uBase} (interpret : Base → Type uValue)
    (sample : Ty Base)
    [Fintype (Ty.denote interpret sample)]
    [Nonempty (Ty.denote interpret sample)]
    (cost : M.Cost) :
    CostedAlgebra M interpret (signature sample) where
  exec operation _args :=
    match operation with
    | .sample =>
        RandCosted.sampleWithCost
          (Crypto.Infrastructure.Probability.uniformPMF
            (Ty.denote interpret sample))
          (fun _ => cost)

theorem costBound_exec
    (M : CostModel.{uCost})
    {Base : Type uBase} (interpret : Base → Type uValue)
    (sample : Ty Base)
    [Fintype (Ty.denote interpret sample)]
    [Nonempty (Ty.denote interpret sample)]
    (cost : M.Cost)
    {Args Result : Ty Base}
    (operation : (signature sample).Op Args Result)
    (args : Ty.denote interpret Args) :
    RandCosted.CostBound
      ((algebra M interpret sample cost).exec operation args) cost := by
  letI := M.instPartialOrder
  cases operation
  intro result hresult
  simp only [algebra, RandCosted.sampleWithCost] at hresult
  rw [PMF.mem_support_map_iff] at hresult
  rcases hresult with ⟨value, _hvalue, hresult⟩
  subst result
  exact le_refl cost

@[simp] theorem valueDist_exec
    (M : CostModel.{uCost})
    {Base : Type uBase} (interpret : Base → Type uValue)
    (sample : Ty Base)
    [Fintype (Ty.denote interpret sample)]
    [Nonempty (Ty.denote interpret sample)]
    (cost : M.Cost) (args : Ty.denote interpret .unit) :
    RandCosted.valueDist
        ((algebra M interpret sample cost).exec
          UniformSampleOperation.sample args) =
      Crypto.Infrastructure.Probability.uniformPMF
        (Ty.denote interpret sample) := by
  simp [algebra]

end UniformSampleOperation

/--
A distribution/sampler reference for one object-language type.

The operation identifies the chosen distribution inside a signature; its
actual `PMF` is supplied by the signature's algebra. Thus first-order syntax
can choose among distributions without storing a host-language `PMF`.
-/
structure Sampler
    {Base : Type uBase} (S : Signature.{uBase, uOp} Base)
    (sampleTy : Ty Base) where
  operation : S.Op .unit sampleTy

/- Smart constructors for built-in operations inside a composite signature. -/
namespace SmartOperation

def unifSamp
    {Base : Type uBase} {S : Signature.{uBase, uOp} Base}
    {sample : Ty Base}
    [Signature.Embedding (UniformSampleOperation.signature sample) S] :
    S.Op .unit sample :=
  Signature.inject
    (source := UniformSampleOperation.signature sample)
    UniformSampleOperation.sample

/-- Inject a sampler operation once and package its result type with it. -/
def sampler
    {Base : Type uBase}
    {source : Signature.{uBase, uSourceOp} Base}
    {target : Signature.{uBase, uOp} Base}
    {sampleTy : Ty Base}
    (operation : source.Op .unit sampleTy)
    [Signature.Embedding source target] : Sampler target sampleTy where
  operation := Signature.inject operation

/-- The built-in uniform distribution over the specified finite carrier. -/
def uniformSampler
    {Base : Type uBase} {S : Signature.{uBase, uOp} Base}
    (sampleTy : Ty Base)
    [Signature.Embedding (UniformSampleOperation.signature sampleTy) S] :
    Sampler S sampleTy where
  operation := SmartOperation.unifSamp

def add
    {Base : Type uBase} {S : Signature.{uBase, uOp} Base}
    {carrier : Ty Base}
    [Signature.Embedding (AddOperation.signature carrier) S] :
    S.Op (.prod carrier carrier) carrier :=
  Signature.inject
    (source := AddOperation.signature carrier) AddOperation.add

def neg
    {Base : Type uBase} {S : Signature.{uBase, uOp} Base}
    {carrier : Ty Base}
    [Signature.Embedding (NegOperation.signature carrier) S] :
    S.Op carrier carrier :=
  Signature.inject
    (source := NegOperation.signature carrier) NegOperation.neg

def sub
    {Base : Type uBase} {S : Signature.{uBase, uOp} Base}
    {carrier : Ty Base}
    [Signature.Embedding (SubOperation.signature carrier) S] :
    S.Op (.prod carrier carrier) carrier :=
  Signature.inject
    (source := SubOperation.signature carrier) SubOperation.sub

def smul
    {Base : Type uBase} {S : Signature.{uBase, uOp} Base}
    {scalar carrier : Ty Base}
    [Signature.Embedding (SMulOperation.signature scalar carrier) S] :
    S.Op (.prod scalar carrier) carrier :=
  Signature.inject
    (source := SMulOperation.signature scalar carrier) SMulOperation.smul

def mul
    {Base : Type uBase} {S : Signature.{uBase, uOp} Base}
    {value : Ty Base}
    [Signature.Embedding (MulOperation.signature value) S] :
    S.Op (.prod value value) value :=
  Signature.inject
    (source := MulOperation.signature value) MulOperation.mul

end SmartOperation

end CryptoFirstOrder

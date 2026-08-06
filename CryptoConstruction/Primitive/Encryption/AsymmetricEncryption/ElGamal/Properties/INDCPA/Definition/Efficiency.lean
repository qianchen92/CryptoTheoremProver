import CryptoFirstOrder.Adapter.OneShotChoiceAdd
import CryptoConstruction.Primitive.Encryption.AsymmetricEncryption.ElGamal.Properties.Semantics

/-! # Efficiency data for the executable ElGamal DDH reduction -/

namespace CryptoConstruction.Primitive.Encryption.AsymmetricEncryption.ElGamal

open Crypto.Infrastructure.Computation.Cost
open Crypto.Infrastructure.Computation
open Crypto.Infrastructure.Computation.Oracle

universe uCost uParameter uScalar uGroup

variable
    {M : CostModel.{uCost}}
    {Parameter : Type uParameter}
    {Scalar : Type uScalar}
    {Carrier : Type uGroup}

/--
Explicit resource data for compiling the closed DDH reduction. Structural
charges are fixed costs; the parameter-dependent group addition is bounded by
the family's `addBudget` at the parameter's security tag.
-/
structure ReductionEfficiencyCertificate
    (measure : NatMeasure M)
    (F : Family M Parameter Scalar Carrier) where
  prepareCost : M.Cost
  rejectCost : M.Cost
  queryPrefixCost : M.Cost
  querySuffixCost : M.Cost
  repeatQueryCost : M.Cost
  prepareRuntime : Crypto.SecPar → Nat
  rejectRuntime : Crypto.SecPar → Nat
  addRuntime : Crypto.SecPar → Nat
  queryRuntime : Crypto.SecPar → Nat
  queryBudget : Crypto.SecPar → M.Cost
  prepareCost_le_runtime : ∀ sec,
    measure (M.instAddMonoid.add prepareCost M.instAddMonoid.zero) ≤
      prepareRuntime sec
  rejectCost_le_runtime : ∀ sec,
    measure (M.instAddMonoid.add rejectCost M.instAddMonoid.zero) ≤
      rejectRuntime sec
  addBudget_le_runtime : ∀ sec,
    measure (F.addBudget sec) ≤ addRuntime sec
  firstQuery_le_budget : ∀ parameter,
    M.instPartialOrder.le
      (M.instAddMonoid.add queryPrefixCost
        (M.instAddMonoid.add (F.addCost parameter)
          (M.instAddMonoid.add querySuffixCost M.instAddMonoid.zero)))
      (queryBudget (F.parameterSec parameter))
  repeatQuery_le_budget : ∀ sec,
    M.instPartialOrder.le
      (M.instAddMonoid.add repeatQueryCost M.instAddMonoid.zero)
      (queryBudget sec)
  queryBudget_le_runtime : ∀ sec,
    measure (queryBudget sec) ≤ queryRuntime sec
  prepareRuntime_isPoly :
    Crypto.Infrastructure.Asymptotic.IsPolyBounded prepareRuntime
  rejectRuntime_isPoly :
    Crypto.Infrastructure.Asymptotic.IsPolyBounded rejectRuntime
  addRuntime_isPoly :
    Crypto.Infrastructure.Asymptotic.IsPolyBounded addRuntime
  queryRuntime_isPoly :
    Crypto.Infrastructure.Asymptotic.IsPolyBounded queryRuntime
  repeatBudgetMono : ∀ sec {first second : Nat}, first ≤ second →
    M.instPartialOrder.le
      (Oracle.Program.repeatCost M first (queryBudget sec))
      (Oracle.Program.repeatCost M second (queryBudget sec))
  exchange : Oracle.Program.CostExchange M

end CryptoConstruction.Primitive.Encryption.AsymmetricEncryption.ElGamal

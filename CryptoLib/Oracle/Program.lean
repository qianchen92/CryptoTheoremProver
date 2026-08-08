import CryptoLib.Oracle.Spec
import CryptoLib.Core.Infrastructure.Computation.Cost.Randomized

namespace CryptoLib.Oracle

open CryptoLib.Core.Infrastructure.Computation.Cost

universe uCost uOracle uQuery uResponse uValue

/--
An adaptive oracle program parameterized by its exact caller-side query cost.

The query constructor carries no cost.  Issuance cost is produced only by
the issue-cost function; the response, updated state, and internal oracle cost are
produced only by the environment used by the exact interpreter.
-/
inductive Program
    {M : CostModel.{uCost}}
    {Spec : OracleSpec.{uOracle, uQuery, uResponse}}
    (issueCost : (name : Spec.Name) → Spec.Query name → M.Cost) :
    Type (max uValue uResponse) →
      Type (max (uCost + 1) (uOracle + 1) uQuery (uResponse + 1) (uValue + 1)) where
  | pure {α : Type (max uValue uResponse)} : α → Program issueCost α
  | bind {α β : Type (max uValue uResponse)} :
      Program issueCost α → (α → Program issueCost β) → Program issueCost β
  | liftCosted {α : Type (max uValue uResponse)} :
      RandCosted M α → Program issueCost α
  | query (name : Spec.Name) :
      Spec.Query name → Program issueCost (ULift.{uValue} (Spec.Response name))

namespace Program

variable
    {M : CostModel.{uCost}}
    {Spec : OracleSpec.{uOracle, uQuery, uResponse}}
    {issueCost : (name : Spec.Name) → Spec.Query name → M.Cost}

instance : Monad (Program issueCost) where
  pure := Program.pure
  bind := Program.bind

end Program

end CryptoLib.Oracle

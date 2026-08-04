import Crypto.Infrastructure.Computation.Algebra.Handler
import Crypto.Infrastructure.Computation.Oracle.Spec

namespace Crypto.Infrastructure.Computation.Oracle

open Crypto.Infrastructure.Computation.Algebra
open Crypto.Infrastructure.Computation.Cost

universe uCost uOracle uQuery uResponse uValue

/-- A typed caller-side primitive that issues one oracle query. -/
inductive QueryIssue
    (Spec : OracleSpec.{uOracle, uQuery, uResponse}) : Type → Type (max uOracle uQuery) where
  | issue (name : Spec.Name) (query : Spec.Query name) : QueryIssue Spec Unit

namespace QueryIssue

/-- The result-indexed signature of caller-side oracle-query issuance. -/
def signature (Spec : OracleSpec.{uOracle, uQuery, uResponse}) :
    Signature.{0, max uOracle uQuery} where
  Op := QueryIssue Spec

end QueryIssue

/--
An adaptive oracle program parameterized by its exact caller-side query handler.

The query constructor carries no cost.  Issuance cost is produced only by
`issueAlgebra.exec`; the response, updated state, and internal oracle cost are
produced only by the environment used by the exact interpreter.
-/
inductive Program
    {M : CostModel.{uCost}}
    {Spec : OracleSpec.{uOracle, uQuery, uResponse}}
    (issueAlgebra : CostedAlgebra M (QueryIssue.signature Spec)) :
    Type (max uValue uResponse) →
      Type (max (uCost + 1) (uOracle + 1) uQuery (uResponse + 1) (uValue + 1)) where
  | pure {α : Type (max uValue uResponse)} : α → Program issueAlgebra α
  | bind {α β : Type (max uValue uResponse)} :
      Program issueAlgebra α → (α → Program issueAlgebra β) → Program issueAlgebra β
  | liftCosted {α : Type (max uValue uResponse)} :
      RandCosted M α → Program issueAlgebra α
  | query (name : Spec.Name) :
      Spec.Query name → Program issueAlgebra (ULift.{uValue} (Spec.Response name))

namespace Program

variable
    {M : CostModel.{uCost}}
    {Spec : OracleSpec.{uOracle, uQuery, uResponse}}
    {issueAlgebra : CostedAlgebra M (QueryIssue.signature Spec)}

instance : Monad (Program issueAlgebra) where
  pure := Program.pure
  bind := Program.bind

end Program

end Crypto.Infrastructure.Computation.Oracle

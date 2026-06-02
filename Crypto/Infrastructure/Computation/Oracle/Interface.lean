import Crypto.Infrastructure.Asymptotic.SecurityParameter
import Mathlib.Probability.ProbabilityMassFunction.Basic
import Mathlib.Probability.ProbabilityMassFunction.Monad

namespace Crypto.Infrastructure.Computation.Oracle

universe uOracle uQuery uResponse uState uValue

/-- A heterogeneous collection of oracle endpoints, indexed by oracle name. -/
structure OracleSpec where
  Name : Type uOracle
  Query : Name → Type uQuery
  Response : (name : Name) → Type uResponse

/-- A stateful probabilistic implementation of every endpoint in an oracle spec. -/
structure OracleEnv (Spec : OracleSpec.{uOracle, uQuery, uResponse}) where
  State : Type uState
  init : State
  query :
    (name : Spec.Name) →
    Crypto.SecPar →
    State →
    Spec.Query name →
    PMF (Spec.Response name × State)

/-- A stateful probabilistic oracle indexed by the security parameter. -/
structure OracleFn (Query : Type uQuery) (Response : Type uResponse) where
  State : Type uState
  init : State
  query : Crypto.SecPar → State → Query → PMF (Response × State)

/--
A program with oracle access.

This is a syntax for adaptive oracle interactions.  The machine builds an
`OracleProgram`; the interpreter is responsible for threading the oracle state.
This keeps oracle state hidden from the machine interface.
-/
inductive OracleProgram (Spec : OracleSpec.{uOracle, uQuery, uResponse}) :
    Type (max uValue uResponse) →
      Type (max (uOracle + 1) uQuery (uResponse + 1) (uValue + 1)) where
  | pure {α : Type (max uValue uResponse)} : α → OracleProgram Spec α
  | bind {α : Type (max uValue uResponse)} {β : Type (max uValue uResponse)} :
      OracleProgram Spec α → (α → OracleProgram Spec β) → OracleProgram Spec β
  | liftPMF {α : Type (max uValue uResponse)} : PMF α → OracleProgram Spec α
  | query (name : Spec.Name) :
      Spec.Query name → OracleProgram Spec (ULift.{uValue} (Spec.Response name))

namespace OracleProgram

variable {Spec : OracleSpec.{uOracle, uQuery, uResponse}}

instance : Monad (OracleProgram Spec) where
  pure := fun value => OracleProgram.pure value
  bind := fun program next => OracleProgram.bind program next

/-- Interpret an oracle program against an environment, threading environment state linearly. -/
noncomputable def run
    {α : Type (max uValue uResponse)}
    (program : OracleProgram Spec α)
    (sec : Crypto.SecPar)
    (env : OracleEnv.{uOracle, uQuery, uResponse, uState} Spec)
    (state : env.State) :
    PMF (α × env.State) :=
  match program with
  | OracleProgram.pure value => PMF.pure (value, state)
  | OracleProgram.bind first next =>
      PMF.bind (run first sec env state) fun result =>
        run (next result.1) sec env result.2
  | OracleProgram.liftPMF dist =>
      PMF.bind dist fun value =>
        PMF.pure (value, state)
  | OracleProgram.query name oracleQuery =>
      PMF.bind (env.query name sec state oracleQuery) fun result =>
        PMF.pure (ULift.up result.1, result.2)

/-- Interpret an oracle program from the environment's initial state and forget the final state. -/
noncomputable def runWithEnv
    {α : Type (max uValue uResponse)}
    (program : OracleProgram Spec α)
    (sec : Crypto.SecPar)
    (env : OracleEnv.{uOracle, uQuery, uResponse, uState} Spec) :
    PMF α :=
  PMF.bind (run program sec env env.init) fun result =>
    PMF.pure result.1

@[simp] theorem runWithEnv_pure
    {α : Type (max uValue uResponse)}
    (value : α)
    (sec : Crypto.SecPar)
    (env : OracleEnv.{uOracle, uQuery, uResponse, uState} Spec) :
    runWithEnv (pure value : OracleProgram Spec α) sec env = PMF.pure value := by
  simp [runWithEnv, run]

end OracleProgram

end Crypto.Infrastructure.Computation.Oracle

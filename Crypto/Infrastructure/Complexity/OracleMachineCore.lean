import Crypto.Infrastructure.Complexity.OracleImplementation

namespace Crypto.Infrastructure.Complexity

open Crypto.Infrastructure.Computation
open Crypto.Infrastructure.Computation.Algebra
open Crypto.Infrastructure.Computation.Cost
open Crypto.Infrastructure.Computation.Oracle

universe uCost uIn uOut uOracle uQuery uResponse uState

/--
An adaptive oracle machine over one exact caller-side cost model.

This definition is separated from PPT admission so operational compilers can
refer to the executable caller without creating an import cycle.
-/
structure OracleMachine
    (M : CostModel.{uCost})
    (Input : Crypto.SecPar → Type uIn)
    (Output : (sec : Crypto.SecPar) → Input sec → Type uOut)
    (Spec :
      (sec : Crypto.SecPar) → Input sec →
        OracleSpec.{uOracle, uQuery, uResponse}) where
  issueAlgebra :
    (sec : Crypto.SecPar) → (input : Input sec) →
      CostedAlgebra M (QueryIssue.signature (Spec sec input))
  program :
    (sec : Crypto.SecPar) → (input : Input sec) →
      Oracle.Program (issueAlgebra sec input)
        (ULift.{uResponse} (Output sec input))

namespace OracleMachine

variable
    {M : CostModel.{uCost}}
    {Input : Crypto.SecPar → Type uIn}
    {Output : (sec : Crypto.SecPar) → Input sec → Type uOut}
    {Spec :
      (sec : Crypto.SecPar) → Input sec →
        OracleSpec.{uOracle, uQuery, uResponse}}

/-- Run the machine through the sole exact oracle interpreter. -/
noncomputable def runExact
    (machine : OracleMachine M Input Output Spec)
    (sec : Crypto.SecPar) (input : Input sec)
    (env :
      CostedOracleEnv.{uCost, uOracle, uQuery, uResponse, uState}
        M (Spec sec input)) :
    PMF
      (ExactRunResult M (Spec sec input) env.State
        (ULift.{uResponse} (Output sec input))) :=
  Oracle.Program.runExactFromInit (machine.program sec input) sec env

/-- Retain the returned value and exact ordered composition cost. -/
noncomputable def runCosted
    (machine : OracleMachine M Input Output Spec)
    (sec : Crypto.SecPar) (input : Input sec)
    (env :
      CostedOracleEnv.{uCost, uOracle, uQuery, uResponse, uState}
        M (Spec sec input)) :
    RandCosted M (Output sec input) :=
  RandCosted.map ULift.down
    (Oracle.Program.runCosted (machine.program sec input) sec env)

/-- Ordinary value semantics against a cost-erased environment. -/
noncomputable def runWithEnv
    (machine : OracleMachine M Input Output Spec)
    (sec : Crypto.SecPar) (input : Input sec)
    (env : OracleEnv.{uOracle, uQuery, uResponse, uState} (Spec sec input)) :
    PMF (Output sec input) :=
  PMF.map ULift.down
    (Oracle.Program.runWithEnv (machine.program sec input) sec env)

/-- Exact composition with the authoritative implementation environment. -/
noncomputable def runWithImplementation
    (machine : OracleMachine M Input Output Spec)
    (implementation :
      OracleImplementation.{uCost, uIn, uOracle, uQuery, uResponse, uState}
        M Input Spec)
    (sec : Crypto.SecPar) (input : Input sec) :
    RandCosted M (Output sec input) :=
  machine.runCosted sec input (implementation.env sec input)

/-- Exact execution erases to the ordinary semantics of the same environment. -/
@[simp] theorem valueDist_runCosted
    (machine : OracleMachine M Input Output Spec)
    (sec : Crypto.SecPar) (input : Input sec)
    (env :
      CostedOracleEnv.{uCost, uOracle, uQuery, uResponse, uState}
        M (Spec sec input)) :
    RandCosted.valueDist (machine.runCosted sec input env) =
      machine.runWithEnv sec input env.erase := by
  simp only [runCosted, runWithEnv, RandCosted.valueDist_map]
  rw [Oracle.Program.valueDist_runCosted_eq_runWithEnv_erase]

/-- The implementation wrapper introduces no new probability semantics. -/
@[simp] theorem valueDist_runWithImplementation
    (machine : OracleMachine M Input Output Spec)
    (implementation :
      OracleImplementation.{uCost, uIn, uOracle, uQuery, uResponse, uState}
        M Input Spec)
    (sec : Crypto.SecPar) (input : Input sec) :
    RandCosted.valueDist
        (machine.runWithImplementation implementation sec input) =
      machine.runWithEnv sec input
        (implementation.env sec input).erase := by
  exact machine.valueDist_runCosted sec input (implementation.env sec input)

end OracleMachine

end Crypto.Infrastructure.Complexity

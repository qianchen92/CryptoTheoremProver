import CryptoLib.Core.Infrastructure.Computation.Oracle.Spec

namespace CryptoLib.Core.Infrastructure.Computation.Oracle

universe uOracle uQuery uResponse

/-- The ordered oracle names queried along one execution path. -/
structure QueryTrace (Spec : OracleSpec.{uOracle, uQuery, uResponse}) where
  entries : List Spec.Name

namespace QueryTrace

variable {Spec : OracleSpec.{uOracle, uQuery, uResponse}}

/-- The trace containing no oracle calls. -/
def empty (Spec : OracleSpec.{uOracle, uQuery, uResponse}) : QueryTrace Spec :=
  ⟨[]⟩

/-- The trace containing one call to `name`. -/
def singleton (name : Spec.Name) : QueryTrace Spec :=
  ⟨[name]⟩

/-- Sequential trace composition. -/
def append (first second : QueryTrace Spec) : QueryTrace Spec :=
  ⟨first.entries ++ second.entries⟩

/-- Number of calls to one fixed oracle name. -/
noncomputable def count (trace : QueryTrace Spec) (name : Spec.Name) : Nat := by
  classical
  exact trace.entries.count name

/-- Total number of oracle calls in the trace. -/
def total (trace : QueryTrace Spec) : Nat :=
  trace.entries.length

@[simp] theorem entries_empty : (empty Spec).entries = [] :=
  rfl

@[simp] theorem entries_singleton (name : Spec.Name) :
    (singleton name).entries = [name] :=
  rfl

@[simp] theorem entries_append (first second : QueryTrace Spec) :
    (append first second).entries = first.entries ++ second.entries :=
  rfl

@[simp] theorem count_empty (name : Spec.Name) :
    (empty Spec).count name = 0 := by
  classical
  simp [count, empty]

@[simp] theorem count_singleton_self (name : Spec.Name) :
    (singleton name).count name = 1 := by
  classical
  simp [count, singleton]

@[simp] theorem count_singleton_of_ne {queried name : Spec.Name}
    (hne : queried ≠ name) :
    (singleton queried).count name = 0 := by
  classical
  simp [count, singleton, hne]

@[simp] theorem count_append (first second : QueryTrace Spec) (name : Spec.Name) :
    (append first second).count name = first.count name + second.count name := by
  classical
  simp [count, append]

@[simp] theorem total_empty : (empty Spec).total = 0 :=
  rfl

@[simp] theorem total_singleton (name : Spec.Name) :
    (singleton name).total = 1 :=
  rfl

@[simp] theorem total_append (first second : QueryTrace Spec) :
    (append first second).total = first.total + second.total := by
  simp [total, append]

theorem count_le_total (trace : QueryTrace Spec) (name : Spec.Name) :
    trace.count name ≤ trace.total := by
  classical
  exact List.count_le_length

end QueryTrace

end CryptoLib.Core.Infrastructure.Computation.Oracle

import CryptoLib.Program.Transform.Basic
import CryptoLib.Test.Infrastructure.Computation.TraceCost

namespace CryptoLib.Test.Program.Transformations

open CryptoLib.Core.Infrastructure.Computation.Cost
open CryptoLib.Program

/-- One carrier is enough to exercise typed variables and structural types. -/
inductive TestBase where
  | bit
  deriving DecidableEq

abbrev interpret : TestBase → Type
  | .bit => Bool

abbrev bitTy : Ty TestBase :=
  .base .bit

/-- Events are intentionally kept in execution order by the trace model. -/
inductive TraceEvent where
  | first
  | second
  | thenArm
  | elseArm
  | afterBranch
  | source
  | middleLeft
  | middleRight
  | targetLeft
  | targetRight
  deriving DecidableEq, Repr

abbrev EventTraceCost :=
  CryptoLib.Test.Infrastructure.Computation.TraceCost TraceEvent

abbrev eventTraceCostModel :=
  CryptoLib.Test.Infrastructure.Computation.TraceCost.costModel TraceEvent

def eventCost (event : TraceEvent) : EventTraceCost :=
  CryptoLib.Test.Infrastructure.Computation.TraceCost.singleton event

inductive TraceOperation :
    Ty TestBase → Ty TestBase → Type where
  | tick (event : TraceEvent) : TraceOperation .unit .unit

abbrev eventSignature : Signature TestBase where
  Op := TraceOperation

noncomputable def eventAlgebra :
    CostedAlgebra eventTraceCostModel interpret eventSignature where
  exec operation _args :=
    match operation with
    | .tick event =>
        RandCosted.liftCosted
          (⟨ULift.up (), eventCost event⟩ :
            Costed eventTraceCostModel (Ty.denote interpret .unit))

/-- One nonzero-cost primitive call in an arbitrary surrounding context. -/
def tickCode (event : TraceEvent) {context : List (Ty TestBase)} :
    Code interpret eventSignature context .unit :=
  .call (TraceOperation.tick event) .unit (.ret (.var .here))

theorem runCosted_tick
    (event : TraceEvent) {context : List (Ty TestBase)}
    (environment : Env interpret context) :
    Code.runCosted eventAlgebra (tickCode event) environment =
      RandCosted.liftCosted
        (⟨ULift.up (), eventCost event⟩ :
          Costed eventTraceCostModel (Ty.denote interpret .unit)) := by
  simp only [tickCode, Code.runCosted, eventAlgebra]
  exact RandCosted.liftCosted_bind_liftCosted _ _

/-- The selected outer variable sits below both a pure and a call binder. -/
def nestedBinderCode :
    Code interpret eventSignature [bitTy] bitTy :=
  .letPure (.var .here)
    (.call (TraceOperation.tick .first) .unit
      (.ret (.var (.there (.there .here)))))

/-- Renaming traverses nested `letPure` and `call` binders without capture. -/
theorem rename_under_nested_let_call :
    nestedBinderCode.rename (Ren.weaken : Ren [bitTy] [bitTy, bitTy]) =
      Code.letPure (.var (.there .here))
        (.call (TraceOperation.tick .first) .unit
          (.ret (.var (.there (.there (.there .here)))))) := by
  rfl

/-- A product whose two fields exercise the option-expression constructors. -/
def productOptionExpression :
    Expr interpret [bitTy, bitTy]
      (.prod (.option bitTy) (.option bitTy)) :=
  .pair (.some (.var .here)) (.some (.var (.there .here)))

def productOptionSubstitution :
    Sub interpret [bitTy, bitTy] [] :=
  Sub.cons (.constant true)
    (Sub.cons (.constant false) (Sub.empty (interpret := interpret)))

/-- Substitution is structural through both products and options. -/
theorem subst_product_and_option :
    productOptionExpression.subst productOptionSubstitution =
      Expr.pair (.some (.constant true)) (.some (.constant false)) := by
  rfl

def firstOperation : Code interpret eventSignature [] .unit :=
  tickCode .first

def secondOperation : Code interpret eventSignature [.unit] .unit :=
  tickCode .second

/-- Two primitive calls are combined solely by first-order syntax. -/
def sequencedOperations : Code interpret eventSignature [] .unit :=
  Code.seq firstOperation secondOperation

/-- Both nonzero primitive costs occur in their exact left-to-right order. -/
theorem seq_two_nonzero_operations_exact :
    Code.runCosted eventAlgebra sequencedOperations .nil =
      RandCosted.liftCosted
        (⟨ULift.up (), ⟨[.first, .second]⟩⟩ :
          Costed eventTraceCostModel (Ty.denote interpret .unit)) := by
  unfold sequencedOperations
  rw [Code.runCosted_seq]
  simp only [firstOperation, secondOperation, runCosted_tick]
  rw [RandCosted.liftCosted_bind_liftCosted]
  rfl

def selectedBranch (condition : Bool) :
    Code interpret eventSignature [] .unit :=
  .branch (.bool condition) (tickCode .thenArm) (tickCode .elseArm)

def afterBranch : Code interpret eventSignature [.unit] .unit :=
  tickCode .afterBranch

def sequencedBranch (condition : Bool) :
    Code interpret eventSignature [] .unit :=
  Code.seq (selectedBranch condition) afterBranch

/-- Sequencing is distributed into the true branch arm. -/
theorem seq_true_branch_exact :
    Code.runCosted eventAlgebra (sequencedBranch true) .nil =
      RandCosted.liftCosted
        (⟨ULift.up (), ⟨[.thenArm, .afterBranch]⟩⟩ :
          Costed eventTraceCostModel (Ty.denote interpret .unit)) := by
  unfold sequencedBranch
  rw [Code.runCosted_seq]
  simp only [selectedBranch, Code.runCosted, Expr.eval]
  rw [if_pos True.intro]
  simp only [runCosted_tick, afterBranch]
  rw [RandCosted.liftCosted_bind_liftCosted]
  rfl

/-- Sequencing is distributed into the false branch arm. -/
theorem seq_false_branch_exact :
    Code.runCosted eventAlgebra (sequencedBranch false) .nil =
      RandCosted.liftCosted
        (⟨ULift.up (), ⟨[.elseArm, .afterBranch]⟩⟩ :
          Costed eventTraceCostModel (Ty.denote interpret .unit)) := by
  unfold sequencedBranch
  rw [Code.runCosted_seq]
  simp only [selectedBranch, Code.runCosted, Expr.eval, Bool.false_eq_true,
    if_false, runCosted_tick, afterBranch]
  rw [RandCosted.liftCosted_bind_liftCosted]
  rfl

def oneTickProcedure (event : TraceEvent) :
    Procedure interpret eventSignature .unit .unit where
  body := tickCode event

def twoTickProcedure (firstEvent secondEvent : TraceEvent) :
    Procedure interpret eventSignature .unit .unit where
  body :=
    .call (TraceOperation.tick firstEvent) .unit
      (.call (TraceOperation.tick secondEvent) .unit (.ret (.var .here)))

/-- The first handler expands `source` into two ordered middle operations. -/
def expandSource : Handler interpret eventSignature eventSignature where
  body operation :=
    match operation with
    | TraceOperation.tick .source => twoTickProcedure .middleLeft .middleRight
    | TraceOperation.tick event => oneTickProcedure event

def lowerMiddleEvent : TraceEvent → TraceEvent
  | .middleLeft => .targetLeft
  | .middleRight => .targetRight
  | event => event

/-- The second handler lowers each middle operation independently. -/
def lowerMiddle : Handler interpret eventSignature eventSignature where
  body operation :=
    match operation with
    | TraceOperation.tick event => oneTickProcedure (lowerMiddleEvent event)

def sourceOperation : Code interpret eventSignature [] .unit :=
  tickCode .source

theorem runCosted_oneTickProcedure
    (event : TraceEvent)
    (input : Ty.denote interpret (.unit : Ty TestBase)) :
    Procedure.runCosted eventAlgebra (oneTickProcedure event) input =
      RandCosted.liftCosted
        (⟨ULift.up (), eventCost event⟩ :
          Costed eventTraceCostModel (Ty.denote interpret .unit)) := by
  change
    Code.runCosted eventAlgebra (tickCode event) (.cons input .nil) = _
  exact runCosted_tick event (.cons input .nil)

theorem runCosted_lowerMiddle_tick
    (event : TraceEvent)
    (input : Ty.denote interpret (.unit : Ty TestBase)) :
    (lowerMiddle.inducedAlgebra eventAlgebra).exec
        (TraceOperation.tick event) input =
      RandCosted.liftCosted
        (⟨ULift.up (), eventCost (lowerMiddleEvent event)⟩ :
          Costed eventTraceCostModel (Ty.denote interpret .unit)) := by
  change
    Procedure.runCosted eventAlgebra
        (oneTickProcedure (lowerMiddleEvent event)) input = _
  exact runCosted_oneTickProcedure (lowerMiddleEvent event) input

theorem runCosted_twoTick_lowered :
    Procedure.runCosted (lowerMiddle.inducedAlgebra eventAlgebra)
        (twoTickProcedure .middleLeft .middleRight) (ULift.up ()) =
      RandCosted.liftCosted
        (⟨ULift.up (), ⟨[.targetLeft, .targetRight]⟩⟩ :
          Costed eventTraceCostModel (Ty.denote interpret .unit)) := by
  simp only [Procedure.runCosted, twoTickProcedure, Code.runCosted,
    runCosted_lowerMiddle_tick, Expr.eval, Env.get]
  rw [RandCosted.bind_pure]
  rw [RandCosted.liftCosted_bind_liftCosted]
  rfl

theorem runCosted_expandSource_induced :
    (expandSource.inducedAlgebra
        (lowerMiddle.inducedAlgebra eventAlgebra)).exec
        (TraceOperation.tick .source) (ULift.up ()) =
      RandCosted.liftCosted
        (⟨ULift.up (), ⟨[.targetLeft, .targetRight]⟩⟩ :
          Costed eventTraceCostModel (Ty.denote interpret .unit)) := by
  change
    Procedure.runCosted (lowerMiddle.inducedAlgebra eventAlgebra)
        (twoTickProcedure .middleLeft .middleRight) (ULift.up ()) = _
  exact runCosted_twoTick_lowered

/-- Concrete identity handling preserves the complete costed distribution. -/
theorem identity_handler_exact :
    Code.runCosted eventAlgebra
        (sourceOperation.handle (Handler.id eventSignature)) .nil =
      Code.runCosted eventAlgebra sourceOperation .nil := by
  exact Code.runCosted_handle_id eventAlgebra sourceOperation .nil

/-- Composed and staged concrete handlers are exactly semantically equal. -/
theorem composed_handlers_exact :
    Code.runCosted eventAlgebra
        (sourceOperation.handle (lowerMiddle.comp expandSource)) .nil =
      Code.runCosted eventAlgebra
        ((sourceOperation.handle expandSource).handle lowerMiddle) .nil := by
  exact Code.runCosted_handle_comp expandSource lowerMiddle eventAlgebra
    sourceOperation .nil

/-- The composed handler retains both expanded operations and their order. -/
theorem composed_handler_ordered_trace :
    Code.runCosted eventAlgebra
        (sourceOperation.handle (lowerMiddle.comp expandSource)) .nil =
      RandCosted.liftCosted
        (⟨ULift.up (), ⟨[.targetLeft, .targetRight]⟩⟩ :
          Costed eventTraceCostModel (Ty.denote interpret .unit)) := by
  rw [Code.runCosted_handle]
  rw [Handler.inducedAlgebra_comp]
  unfold sourceOperation tickCode
  simp only [Code.runCosted, runCosted_expandSource_induced, Expr.eval,
    Env.get]
  rw [RandCosted.bind_pure]

/-- The trace cost model detects an illegal reordering of the same events. -/
theorem ordered_trace_is_not_reversed :
    (⟨[.first, .second]⟩ : EventTraceCost) ≠ ⟨[.second, .first]⟩ := by
  decide

end CryptoLib.Test.Program.Transformations

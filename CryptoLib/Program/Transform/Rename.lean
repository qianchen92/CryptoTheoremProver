import CryptoLib.Program.Semantics

namespace CryptoLib.Program

open CryptoLib.Core.Infrastructure.Computation.Cost

universe uCost uBase uValue uOp

/-- A type-preserving renaming between typed de Bruijn contexts. -/
abbrev Ren
    {Base : Type uBase} (source target : List (Ty Base)) :=
  ∀ {value}, Var source value → Var target value

namespace Ren

/-- The identity typed renaming. -/
def id
    {Base : Type uBase} {context : List (Ty Base)} :
    Ren context context :=
  fun index ↦ index

/-- Compose typed renamings, applying `first` before `second`. -/
def comp
    {Base : Type uBase}
    {source middle target : List (Ty Base)}
    (second : Ren middle target) (first : Ren source middle) :
    Ren source target :=
  fun index ↦ second (first index)

/-- Shift every variable past one newly inserted context entry. -/
def weaken
    {Base : Type uBase} {context : List (Ty Base)}
    {inserted : Ty Base} :
    Ren context (inserted :: context) :=
  fun index ↦ .there index

/-- Lift a renaming under one binder, preserving the newly bound variable. -/
def lift
    {Base : Type uBase} {source target : List (Ty Base)}
    {bound : Ty Base} (rename : Ren source target) :
    Ren (bound :: source) (bound :: target)
  | _, .here => .here
  | _, .there index => .there (rename index)

/-- Lift a renaming under a statically known list of binders. -/
def liftPrefix
    {Base : Type uBase} {source target : List (Ty Base)}
    (binders : List (Ty Base)) (rename : Ren source target) :
    Ren (binders ++ source) (binders ++ target) :=
  match binders with
  | [] => rename
  | _ :: rest => lift (liftPrefix rest rename)

/-- Extensional equality for typed renamings. -/
@[ext] theorem ext
    {Base : Type uBase} {source target : List (Ty Base)}
    {left right : Ren source target}
    (equal : ∀ {value} (index : Var source value), left index = right index) :
    @left = @right := by
  funext value index
  exact equal index

@[simp] theorem rename_id
    {Base : Type uBase} {context : List (Ty Base)}
    {value : Ty Base} (index : Var context value) :
    (id : Ren context context) index = index :=
  rfl

@[simp] theorem rename_comp
    {Base : Type uBase}
    {source middle target : List (Ty Base)}
    (second : Ren middle target) (first : Ren source middle)
    {value : Ty Base} (index : Var source value) :
    comp second first index = second (first index) :=
  rfl

@[simp] theorem lift_id
    {Base : Type uBase} {context : List (Ty Base)}
    {bound : Ty Base} :
    @lift Base context context bound id =
      @id Base (bound :: context) := by
  apply ext
  intro value index
  cases index <;> rfl

@[simp] theorem lift_comp
    {Base : Type uBase}
    {source middle target : List (Ty Base)} {bound : Ty Base}
    (second : Ren middle target) (first : Ren source middle) :
    @lift Base source target bound (comp second first) =
      @comp Base (bound :: source) (bound :: middle) (bound :: target)
        (@lift Base middle target bound second)
        (@lift Base source middle bound first) := by
  apply ext
  intro value index
  cases index <;> rfl

end Ren

namespace Var

/-- Apply a typed renaming to a variable. -/
def rename
    {Base : Type uBase} {source target : List (Ty Base)}
    {value : Ty Base} (index : Var source value)
    (rename : Ren source target) :
    Var target value :=
  rename index

@[simp] theorem rename_id
    {Base : Type uBase} {context : List (Ty Base)}
    {value : Ty Base} (index : Var context value) :
    index.rename Ren.id = index :=
  rfl

@[simp] theorem rename_comp
    {Base : Type uBase}
    {source middle target : List (Ty Base)}
    {value : Ty Base} (index : Var source value)
    (first : Ren source middle) (second : Ren middle target) :
    (index.rename first).rename second =
      index.rename (Ren.comp second first) :=
  rfl

end Var

namespace Expr

/-- Rename every free variable in a pure expression. -/
def rename
    {Base : Type uBase} {interpret : Base → Type uValue}
    {source target : List (Ty Base)} {result : Ty Base}
    (expression : Expr interpret source result)
    (rename : Ren source target) :
    Expr interpret target result :=
  match expression with
  | .var index => .var (index.rename rename)
  | .unit => .unit
  | .bool value => .bool value
  | .constant value => .constant value
  | .pair left right => .pair (left.rename rename) (right.rename rename)
  | .fst product => .fst (product.rename rename)
  | .snd product => .snd (product.rename rename)
  | .none => .none
  | .some value => .some (value.rename rename)

@[simp] theorem rename_id
    {Base : Type uBase} {interpret : Base → Type uValue}
    {context : List (Ty Base)} {result : Ty Base}
    (expression : Expr interpret context result) :
    expression.rename Ren.id = expression := by
  induction expression <;> simp [rename, *]

@[simp] theorem rename_comp
    {Base : Type uBase} {interpret : Base → Type uValue}
    {source middle target : List (Ty Base)} {result : Ty Base}
    (expression : Expr interpret source result)
    (first : Ren source middle) (second : Ren middle target) :
    (expression.rename first).rename second =
      expression.rename (Ren.comp second first) := by
  induction expression <;> simp [rename, *]

end Expr

namespace Code

/-- Rename every free variable in first-order code. -/
def rename
    {Base : Type uBase} {interpret : Base → Type uValue}
    {S : Signature.{uBase, uOp} Base}
    {source target : List (Ty Base)} {result : Ty Base}
    (code : Code interpret S source result)
    (rename : Ren source target) :
    Code interpret S target result :=
  match code with
  | .ret value => .ret (value.rename rename)
  | .letPure value next =>
      .letPure (value.rename rename) (next.rename (Ren.lift rename))
  | .call operation args next =>
      .call operation (args.rename rename) (next.rename (Ren.lift rename))
  | .branch condition thenCode elseCode =>
      .branch (condition.rename rename)
        (thenCode.rename rename) (elseCode.rename rename)

@[simp] theorem rename_id
    {Base : Type uBase} {interpret : Base → Type uValue}
    {S : Signature.{uBase, uOp} Base}
    {context : List (Ty Base)} {result : Ty Base}
    (code : Code interpret S context result) :
    code.rename Ren.id = code := by
  induction code <;> simp [Code.rename, *]

@[simp] theorem rename_comp
    {Base : Type uBase} {interpret : Base → Type uValue}
    {S : Signature.{uBase, uOp} Base}
    {source middle target : List (Ty Base)} {result : Ty Base}
    (code : Code interpret S source result)
    (first : Ren source middle) (second : Ren middle target) :
    (code.rename first).rename second =
      code.rename (Ren.comp second first) := by
  induction code generalizing middle target <;>
    simp [Code.rename, *, Ren.lift_comp]

end Code

namespace Procedure

/-- Recontextualize a procedure body through its distinguished input. -/
def renameBody
    {Base : Type uBase} {interpret : Base → Type uValue}
    {S : Signature.{uBase, uOp} Base} {input output : Ty Base}
    {target : List (Ty Base)}
    (procedure : Procedure interpret S input output)
    (rename : Ren [input] target) :
    Code interpret S target output :=
  procedure.body.rename rename

end Procedure

namespace Env

/--
Two environments are related by a renaming when every source lookup agrees
with the corresponding target lookup.
-/
def Related
    {Base : Type uBase} {interpret : Base → Type uValue}
    {source target : List (Ty Base)} (rename : Ren source target)
    (sourceEnv : Env interpret source) (targetEnv : Env interpret target) : Prop :=
  ∀ {value} (index : Var source value),
    targetEnv.get (rename index) = sourceEnv.get index

theorem related_id
    {Base : Type uBase} {interpret : Base → Type uValue}
    {context : List (Ty Base)} (environment : Env interpret context) :
    Related Ren.id environment environment := by
  intro value index
  rfl

theorem related_lift
    {Base : Type uBase} {interpret : Base → Type uValue}
    {source target : List (Ty Base)} {bound : Ty Base}
    {rename : Ren source target}
    {sourceEnv : Env interpret source} {targetEnv : Env interpret target}
    (related : Related rename sourceEnv targetEnv)
    (value : Ty.denote interpret bound) :
    Related (Ren.lift rename) (.cons value sourceEnv) (.cons value targetEnv) := by
  intro result index
  cases index with
  | here => rfl
  | there index => exact related index

theorem related_lift_weaken
    {Base : Type uBase} {interpret : Base → Type uValue}
    {context : List (Ty Base)} {bound inserted : Ty Base}
    (environment : Env interpret context)
    (boundValue : Ty.denote interpret bound)
    (insertedValue : Ty.denote interpret inserted) :
    Related (Ren.lift (Ren.weaken : Ren context (inserted :: context)))
      (.cons boundValue environment)
      (.cons boundValue (.cons insertedValue environment)) := by
  intro result index
  cases index <;> rfl

end Env

namespace Expr

/-- Renaming preserves expression evaluation in related environments. -/
theorem eval_rename
    {Base : Type uBase} {interpret : Base → Type uValue}
    {source target : List (Ty Base)} {result : Ty Base}
    {ρ : Ren source target}
    {sourceEnv : Env interpret source} {targetEnv : Env interpret target}
    (related : Env.Related ρ sourceEnv targetEnv)
    (expression : Expr interpret source result) :
    (expression.rename ρ).eval targetEnv = expression.eval sourceEnv := by
  induction expression with
  | var index => exact related index
  | unit => rfl
  | bool value => rfl
  | constant value => rfl
  | pair left right ihLeft ihRight =>
      simp only [Expr.rename, eval, ihLeft, ihRight]
  | fst product ih => simp only [Expr.rename, eval, ih]
  | snd product ih => simp only [Expr.rename, eval, ih]
  | none => rfl
  | some value ih => simp only [Expr.rename, eval, ih]

end Expr

namespace Code

/-- Renaming preserves the complete exact execution distribution. -/
theorem runCosted_rename
    {M : CostModel.{uCost}}
    {Base : Type uBase} {interpret : Base → Type uValue}
    {S : Signature.{uBase, uOp} Base} (algebra : CostedAlgebra M interpret S)
    {source target : List (Ty Base)} {result : Ty Base}
    {rename : Ren source target}
    {sourceEnv : Env interpret source} {targetEnv : Env interpret target}
    (related : Env.Related rename sourceEnv targetEnv)
    (code : Code interpret S source result) :
    runCosted algebra (code.rename rename) targetEnv =
      runCosted algebra code sourceEnv := by
  induction code generalizing target with
  | ret value => simp only [Code.rename, runCosted, value.eval_rename related]
  | letPure value next ih =>
      simp only [Code.rename, runCosted]
      rw [value.eval_rename related]
      exact ih (Env.related_lift related (value.eval sourceEnv))
  | call operation args next ih =>
      simp only [Code.rename, runCosted]
      rw [args.eval_rename related]
      apply congrArg
        (RandCosted.bind (algebra.exec operation (args.eval sourceEnv)))
      funext value
      exact ih (Env.related_lift related value)
  | branch condition thenCode elseCode ihThen ihElse =>
      simp only [Code.rename, runCosted, condition.eval_rename related]
      split
      · exact ihThen related
      · exact ihElse related

/-- Cost erasure of `runCosted_rename`. -/
theorem valueDist_rename
    {M : CostModel.{uCost}}
    {Base : Type uBase} {interpret : Base → Type uValue}
    {S : Signature.{uBase, uOp} Base} (algebra : CostedAlgebra M interpret S)
    {source target : List (Ty Base)} {result : Ty Base}
    {rename : Ren source target}
    {sourceEnv : Env interpret source} {targetEnv : Env interpret target}
    (related : Env.Related rename sourceEnv targetEnv)
    (code : Code interpret S source result) :
    valueDist algebra (code.rename rename) targetEnv =
      valueDist algebra code sourceEnv := by
  simp only [valueDist, runCosted_rename algebra related code]

end Code

end CryptoLib.Program

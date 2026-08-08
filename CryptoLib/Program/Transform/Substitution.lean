import CryptoLib.Program.Transform.Rename

namespace CryptoLib.Program

open CryptoLib.Core.Infrastructure.Computation.Cost

universe uCost uBase uValue uOp

/-- A type-preserving substitution of expressions for typed variables. -/
abbrev Sub
    {Base : Type uBase} (interpret : Base → Type uValue)
    (source target : List (Ty Base)) :=
  ∀ {value}, Var source value → Expr interpret target value

namespace Sub

/-- Extensional equality for typed substitutions. -/
@[ext] theorem ext
    {Base : Type uBase} {interpret : Base → Type uValue}
    {source target : List (Ty Base)}
    {left right : Sub interpret source target}
    (equal : ∀ {value} (index : Var source value), left index = right index) :
    @left = @right := by
  funext value index
  exact equal index

/-- The identity substitution maps each variable to itself. -/
def id
    {Base : Type uBase} {interpret : Base → Type uValue}
    {context : List (Ty Base)} :
    Sub interpret context context :=
  fun index ↦ .var index

/-- Extend a substitution with an expression for the newest variable. -/
def cons
    {Base : Type uBase} {interpret : Base → Type uValue}
    {source target : List (Ty Base)} {head : Ty Base}
    (value : Expr interpret target head)
    (tail : Sub interpret source target) :
    Sub interpret (head :: source) target
  | _, .here => value
  | _, .there index => tail index

/-- The unique substitution out of an empty context. -/
def empty
    {Base : Type uBase} {interpret : Base → Type uValue}
    {target : List (Ty Base)} :
    Sub interpret [] target :=
  fun index ↦ nomatch index

/-- Substitute the sole source variable with an expression. -/
def single
    {Base : Type uBase} {interpret : Base → Type uValue}
    {context : List (Ty Base)} {head : Ty Base}
    (value : Expr interpret context head) :
    Sub interpret [head] context :=
  cons value (empty (interpret := interpret))

/-- Regard a typed renaming as a variable-only substitution. -/
def ofRen
    {Base : Type uBase} {interpret : Base → Type uValue}
    {source target : List (Ty Base)}
    (rename : Ren source target) :
    Sub interpret source target :=
  fun index ↦ .var (rename index)

/-- Lift a substitution under one binder. -/
def lift
    {Base : Type uBase} {interpret : Base → Type uValue}
    {source target : List (Ty Base)} {bound : Ty Base}
    (substitution : Sub interpret source target) :
    Sub interpret (bound :: source) (bound :: target)
  | _, .here => .var .here
  | _, .there index => (substitution index).rename Ren.weaken

@[simp] theorem id_apply
    {Base : Type uBase} {interpret : Base → Type uValue}
    {context : List (Ty Base)} {value : Ty Base}
    (index : Var context value) :
    (id (interpret := interpret)) index = Expr.var index :=
  rfl

@[simp] theorem cons_here
    {Base : Type uBase} {interpret : Base → Type uValue}
    {source target : List (Ty Base)} {head : Ty Base}
    (value : Expr interpret target head)
    (tail : Sub interpret source target) :
    cons value tail Var.here = value :=
  rfl

@[simp] theorem cons_there
    {Base : Type uBase} {interpret : Base → Type uValue}
    {source target : List (Ty Base)} {head value : Ty Base}
    (expression : Expr interpret target head)
    (tail : Sub interpret source target) (index : Var source value) :
    cons expression tail (.there index) = tail index :=
  rfl

@[simp] theorem single_here
    {Base : Type uBase} {interpret : Base → Type uValue}
    {context : List (Ty Base)} {head : Ty Base}
    (value : Expr interpret context head) :
    single value Var.here = value :=
  rfl

@[simp] theorem lift_id
    {Base : Type uBase} {interpret : Base → Type uValue}
    {context : List (Ty Base)} {bound : Ty Base} :
    @lift Base interpret context context bound (id (interpret := interpret)) =
      @id Base interpret (bound :: context) := by
  apply ext
  intro value index
  cases index <;> rfl

@[simp] theorem lift_ofRen
    {Base : Type uBase} {interpret : Base → Type uValue}
    {source target : List (Ty Base)} {bound : Ty Base}
    (rename : Ren source target) :
    @lift Base interpret source target bound (ofRen (interpret := interpret) rename) =
      @ofRen Base interpret (bound :: source) (bound :: target)
        (@Ren.lift Base source target bound rename) := by
  apply ext
  intro value index
  cases index <;> rfl

end Sub

namespace Expr

/-- Simultaneously substitute expressions for all free variables. -/
def subst
    {Base : Type uBase} {interpret : Base → Type uValue}
    {source target : List (Ty Base)} {result : Ty Base}
    (expression : Expr interpret source result)
    (substitution : Sub interpret source target) :
    Expr interpret target result :=
  match expression with
  | .var index => substitution index
  | .unit => .unit
  | .bool value => .bool value
  | .constant value => .constant value
  | .pair left right => .pair (left.subst substitution) (right.subst substitution)
  | .fst product => .fst (product.subst substitution)
  | .snd product => .snd (product.subst substitution)
  | .none => .none
  | .some value => .some (value.subst substitution)

@[simp] theorem subst_var
    {Base : Type uBase} {interpret : Base → Type uValue}
    {source target : List (Ty Base)} {result : Ty Base}
    (index : Var source result) (substitution : Sub interpret source target) :
    (Expr.var index).subst substitution = substitution index :=
  rfl

end Expr

namespace Sub

/-- Compose substitutions, applying `inner` before `outer`. -/
def comp
    {Base : Type uBase} {interpret : Base → Type uValue}
    {source middle target : List (Ty Base)}
    (outer : Sub interpret middle target)
    (inner : Sub interpret source middle) :
    Sub interpret source target :=
  fun index ↦ (inner index).subst outer

/-- Rename every expression produced by a substitution. -/
def rename
    {Base : Type uBase} {interpret : Base → Type uValue}
    {source middle target : List (Ty Base)}
    (rename : Ren middle target)
    (substitution : Sub interpret source middle) :
    Sub interpret source target :=
  fun index ↦ (substitution index).rename rename

/-- Precompose a substitution with a variable renaming. -/
def afterRen
    {Base : Type uBase} {interpret : Base → Type uValue}
    {source middle target : List (Ty Base)}
    (substitution : Sub interpret middle target)
    (rename : Ren source middle) :
    Sub interpret source target :=
  fun index ↦ substitution (rename index)

@[simp] theorem comp_apply
    {Base : Type uBase} {interpret : Base → Type uValue}
    {source middle target : List (Ty Base)}
    (outer : Sub interpret middle target)
    (inner : Sub interpret source middle)
    {value : Ty Base} (index : Var source value) :
    comp outer inner index = (inner index).subst outer :=
  rfl

end Sub

namespace Expr

@[simp] theorem subst_id
    {Base : Type uBase} {interpret : Base → Type uValue}
    {context : List (Ty Base)} {result : Ty Base}
    (expression : Expr interpret context result) :
    expression.subst (Sub.id (interpret := interpret)) = expression := by
  induction expression <;> simp [subst, *]

@[simp] theorem subst_comp
    {Base : Type uBase} {interpret : Base → Type uValue}
    {source middle target : List (Ty Base)} {result : Ty Base}
    (expression : Expr interpret source result)
    (inner : Sub interpret source middle)
    (outer : Sub interpret middle target) :
    (expression.subst inner).subst outer =
      expression.subst (Sub.comp outer inner) := by
  induction expression <;> simp [subst, Sub.comp, *]

theorem rename_eq_subst
    {Base : Type uBase} {interpret : Base → Type uValue}
    {source target : List (Ty Base)} {result : Ty Base}
    (expression : Expr interpret source result) (rename : Ren source target) :
    expression.rename rename =
      expression.subst (Sub.ofRen (interpret := interpret) rename) := by
  induction expression <;>
    simp [Expr.rename, subst, Sub.ofRen, Var.rename, *]

theorem subst_after_rename
    {Base : Type uBase} {interpret : Base → Type uValue}
    {source middle target : List (Ty Base)} {result : Ty Base}
    (expression : Expr interpret source result)
    (rename : Ren source middle)
    (substitution : Sub interpret middle target) :
    (expression.rename rename).subst substitution =
      expression.subst (Sub.afterRen substitution rename) := by
  induction expression <;>
    simp [Expr.rename, subst, Sub.afterRen, Var.rename, *]

theorem rename_after_subst
    {Base : Type uBase} {interpret : Base → Type uValue}
    {source middle target : List (Ty Base)} {result : Ty Base}
    (expression : Expr interpret source result)
    (substitution : Sub interpret source middle)
    (rename : Ren middle target) :
    (expression.subst substitution).rename rename =
      expression.subst (Sub.rename rename substitution) := by
  induction expression <;>
    simp [Expr.rename, subst, Sub.rename, *]

/-- Substitution lifted through weakening commutes with substitution. -/
theorem subst_lift_weaken
    {Base : Type uBase} {interpret : Base → Type uValue}
    {source target : List (Ty Base)} {bound result : Ty Base}
    (expression : Expr interpret source result)
    (substitution : Sub interpret source target) :
    (expression.rename (Ren.weaken : Ren source (bound :: source))).subst
        (Sub.lift substitution) =
      (expression.subst substitution).rename Ren.weaken := by
  induction expression with
  | var index => rfl
  | unit => rfl
  | bool value => rfl
  | constant value => rfl
  | pair left right ihLeft ihRight =>
      simp only [Expr.rename, subst, ihLeft, ihRight]
  | fst product ih => simp only [Expr.rename, subst, ih]
  | snd product ih => simp only [Expr.rename, subst, ih]
  | none => rfl
  | some value ih => simp only [Expr.rename, subst, ih]

end Expr

namespace Sub

@[simp] theorem lift_comp
    {Base : Type uBase} {interpret : Base → Type uValue}
    {source middle target : List (Ty Base)} {bound : Ty Base}
    (outer : Sub interpret middle target)
    (inner : Sub interpret source middle) :
    @lift Base interpret source target bound (comp outer inner) =
      @comp Base interpret (bound :: source) (bound :: middle) (bound :: target)
        (@lift Base interpret middle target bound outer)
        (@lift Base interpret source middle bound inner) := by
  apply ext
  intro value index
  cases index with
  | here => rfl
  | there index => exact (Expr.subst_lift_weaken (inner index) outer).symm

@[simp] theorem subst_var
    {Base : Type uBase} {interpret : Base → Type uValue}
    {source target : List (Ty Base)}
    (substitution : Sub interpret source target) :
    @comp Base interpret source source target substitution
      (id (interpret := interpret)) = @substitution := by
  apply ext
  intro value index
  exact Expr.subst_var index substitution

@[simp] theorem subst_id
    {Base : Type uBase} {interpret : Base → Type uValue}
    {source target : List (Ty Base)}
    (substitution : Sub interpret source target) :
    @comp Base interpret source target target
      (id (interpret := interpret)) substitution = @substitution := by
  apply ext
  intro value index
  exact Expr.subst_id (substitution index)

theorem subst_comp
    {Base : Type uBase} {interpret : Base → Type uValue}
    {first second third fourth : List (Ty Base)}
    (outer : Sub interpret third fourth)
    (middle : Sub interpret second third)
    (inner : Sub interpret first second) :
    @comp Base interpret first third fourth outer (comp middle inner) =
      @comp Base interpret first second fourth (comp outer middle) inner := by
  apply ext
  intro value index
  exact Expr.subst_comp (inner index) middle outer

end Sub

namespace Code

/-- Simultaneously substitute expressions for every free code variable. -/
def subst
    {Base : Type uBase} {interpret : Base → Type uValue}
    {S : Signature.{uBase, uOp} Base}
    {source target : List (Ty Base)} {result : Ty Base}
    (code : Code interpret S source result)
    (substitution : Sub interpret source target) :
    Code interpret S target result :=
  match code with
  | .ret value => .ret (value.subst substitution)
  | .letPure value next =>
      .letPure (value.subst substitution) (next.subst (Sub.lift substitution))
  | .call operation args next =>
      .call operation (args.subst substitution) (next.subst (Sub.lift substitution))
  | .branch condition thenCode elseCode =>
      .branch (condition.subst substitution)
        (thenCode.subst substitution) (elseCode.subst substitution)

@[simp] theorem subst_id
    {Base : Type uBase} {interpret : Base → Type uValue}
    {S : Signature.{uBase, uOp} Base}
    {context : List (Ty Base)} {result : Ty Base}
    (code : Code interpret S context result) :
    code.subst (Sub.id (interpret := interpret)) = code := by
  induction code <;> simp [Code.subst, *]

@[simp] theorem subst_comp
    {Base : Type uBase} {interpret : Base → Type uValue}
    {S : Signature.{uBase, uOp} Base}
    {source middle target : List (Ty Base)} {result : Ty Base}
    (code : Code interpret S source result)
    (inner : Sub interpret source middle)
    (outer : Sub interpret middle target) :
    (code.subst inner).subst outer =
      code.subst (Sub.comp outer inner) := by
  induction code generalizing middle target <;>
    simp [Code.subst, *, Sub.lift_comp]

theorem rename_eq_subst
    {Base : Type uBase} {interpret : Base → Type uValue}
    {S : Signature.{uBase, uOp} Base}
    {source target : List (Ty Base)} {result : Ty Base}
    (code : Code interpret S source result) (rename : Ren source target) :
    code.rename rename =
      code.subst (Sub.ofRen (interpret := interpret) rename) := by
  induction code generalizing target <;>
    simp [Code.rename, Code.subst, Expr.rename_eq_subst, *, Sub.lift_ofRen]

end Code

namespace Env

/--
Two environments are related by a substitution when evaluating every
substituted expression in the target recovers its source lookup.
-/
def SubRelated
    {Base : Type uBase} {interpret : Base → Type uValue}
    {source target : List (Ty Base)}
    (substitution : Sub interpret source target)
    (sourceEnv : Env interpret source) (targetEnv : Env interpret target) : Prop :=
  ∀ {value} (index : Var source value),
    (substitution index).eval targetEnv = sourceEnv.get index

theorem related_weaken
    {Base : Type uBase} {interpret : Base → Type uValue}
    {context : List (Ty Base)} {bound : Ty Base}
    (environment : Env interpret context)
    (value : Ty.denote interpret bound) :
    Related (Ren.weaken : Ren context (bound :: context))
      environment (.cons value environment) := by
  intro result index
  rfl

theorem subRelated_id
    {Base : Type uBase} {interpret : Base → Type uValue}
    {context : List (Ty Base)} (environment : Env interpret context) :
    SubRelated (Sub.id (interpret := interpret)) environment environment := by
  intro value index
  rfl

theorem subRelated_lift
    {Base : Type uBase} {interpret : Base → Type uValue}
    {source target : List (Ty Base)} {bound : Ty Base}
    {substitution : Sub interpret source target}
    {sourceEnv : Env interpret source} {targetEnv : Env interpret target}
    (related : SubRelated substitution sourceEnv targetEnv)
    (value : Ty.denote interpret bound) :
    SubRelated (Sub.lift substitution)
      (.cons value sourceEnv) (.cons value targetEnv) := by
  intro result index
  cases index with
  | here => rfl
  | there index =>
      change
        ((substitution index).rename Ren.weaken).eval
            (.cons value targetEnv) = sourceEnv.get index
      rw [Expr.eval_rename (related_weaken targetEnv value)]
      exact related index

theorem subRelated_single
    {Base : Type uBase} {interpret : Base → Type uValue}
    {context : List (Ty Base)} {head : Ty Base}
    (expression : Expr interpret context head)
    (environment : Env interpret context) :
    SubRelated (Sub.single expression)
      (.cons (expression.eval environment) .nil) environment := by
  intro result index
  cases index with
  | here => rfl
  | there index => cases index

end Env

namespace Expr

/-- Substitution preserves expression evaluation in related environments. -/
theorem eval_subst
    {Base : Type uBase} {interpret : Base → Type uValue}
    {source target : List (Ty Base)} {result : Ty Base}
    {substitution : Sub interpret source target}
    {sourceEnv : Env interpret source} {targetEnv : Env interpret target}
    (related : Env.SubRelated substitution sourceEnv targetEnv)
    (expression : Expr interpret source result) :
    (expression.subst substitution).eval targetEnv = expression.eval sourceEnv := by
  induction expression with
  | var index => exact related index
  | unit => rfl
  | bool value => rfl
  | constant value => rfl
  | pair left right ihLeft ihRight =>
      simp only [Expr.subst, eval, ihLeft, ihRight]
  | fst product ih => simp only [Expr.subst, eval, ih]
  | snd product ih => simp only [Expr.subst, eval, ih]
  | none => rfl
  | some value ih => simp only [Expr.subst, eval, ih]

end Expr

namespace Code

/-- Substitution preserves the complete exact execution distribution. -/
theorem runCosted_subst
    {M : CostModel.{uCost}}
    {Base : Type uBase} {interpret : Base → Type uValue}
    {S : Signature.{uBase, uOp} Base} (algebra : CostedAlgebra M interpret S)
    {source target : List (Ty Base)} {result : Ty Base}
    {substitution : Sub interpret source target}
    {sourceEnv : Env interpret source} {targetEnv : Env interpret target}
    (related : Env.SubRelated substitution sourceEnv targetEnv)
    (code : Code interpret S source result) :
    runCosted algebra (code.subst substitution) targetEnv =
      runCosted algebra code sourceEnv := by
  induction code generalizing target with
  | ret value => simp only [Code.subst, runCosted, value.eval_subst related]
  | letPure value next ih =>
      simp only [Code.subst, runCosted]
      rw [value.eval_subst related]
      exact ih (Env.subRelated_lift related (value.eval sourceEnv))
  | call operation args next ih =>
      simp only [Code.subst, runCosted]
      rw [args.eval_subst related]
      apply congrArg
        (RandCosted.bind (algebra.exec operation (args.eval sourceEnv)))
      funext value
      exact ih (Env.subRelated_lift related value)
  | branch condition thenCode elseCode ihThen ihElse =>
      simp only [Code.subst, runCosted, condition.eval_subst related]
      split
      · exact ihThen related
      · exact ihElse related

/-- Cost erasure of `runCosted_subst`. -/
theorem valueDist_subst
    {M : CostModel.{uCost}}
    {Base : Type uBase} {interpret : Base → Type uValue}
    {S : Signature.{uBase, uOp} Base} (algebra : CostedAlgebra M interpret S)
    {source target : List (Ty Base)} {result : Ty Base}
    {substitution : Sub interpret source target}
    {sourceEnv : Env interpret source} {targetEnv : Env interpret target}
    (related : Env.SubRelated substitution sourceEnv targetEnv)
    (code : Code interpret S source result) :
    valueDist algebra (code.subst substitution) targetEnv =
      valueDist algebra code sourceEnv := by
  simp only [valueDist, runCosted_subst algebra related code]

end Code

end CryptoLib.Program

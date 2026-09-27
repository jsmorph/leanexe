import LeanExe.Source.ScalarBooleanLocal
import LeanExe.Source.ScalarPublicArgument

namespace LeanExe.Source.Scalar

/-- Scalar lets, direct applications and standard Id binds share binding semantics. -/
inductive BooleanScopeBindingForm where
  | letE (nondep : Bool)
  | application (binder : Lean.BinderInfo)
  | monadic (binder : Lean.BinderInfo) (result : BooleanType)
  deriving Repr

namespace BooleanScopeBindingForm

def base : BooleanScopeBindingForm → BooleanBindingForm
  | .letE nondep => .letE nondep
  | .application binder => .application binder
  | .monadic binder result => .monadic binder result

def expr (form : BooleanScopeBindingForm) (name : Lean.Name)
    (domain value body : Lean.Expr) : Lean.Expr := form.base.expr name domain value body

theorem binding_size (form : BooleanScopeBindingForm) (name : Lean.Name)
    (domain value body : Lean.Expr) :
    sizeOf (.letE name domain value body form.base.nondep : Lean.Expr) ≤
      sizeOf (form.expr name domain value body) := form.base.binding_size name domain value body

/-- The direct lambda application evaluates the checked body at its argument. -/
theorem application_apply {α β : Type} (value : α) (body : α → β) :
    (fun input => body input) value = body value := rfl

/-- The standard Id bind used by the syntax renderer evaluates its continuation. -/
theorem monadic_apply {α β : Type} (value : Id α) (body : α → Id β) :
    (value >>= body) = body value := rfl

end BooleanScopeBindingForm

/-- Exact scalar binding syntax around an independently checked Boolean continuation. -/
structure BooleanScopeBinding (booleanInput : Bool) where
  name : Lean.Name
  domain : Lean.Expr
  input : PublicArgument.Domain (if booleanInput then .boolean else .word) domain
  value : Lean.Expr
  body : Lean.Expr
  form : BooleanScopeBindingForm
  extended : ∀ expression : BooleanLocal,
    form.expr name domain value body ≠ expression.expr
  deriving Repr

namespace BooleanScopeBinding

def expr (binding : BooleanScopeBinding booleanInput) : Lean.Expr :=
  binding.form.expr binding.name binding.domain binding.value binding.body

theorem value_size (binding : BooleanScopeBinding booleanInput) : sizeOf binding.value < sizeOf binding.expr := by
  have bound := binding.form.binding_size binding.name binding.domain binding.value binding.body
  simp only [expr]
  simp at bound
  omega

theorem body_size (binding : BooleanScopeBinding booleanInput) : sizeOf binding.body < sizeOf binding.expr := by
  have bound := binding.form.binding_size binding.name binding.domain binding.value binding.body
  simp only [expr]
  simp at bound
  omega

end BooleanScopeBinding
end LeanExe.Source.Scalar

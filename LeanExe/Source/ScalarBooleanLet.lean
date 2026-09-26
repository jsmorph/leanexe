import LeanExe.Source.ScalarBooleanType
import LeanExe.Source.ScalarDo

namespace LeanExe.Source.Scalar

/-- The source binder is retained while its value is supplied to the body. -/
inductive BooleanBindingForm where
  | letE (nondep : Bool)
  | application (binder : Lean.BinderInfo)
  deriving Repr

instance : Coe Bool BooleanBindingForm := ⟨BooleanBindingForm.letE⟩

def BooleanBindingForm.nondep : BooleanBindingForm → Bool
  | .letE nondep => nondep
  | .application _ => false

def BooleanBindingForm.expr (form : BooleanBindingForm) (name : Lean.Name)
    (type value body : Lean.Expr) : Lean.Expr :=
  match form with
  | .letE nondep => .letE name type value body nondep
  | .application binder => .app (.lam name type body binder) value

/-- Preserve a Boolean binding around a scalar operand from its body. -/
def booleanLetExpr (name : Lean.Name) (nondep : Bool) (value body : Lean.Expr)
    (type : BooleanType := .boolean) : Lean.Expr :=
  .letE name type.expr value body nondep

/-- Preserve a word binding around a scalar operand of a Boolean result. -/
def booleanWordLetExpr (name : Lean.Name) (nondep : Bool) (value body : Lean.Expr)
    (type : ResultType := .word) : Lean.Expr :=
  .letE name type.expr value body nondep

theorem BooleanType.base_size (type : BooleanType) :
    sizeOf (BooleanType.boolean.expr) ≤ sizeOf type.expr := by
  induction type with
  | boolean => exact Nat.le_refl _
  | identity inner ih => simp_all [BooleanType.expr] <;> omega

theorem ResultType.word_size (type : ResultType) :
    sizeOf (ResultType.word.expr) ≤ sizeOf type.expr := by
  induction type with
  | word => exact Nat.le_refl _
  | identity inner ih => simp_all [ResultType.expr] <;> omega

/-- External Boolean references after removing the innermost Boolean binding. -/
def booleanLetVariables (indices : List Nat) : List Nat :=
  indices.filterMap fun | 0 => none | index + 1 => some index

@[simp] theorem mem_booleanLetVariables (indices : List Nat) (index : Nat) :
    index ∈ booleanLetVariables indices ↔ index + 1 ∈ indices := by
  simp only [booleanLetVariables, List.mem_filterMap]
  constructor
  · rintro ⟨other, member, found⟩
    cases other with
    | zero => contradiction
    | succ other => cases found; exact member
  · intro member
    exact ⟨index + 1, member, rfl⟩

/-- The new flag occupies index zero; captured flags retain their outer meanings. -/
def booleanLetBooleans (value : Bool) (outer : Nat → Bool) : Nat → Bool
  | 0 => value
  | index + 1 => outer index

end LeanExe.Source.Scalar

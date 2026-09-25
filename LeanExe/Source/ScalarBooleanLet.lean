import LeanExe.Source.ScalarBooleanType
import LeanExe.Source.ScalarDo

namespace LeanExe.Source.Scalar

/-- Preserve a Boolean binding around a scalar operand from its body. -/
def booleanLetExpr (name : Lean.Name) (nondep : Bool) (value body : Lean.Expr)
    (type : BooleanType := .boolean) : Lean.Expr :=
  .letE name type.expr value body nondep

/-- Preserve a word binding around a scalar operand of a Boolean result. -/
def booleanWordLetExpr (name : Lean.Name) (nondep : Bool) (value body : Lean.Expr)
    (type : ResultType := .word) : Lean.Expr :=
  .letE name type.expr value body nondep

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

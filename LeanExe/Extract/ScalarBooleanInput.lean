import LeanExe.Extract.ScalarPredicateInput
import LeanExe.Source.ScalarBooleanInput

namespace LeanExe.Extract.Core
open LeanExe.Source.Scalar

/-- Remove one standard Id layer only when the arrow and lambda domains match. -/
def booleanInputTypes? (input domain : Lean.Expr) : Option BooleanType :=
  if input = domain then
    match input with
    | .app (.const ``Id [.zero]) inner => booleanType? inner
    | _ => none
  else none

@[simp] theorem booleanInputTypes_accepts (input : BooleanType) :
    booleanInputTypes? (BooleanType.identity input).expr (BooleanType.identity input).expr = some input := by
  simp [booleanInputTypes?, BooleanType.expr]

theorem booleanInputTypes_sound {input domain : Lean.Expr} {type : BooleanType}
    (found : booleanInputTypes? input domain = some type) :
    input = (BooleanType.identity type).expr ∧ domain = (BooleanType.identity type).expr := by
  unfold booleanInputTypes? at found
  split at found
  next same =>
    split at found
    next inner =>
      have equal := booleanType_sound found
      subst inner
      exact ⟨rfl, same.symm⟩
    next => contradiction
  next => contradiction

@[simp] theorem predicateInputTypes_boolean (input : BooleanType) (output : Lean.Expr) :
    predicateInputTypes? input.expr input.expr output = none := by
  cases input with
  | boolean => rfl
  | identity inner => simp [predicateInputTypes?, BooleanType.expr, scalarResultType_boolean]

end LeanExe.Extract.Core

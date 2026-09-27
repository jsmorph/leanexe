import LeanExe.Source.ScalarBooleanHelper
import LeanExe.Extract.ScalarBooleanLocalSyntax

namespace LeanExe.Extract.Core
open LeanExe.Source.Scalar

/-- A failed existing Boolean parse gives a syntactic, parser-independent exclusion. -/
theorem booleanLocal_excluded {source : Lean.Expr} (absent : booleanLocalOperands? source = none) :
    ∀ expression : BooleanLocal, source ≠ expression.expr := by
  intro expression same
  rw [same, booleanLocalOperands_expr] at absent
  contradiction

@[simp] theorem booleanHelper_not_local (helper : BooleanHelper booleanInput) :
    booleanLocalOperands? helper.expr = none := by
  cases found : booleanLocalOperands? helper.expr with
  | none => rfl
  | some expression => exact False.elim (helper.extended expression (booleanLocalOperands_sound found))

/-- Check a predicate declaration and retain the entire Boolean continuation. -/
def booleanHelper? (booleanInput : Bool) (source : Lean.Expr) : Option (BooleanHelper booleanInput) :=
  if absent : booleanLocalOperands? source = none then
    match same : source with
    | .letE functionName (.forallE typeName input result typeInfo)
        (.lam parameterName domain body valueInfo) continuation nondep =>
        if inputs : input = .const (if booleanInput then ``Bool else ``UInt64) [] ∧ domain = input then
          match resultFound : booleanType? result with
          | some resultType =>
              let shape : BooleanFunctionBinding := ⟨functionName, typeName, typeInfo, valueInfo, resultType, nondep⟩
              have exactSource : source = booleanHelperExpr booleanInput shape parameterName body continuation := by
                rw [same, inputs.2, inputs.1, booleanType_sound resultFound]
                rfl
              some ⟨shape, parameterName, body, continuation,
                fun value equal => booleanLocal_excluded absent value (same.symm.trans (exactSource.trans equal))⟩
          | none => none
        else none
    | _ => none
  else none

@[simp] theorem booleanHelper_accepts (value : BooleanHelper booleanInput) :
    booleanHelper? booleanInput value.expr = some value := by
  have absent := booleanHelper_not_local value
  rcases value with ⟨shape, parameterName, body, continuation, extended⟩
  simp [booleanHelper?, BooleanHelper.expr, booleanHelperExpr] at absent ⊢
  simp [absent]
  split <;> simp_all
  simp_all only [booleanType_accepts, Option.some.injEq]
  cases shape
  simp_all

@[simp] theorem booleanHelper_other (value : BooleanHelper booleanInput) :
    booleanHelper? (!booleanInput) value.expr = none := by
  have absent := booleanHelper_not_local value
  cases booleanInput <;> simp [booleanHelper?, BooleanHelper.expr, booleanHelperExpr] at absent ⊢
  all_goals simp [absent]

theorem booleanHelper_sound {source : Lean.Expr} {value : BooleanHelper booleanInput}
    (parsed : booleanHelper? booleanInput source = some value) : source = value.expr := by
  cases booleanInput <;> unfold booleanHelper? at parsed
  all_goals simp only [Bool.false_eq_true, ite_false, ite_true] at parsed
  all_goals split at parsed <;> try contradiction
  all_goals split at parsed <;> try contradiction
  all_goals split at parsed <;> try contradiction
  all_goals rename_i inputs
  all_goals split at parsed <;> try contradiction
  all_goals rename_i resultType resultFound
  all_goals cases parsed
  all_goals simp only [BooleanHelper.expr, booleanHelperExpr, Bool.false_eq_true, ite_false, ite_true]
  all_goals rw [inputs.2, inputs.1, booleanType_sound resultFound]

theorem booleanHelper_sizes {source : Lean.Expr} {value : BooleanHelper booleanInput}
    (parsed : booleanHelper? booleanInput source = some value) :
    sizeOf value.body < sizeOf source ∧ sizeOf value.continuation < sizeOf source := by
  rw [booleanHelper_sound parsed]
  exact ⟨value.body_size, value.continuation_size⟩

end LeanExe.Extract.Core

import LeanExe.Source.ScalarBooleanBinaryHelper
import LeanExe.Extract.ScalarBooleanScopeBinding

namespace LeanExe.Extract.Core
open LeanExe.Source.Scalar

@[simp] theorem booleanBinaryHelper_not_local (helper : BooleanBinaryHelper) :
    booleanLocalOperands? helper.expr = none := by
  cases found : booleanLocalOperands? helper.expr with
  | none => rfl
  | some expression => exact False.elim (helper.extended expression (booleanLocalOperands_sound found))

def booleanBinaryHelper? (source : Lean.Expr) : Option BooleanBinaryHelper :=
  if absent : booleanLocalOperands? source = none then
    match same : source with
    | .letE name (.forallE firstType (.const ``UInt64 [])
        (.forallE secondType (.const ``UInt64 []) result secondTypeInfo) firstTypeInfo)
        (.lam firstValue (.const ``UInt64 [])
          (.lam secondValue (.const ``UInt64 []) body secondValueInfo) firstValueInfo) continuation nondep =>
        match resultFound : booleanType? result with
        | none => none
        | some annotation =>
            let shape : BooleanBinaryFunctionBinding := ⟨name,
              ⟨firstType, firstValue, firstTypeInfo, firstValueInfo⟩,
              ⟨secondType, secondValue, secondTypeInfo, secondValueInfo⟩, annotation, nondep⟩
            have exactSource : source = shape.expr body continuation := by
              rw [same, booleanType_sound resultFound]
              rfl
            some ⟨shape, body, continuation,
              fun expression equal => booleanLocal_excluded absent expression
                (same.symm.trans (exactSource.trans equal))⟩
    | _ => none
  else none

@[simp] theorem booleanBinaryHelper_accepts (helper : BooleanBinaryHelper) :
    booleanBinaryHelper? helper.expr = some helper := by
  have absent := booleanBinaryHelper_not_local helper
  rcases helper with ⟨shape, body, continuation, extended⟩
  simp [booleanBinaryHelper?, BooleanBinaryHelper.expr, BooleanBinaryFunctionBinding.expr,
    Parameter.arrow, Parameter.lambda] at absent ⊢
  simp [absent]
  split <;> simp_all
  simp_all only [booleanType_accepts, Option.some.injEq]
  cases shape
  simp_all

theorem booleanBinaryHelper_sound {source : Lean.Expr} {helper : BooleanBinaryHelper}
    (parsed : booleanBinaryHelper? source = some helper) : source = helper.expr := by
  unfold booleanBinaryHelper? at parsed
  split at parsed <;> try contradiction
  split at parsed <;> try contradiction
  split at parsed <;> try contradiction
  rename_i annotation found
  cases parsed
  simp only [BooleanBinaryHelper.expr, BooleanBinaryFunctionBinding.expr, Parameter.arrow, Parameter.lambda]
  rw [booleanType_sound found]

theorem booleanBinaryHelper_sizes {source : Lean.Expr} {helper : BooleanBinaryHelper}
    (parsed : booleanBinaryHelper? source = some helper) :
    sizeOf helper.body < sizeOf source ∧ sizeOf helper.continuation < sizeOf source := by
  rw [booleanBinaryHelper_sound parsed]
  exact ⟨helper.body_size, helper.continuation_size⟩

def booleanBinaryCall? : Lean.Expr → Option BooleanBinaryCall
  | .app (.app (.bvar index) first) second => some ⟨index, first, second⟩
  | _ => none

@[simp] theorem booleanBinaryCall_accepts (call : BooleanBinaryCall) :
    booleanBinaryCall? call.expr = some call := by cases call; rfl

theorem booleanBinaryCall_sound {source : Lean.Expr} {call : BooleanBinaryCall}
    (parsed : booleanBinaryCall? source = some call) : source = call.expr := by
  unfold booleanBinaryCall? at parsed
  split at parsed <;> try contradiction
  cases parsed
  rfl

theorem booleanBinaryCall_sizes {source : Lean.Expr} {call : BooleanBinaryCall}
    (parsed : booleanBinaryCall? source = some call) :
    sizeOf call.first < sizeOf source ∧ sizeOf call.second < sizeOf source := by
  rw [booleanBinaryCall_sound parsed]
  exact ⟨call.first_size, call.second_size⟩

end LeanExe.Extract.Core

import LeanExe.Source.ScalarManyFunction
import LeanExe.Extract.ScalarFunctionSuffix

namespace LeanExe.Extract.Core

open LeanExe.Source.Scalar (FunctionSuffix Parameter ManyFunction)

theorem scalarFunctionSuffix_not_result (suffix : FunctionSuffix) (positive : 0 < suffix.arity) :
    scalarResultType? suffix.type = none := by
  cases suffix with
  | result => simp [FunctionSuffix.arity] at positive
  | argument => rfl

/-- Recognize the checked three-or-more-argument scalar helper shape. -/
def scalarManyFunction? : Lean.Expr → Lean.Expr → Option ManyFunction
  | .forallE firstTypeName (.const ``UInt64 [])
      (.forallE secondTypeName (.const ``UInt64 []) restType secondTypeBi) firstTypeBi,
      .lam firstValueName (.const ``UInt64 [])
        (.lam secondValueName (.const ``UInt64 []) restValue secondValueBi) firstValueBi => do
      let suffix ← scalarFunctionSuffix? restType restValue
      if positive : 0 < suffix.arity then
        some { first := ⟨firstTypeName, firstValueName, firstTypeBi, firstValueBi⟩
               second := ⟨secondTypeName, secondValueName, secondTypeBi, secondValueBi⟩
               suffix, positive }
      else none
  | _, _ => none

@[simp] theorem scalarManyFunction_accepts (function : ManyFunction) :
    scalarManyFunction? function.type function.value = some function := by
  cases function
  simp [ManyFunction.type, ManyFunction.value, Parameter.arrow, Parameter.lambda,
    scalarManyFunction?, scalarFunctionSuffix_accepts, *]

theorem scalarManyFunction_sound {type value : Lean.Expr} {function : ManyFunction}
    (parsed : scalarManyFunction? type value = some function) :
    type = function.type ∧ value = function.value := by
  unfold scalarManyFunction? at parsed
  split at parsed
  · simp only [bind, Option.bind_eq_some_iff] at parsed
    obtain ⟨suffix, found, accepted⟩ := parsed
    split at accepted
    · cases accepted
      obtain ⟨sameType, sameValue⟩ := scalarFunctionSuffix_sound found
      simp [ManyFunction.type, ManyFunction.value, Parameter.arrow, Parameter.lambda,
        sameType, sameValue]
    · contradiction
  · contradiction

theorem scalarManyFunction_body_size {type value : Lean.Expr} {function : ManyFunction}
    (parsed : scalarManyFunction? type value = some function) :
    sizeOf function.body < sizeOf value := by
  rw [(scalarManyFunction_sound parsed).2]
  exact function.body_size

end LeanExe.Extract.Core

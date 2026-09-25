import LeanExe.Source.ScalarManyFunction
import LeanExe.Extract.ScalarFunctionSuffix

namespace LeanExe.Extract.Core

open LeanExe.Source.Scalar (FunctionSuffix Parameter ManyFunction ResultType)

theorem scalarFunctionSuffix_not_result (suffix : FunctionSuffix) (positive : 0 < suffix.arity)
    (render : ResultType → Lean.Expr := ResultType.expr) :
    scalarResultType? (suffix.type render) = none := by
  cases suffix with
  | result => simp [FunctionSuffix.arity] at positive
  | argument => rfl

/-- Three-or-more-argument helpers share the same paired-parameter parser,
with a separate terminal result parser for each supported result kind. -/
def manyFunction? (parseResult : Lean.Expr → Option ResultType) : Lean.Expr → Lean.Expr → Option ManyFunction
  | .forallE firstTypeName (.const ``UInt64 [])
      (.forallE secondTypeName (.const ``UInt64 []) restType secondTypeBi) firstTypeBi,
      .lam firstValueName (.const ``UInt64 [])
        (.lam secondValueName (.const ``UInt64 []) restValue secondValueBi) firstValueBi => do
      let suffix ← functionSuffix? parseResult restType restValue
      if positive : 0 < suffix.arity then
        some { first := ⟨firstTypeName, firstValueName, firstTypeBi, firstValueBi⟩
               second := ⟨secondTypeName, secondValueName, secondTypeBi, secondValueBi⟩
               suffix, positive }
      else none
  | _, _ => none

theorem manyFunction_accepts (parseResult : Lean.Expr → Option ResultType)
    (render : ResultType → Lean.Expr)
    (accepted : ∀ annotation, parseResult (render annotation) = some annotation)
    (notArrow : ∀ annotation name rest bi,
      render annotation ≠ .forallE name (.const ``UInt64 []) rest bi)
    (function : ManyFunction) :
    manyFunction? parseResult (function.type render) function.value = some function := by
  cases function
  simp [ManyFunction.type, ManyFunction.value, Parameter.arrow, Parameter.lambda,
    manyFunction?, functionSuffix_accepts parseResult render accepted notArrow, *]

theorem manyFunction_sound (parseResult : Lean.Expr → Option ResultType)
    (render : ResultType → Lean.Expr)
    (sound : ∀ type annotation, parseResult type = some annotation → type = render annotation)
    {type value : Lean.Expr} {function : ManyFunction}
    (parsed : manyFunction? parseResult type value = some function) :
    type = function.type render ∧ value = function.value := by
  unfold manyFunction? at parsed
  split at parsed
  · simp only [bind, Option.bind_eq_some_iff] at parsed
    obtain ⟨suffix, found, accepted⟩ := parsed
    split at accepted
    · cases accepted
      obtain ⟨sameType, sameValue⟩ := functionSuffix_sound parseResult render sound found
      simp [ManyFunction.type, ManyFunction.value, Parameter.arrow, Parameter.lambda,
        sameType, sameValue]
    · contradiction
  · contradiction

abbrev scalarManyFunction? := manyFunction? scalarResultType?

@[simp] theorem scalarManyFunction_accepts (function : ManyFunction) :
    scalarManyFunction? function.type function.value = some function :=
  manyFunction_accepts _ _ scalarResultType_accepts
    (by intro annotation name rest bi; cases annotation <;> simp [ResultType.expr]) function

theorem scalarManyFunction_sound {type value : Lean.Expr} {function : ManyFunction}
    (parsed : scalarManyFunction? type value = some function) :
    type = function.type ∧ value = function.value :=
  manyFunction_sound _ _ (fun _ _ => scalarResultType_sound) parsed

theorem scalarManyFunction_body_size {type value : Lean.Expr} {function : ManyFunction}
    (parsed : scalarManyFunction? type value = some function) :
    sizeOf function.body < sizeOf value := by
  rw [(scalarManyFunction_sound parsed).2]
  exact function.body_size

end LeanExe.Extract.Core

import LeanExe.Source.ScalarFunctionSuffix
import LeanExe.Extract.ScalarDo

namespace LeanExe.Extract.Core

open LeanExe.Source.Scalar (FunctionSuffix Parameter)

/-- Check each concrete type/lambda parameter pair before checking the scalar
result annotation. No reduction or guessed parameter count is involved. -/
def scalarFunctionSuffix? : Lean.Expr → Lean.Expr → Option FunctionSuffix
  | .forallE typeName (.const ``UInt64 []) restType typeBi,
      .lam valueName (.const ``UInt64 []) restValue valueBi =>
      (scalarFunctionSuffix? restType restValue).map
        (.argument { typeName, valueName, typeBi, valueBi })
  | type, value => (scalarResultType? type).map fun annotation => .result annotation value

@[simp] theorem scalarFunctionSuffix_accepts (suffix : FunctionSuffix) :
    scalarFunctionSuffix? suffix.type suffix.value = some suffix := by
  induction suffix with
  | result annotation body =>
    cases annotation <;> simp [FunctionSuffix.type, FunctionSuffix.value,
      LeanExe.Source.Scalar.ResultType.expr, scalarFunctionSuffix?, scalarResultType?]
  | argument parameter rest ih =>
    simp [FunctionSuffix.type, FunctionSuffix.value, Parameter.arrow, Parameter.lambda,
      scalarFunctionSuffix?, ih]

theorem scalarFunctionSuffix_sound {type value : Lean.Expr} {suffix : FunctionSuffix}
    (parsed : scalarFunctionSuffix? type value = some suffix) :
    type = suffix.type ∧ value = suffix.value := by
  induction type, value using scalarFunctionSuffix?.induct generalizing suffix with
  | case1 typeName restType typeBi valueName restValue valueBi ih =>
    rw [scalarFunctionSuffix?] at parsed
    obtain ⟨rest, found, rfl⟩ := Option.map_eq_some_iff.mp parsed
    obtain ⟨sameType, sameValue⟩ := ih found
    simp [FunctionSuffix.type, FunctionSuffix.value, Parameter.arrow, Parameter.lambda,
      sameType, sameValue]
  | case2 type value excluded =>
    rw [scalarFunctionSuffix?] at parsed
    · obtain ⟨annotation, found, rfl⟩ := Option.map_eq_some_iff.mp parsed
      exact ⟨scalarResultType_sound found, rfl⟩
    · exact excluded

end LeanExe.Extract.Core

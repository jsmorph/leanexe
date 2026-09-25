import LeanExe.Source.ScalarFunctionSuffix
import LeanExe.Extract.ScalarDo

namespace LeanExe.Extract.Core

open LeanExe.Source.Scalar (FunctionSuffix Parameter ResultType)

/-- Parameter parsing is shared by scalar and complete-step helpers. Only the
terminal result parser differs; every concrete type/lambda pair is checked. -/
def functionSuffix? (parseResult : Lean.Expr → Option ResultType) : Lean.Expr → Lean.Expr → Option FunctionSuffix
  | .forallE typeName (.const ``UInt64 []) restType typeBi,
      .lam valueName (.const ``UInt64 []) restValue valueBi =>
      (functionSuffix? parseResult restType restValue).map
        (.argument { typeName, valueName, typeBi, valueBi })
  | type, value => (parseResult type).map fun annotation => .result annotation value

theorem functionSuffix_accepts (parseResult : Lean.Expr → Option ResultType)
    (render : ResultType → Lean.Expr)
    (accepted : ∀ annotation, parseResult (render annotation) = some annotation)
    (notArrow : ∀ annotation name rest bi,
      render annotation ≠ .forallE name (.const ``UInt64 []) rest bi)
    (suffix : FunctionSuffix) :
    functionSuffix? parseResult (suffix.type render) suffix.value = some suffix := by
  induction suffix with
  | result annotation body =>
    simp only [FunctionSuffix.type, FunctionSuffix.value]
    rw [functionSuffix?]
    · simp [accepted]
    · intro name rest bi valueName value valueBi same _
      exact notArrow annotation name rest bi same
  | argument parameter rest ih =>
    simp [FunctionSuffix.type, FunctionSuffix.value, Parameter.arrow, Parameter.lambda,
      functionSuffix?, ih]

theorem functionSuffix_sound (parseResult : Lean.Expr → Option ResultType)
    (render : ResultType → Lean.Expr)
    (sound : ∀ type annotation, parseResult type = some annotation → type = render annotation)
    {type value : Lean.Expr} {suffix : FunctionSuffix}
    (parsed : functionSuffix? parseResult type value = some suffix) :
    type = suffix.type render ∧ value = suffix.value := by
  induction type, value using functionSuffix?.induct generalizing suffix with
  | case1 typeName restType typeBi valueName restValue valueBi ih =>
    rw [functionSuffix?] at parsed
    obtain ⟨rest, found, rfl⟩ := Option.map_eq_some_iff.mp parsed
    obtain ⟨sameType, sameValue⟩ := ih found
    simp [FunctionSuffix.type, FunctionSuffix.value, Parameter.arrow, Parameter.lambda,
      sameType, sameValue]
  | case2 type value excluded =>
    rw [functionSuffix?] at parsed
    · obtain ⟨annotation, found, rfl⟩ := Option.map_eq_some_iff.mp parsed
      exact ⟨sound _ _ found, rfl⟩
    · exact excluded

abbrev scalarFunctionSuffix? := functionSuffix? scalarResultType?

@[simp] theorem scalarFunctionSuffix_accepts (suffix : FunctionSuffix) :
    scalarFunctionSuffix? suffix.type suffix.value = some suffix :=
  functionSuffix_accepts _ _ scalarResultType_accepts
    (by intro annotation name rest bi; cases annotation <;> simp [ResultType.expr]) suffix

theorem scalarFunctionSuffix_sound {type value : Lean.Expr} {suffix : FunctionSuffix}
    (parsed : scalarFunctionSuffix? type value = some suffix) :
    type = suffix.type ∧ value = suffix.value :=
  functionSuffix_sound _ _ (fun _ _ => scalarResultType_sound) parsed

end LeanExe.Extract.Core

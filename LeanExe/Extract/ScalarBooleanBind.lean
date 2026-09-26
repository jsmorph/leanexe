import LeanExe.Extract.ScalarBooleanAction
import LeanExe.Extract.ScalarDo

namespace LeanExe.Extract.Core
open LeanExe.Source.Scalar

/-- Boolean input and lambda-domain annotations must agree exactly. The caller
supplies the existing scalar or step result-annotation parser. -/
def booleanBindType? (parseResult : Lean.Expr → Option ResultType)
    (input domain output : Lean.Expr) : Option ResultType :=
  match input, domain with
  | .const ``Bool [], .const ``Bool [] => parseResult output
  | _, _ => none

theorem booleanBindType_accepts (parseResult : Lean.Expr → Option ResultType)
    {sourceType : Lean.Expr} {type : ResultType} (accepted : parseResult sourceType = some type) :
    booleanBindType? parseResult (.const ``Bool []) (.const ``Bool []) sourceType = some type := accepted

theorem booleanBindType_sound (parseResult : Lean.Expr → Option ResultType)
    {input domain output : Lean.Expr} {type : ResultType}
    (parsed : booleanBindType? parseResult input domain output = some type) :
    input = .const ``Bool [] ∧ domain = .const ``Bool [] ∧ parseResult output = some type := by
  unfold booleanBindType? at parsed
  split at parsed
  · exact ⟨rfl, rfl, parsed⟩
  · contradiction

@[simp] theorem booleanBindType_not_scalar (output : Lean.Expr) :
    scalarBindTypes? (.const ``Bool []) (.const ``Bool []) output = none := rfl

end LeanExe.Extract.Core

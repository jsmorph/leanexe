import LeanExe.Extract.ScalarBooleanLetTypes
import LeanExe.Source.ScalarGuardLet

namespace LeanExe.Extract.Core
open LeanExe.Source.Scalar

def guardLetType? (type : Lean.Expr) : Option GuardLetType :=
  match scalarResultType? type with
  | some result => some (.word result)
  | none => (booleanType? type).map GuardLetType.boolean

@[simp] theorem guardLetType_accepts (type : GuardLetType) :
    guardLetType? type.expr = some type := by
  cases type <;> simp [guardLetType?, GuardLetType.expr, scalarResultType_boolean]

theorem guardLetType_sound {type : Lean.Expr} {result : GuardLetType}
    (found : guardLetType? type = some result) : type = result.expr := by
  unfold guardLetType? at found
  split at found
  · rename_i result parsed
    cases found
    exact scalarResultType_sound parsed
  · obtain ⟨result, parsed, rfl⟩ := Option.map_eq_some_iff.mp found
    exact booleanType_sound parsed

end LeanExe.Extract.Core

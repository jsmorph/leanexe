import LeanExe.Source.ScalarBooleanType

namespace LeanExe.Extract.Core
open LeanExe.Source.Scalar

def booleanType? : Lean.Expr → Option BooleanType
  | .const ``Bool [] => some .boolean
  | .app (.const ``Id [.zero]) inner => (booleanType? inner).map BooleanType.identity
  | _ => none

@[simp] theorem booleanType_accepts (type : BooleanType) : booleanType? type.expr = some type := by
  induction type with
  | boolean => rfl
  | identity inner ih => simp [BooleanType.expr, booleanType?, ih]

theorem booleanType_sound {source : Lean.Expr} {type : BooleanType}
    (parsed : booleanType? source = some type) : source = type.expr := by
  induction source using booleanType?.induct generalizing type with
  | case1 => cases parsed; rfl
  | case2 inner ih =>
    rw [booleanType?] at parsed
    obtain ⟨type, found, rfl⟩ := Option.map_eq_some_iff.mp parsed
    simp [BooleanType.expr, ih found]
  | case3 source noBool noId => rw [booleanType?] at parsed <;> first | assumption | contradiction

end LeanExe.Extract.Core

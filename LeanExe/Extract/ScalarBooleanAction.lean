import LeanExe.Source.ScalarBooleanAction
import LeanExe.Extract.ScalarBooleanLocalSyntax

namespace LeanExe.Extract.Core
open LeanExe.Source.Scalar

/-- Actions and nested values use the same exact Boolean syntax parser. -/
def booleanAction? (source : Lean.Expr) : Option BooleanAction :=
  (booleanLocalOperands? source).map BooleanAction.value

theorem booleanAction_accepts (action : BooleanAction) : booleanAction? action.expr = some action := by
  cases action with
  | value expression => simp [booleanAction?, BooleanAction.expr, BooleanAction.leaf]

theorem booleanAction_sound {source : Lean.Expr} {action : BooleanAction}
    (parsed : booleanAction? source = some action) : source = action.expr := by
  obtain ⟨value, found, rfl⟩ := Option.map_eq_some_iff.mp parsed
  exact booleanLocalOperands_sound found

theorem booleanAction_size {source : Lean.Expr} {action : BooleanAction}
    (parsed : booleanAction? source = some action) {operand : Lean.Expr}
    (member : operand ∈ action.leaf.operands) : sizeOf operand < sizeOf source := by
  rw [booleanAction_sound parsed]
  exact action.operands_size member

end LeanExe.Extract.Core

import LeanExe.Source.ScalarDo

namespace LeanExe.Extract.Core

open LeanExe.Source.Scalar (ResultType)

def scalarResultType? : Lean.Expr → Option ResultType
  | .const ``UInt64 [] => some .word
  | .app (.const ``Id [.zero]) (.const ``UInt64 []) => some .identity
  | _ => none

@[simp] theorem scalarResultType_accepts (type : ResultType) :
    scalarResultType? type.expr = some type := by cases type <;> rfl

theorem scalarResultType_sound {source : Lean.Expr} {type : ResultType}
    (matched : scalarResultType? source = some type) : source = type.expr := by
  unfold scalarResultType? at matched
  split at matched <;> cases matched <;> rfl

end LeanExe.Extract.Core

import LeanExe.Extract.ScalarDo
import LeanExe.Source.ScalarStepSyntax

namespace LeanExe.Extract.Core

def scalarStepResultType? : Lean.Expr → Option LeanExe.Source.Scalar.ResultType
  | .app (.const ``ForInStep [.zero]) (.const ``UInt64 []) => some .word
  | .app (.const ``Id [.zero]) (.app (.const ``ForInStep [.zero]) (.const ``UInt64 [])) => some .identity
  | _ => none

theorem scalarStepResultType_accepts (type : LeanExe.Source.Scalar.ResultType) :
    scalarStepResultType? (LeanExe.Source.Scalar.Step.resultType type) = some type := by cases type <;> rfl

theorem scalarStepResultType_sound {source : Lean.Expr} {type : LeanExe.Source.Scalar.ResultType}
    (matched : scalarStepResultType? source = some type) : source = LeanExe.Source.Scalar.Step.resultType type := by
  unfold scalarStepResultType? at matched
  split at matched <;> cases matched <;> rfl

theorem scalarStepResultType_not_scalar (type : LeanExe.Source.Scalar.ResultType) :
    scalarStepResultType? type.expr = none := by cases type <;> rfl

theorem scalarResultType_not_step (type : LeanExe.Source.Scalar.ResultType) :
    scalarResultType? (LeanExe.Source.Scalar.Step.resultType type) = none := by cases type <;> rfl

end LeanExe.Extract.Core

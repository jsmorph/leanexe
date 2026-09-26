import LeanExe.Extract.ScalarDo
import LeanExe.Source.ScalarStepSyntax

namespace LeanExe.Extract.Core
open LeanExe.Source.Scalar.Step

def scalarStepResultType? : Lean.Expr → Option ResultAnnotation
  | .app (.const ``ForInStep [.zero]) (.const ``UInt64 []) => some .word
  | .app (.const ``Id [.zero]) inner => (scalarStepResultType? inner).map LeanExe.Source.Scalar.ResultType.identity
  | _ => none

theorem scalarStepResultType_accepts (type : ResultAnnotation) :
    scalarStepResultType? (resultType type) = some type := by
  induction type with
  | word => rfl
  | identity inner ih => simp [resultType, scalarStepResultType?, ih]

theorem scalarStepResultType_sound {source : Lean.Expr} {type : ResultAnnotation}
    (matched : scalarStepResultType? source = some type) : source = resultType type := by
  induction source using scalarStepResultType?.induct generalizing type with
  | case1 => cases matched; rfl
  | case2 inner ih =>
    rw [scalarStepResultType?] at matched
    obtain ⟨type, found, rfl⟩ := Option.map_eq_some_iff.mp matched
    simp [resultType, ih found]
  | case3 source h1 h2 => rw [scalarStepResultType?] at matched <;> first | assumption | contradiction

theorem scalarStepResultType_not_scalar (type : LeanExe.Source.Scalar.ResultType) :
    scalarStepResultType? type.expr = none := by
  induction type with
  | word => rfl
  | identity inner ih => simp [LeanExe.Source.Scalar.ResultType.expr, scalarStepResultType?, ih]

theorem scalarResultType_not_step (type : ResultAnnotation) : scalarResultType? (resultType type) = none := by
  induction type with
  | word => rfl
  | identity inner ih => simp [resultType, scalarResultType?, ih]

end LeanExe.Extract.Core

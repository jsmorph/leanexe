import LeanExe.Source.Scalar

namespace LeanExe.Source.Scalar

set_option linter.unusedSimpArgs false in
theorem EvalWith.booleanConversion_result {argument : Lean.Expr} {values : List Value}
    {value : UInt64} (evaluation : EvalWith (.app (.const ``Bool.toUInt64 []) argument) values value) :
    ∃ flag : Bool, value = flag.toUInt64 := by
  generalize expressionEq : Lean.Expr.app (.const ``Bool.toUInt64 []) argument = expression at evaluation
  cases evaluation with
  | booleanWord => exact ⟨_, rfl⟩
  | applyBooleanPredicateWord => exact ⟨_, rfl⟩
  | complement head _ => cases head <;> simp_all
  | extremum op _ _ => cases op <;> simp_all [Extremum.expr, Extremum.head]
  | manyApply call _ _ =>
    have root := congrArg Lean.Expr.getAppFn expressionEq
    simp [ManyCall.expr, ManyCall.index, Lean.Expr.getAppFn] at root
  | range =>
    have root := congrArg Lean.Expr.getAppFn expressionEq
    change Lean.Expr.const ``Bool.toUInt64 [] = .const ``ForIn.forIn [.zero, .zero, .zero, .zero] at root
    simp at root
  | _ =>
    simp_all [literalExpr, typedLiteralExpr, Comparison.branch, CompoundGuard.branch,
      DecidedGuard.dependentBranch, BooleanIdentity.bind, BooleanLocalGuard.branch,
      BooleanLocalGuard.dependentBranch, Identity.run, Identity.pure, Identity.bind,
      UnitSyntax.value, Extremum.expr, ManyFunction.bind, Range.call, Range.head,
      idLetExpr, predicateInputExpr]

end LeanExe.Source.Scalar

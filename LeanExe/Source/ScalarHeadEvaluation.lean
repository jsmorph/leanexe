import LeanExe.Source.Scalar

namespace LeanExe.Source.Scalar

/-- Exact arithmetic heads have one native meaning. -/
theorem Head.same_meaning {firstHead secondHead : Lean.Expr} {f g : UInt64 → UInt64 → UInt64}
    (first : Head firstHead f) (second : Head secondHead g) (same : firstHead = secondHead) : f = g := by
  cases first with
  | direct operation =>
    cases second with
    | direct other => cases operation <;> cases other <;> simp_all
    | canonical other => simp [classHead] at same
  | canonical operation result left right instanceType =>
    cases second with
    | direct other => simp [classHead] at same
    | canonical other => cases operation <;> cases other <;> simp_all [classHead]

@[simp] theorem LocalCall.expr_root (call : LocalCall) : call.expr.getAppFn = .bvar call.index := by
  induction call <;> simp_all [LocalCall.expr, LocalCall.index, Lean.Expr.getAppFn]

@[simp] theorem ManyCall.expr_root (call : ManyCall) : call.expr.getAppFn = .bvar call.index := by
  simp [ManyCall.index, Lean.Expr.getAppFn]

set_option linter.unusedSimpArgs false in
/-- Evaluation of a standard arithmetic application evaluates its two operands
and applies the operation named by the source head. -/
theorem EvalWith.binary_inv {head a b : Lean.Expr} {values : List Value}
    {f : UInt64 → UInt64 → UInt64} {value : UInt64}
    (meaning : Head head f)
    (evaluation : EvalWith (.app (.app head a) b) values value) :
    ∃ x y, EvalWith a values x ∧ EvalWith b values y ∧ value = f x y := by
  generalize expressionEq : Lean.Expr.app (.app head a) b = expression at evaluation
  cases evaluation with
  | binary other left right =>
    simp only [Lean.Expr.app.injEq] at expressionEq
    obtain ⟨⟨same, rfl⟩, rfl⟩ := expressionEq
    exact ⟨_, _, left, right, by rw [Head.same_meaning meaning other same]⟩
  | complement complement argument =>
    cases complement <;> cases meaning with
    | direct operation => cases operation <;> simp_all [classHead, Lean.Expr.getAppFn, Extremum.expr, Extremum.head]
    | canonical operation result left right instanceType =>
      cases operation <;> simp_all [classHead, Lean.Expr.getAppFn, Extremum.expr, Extremum.head]
  | extremum op left right =>
    cases op <;> cases meaning with
    | direct operation => cases operation <;> simp_all [classHead, Lean.Expr.getAppFn, Extremum.expr, Extremum.head]
    | canonical operation result left right instanceType =>
      cases operation <;> simp_all [classHead, Lean.Expr.getAppFn, Extremum.expr, Extremum.head]
  | manyApply call function arguments =>
    have root := congrArg Lean.Expr.getAppFn expressionEq
    rw [ManyCall.expr_root] at root
    cases meaning with
    | direct operation => cases operation <;> simp [Lean.Expr.getAppFn] at root
    | canonical operation result left right instanceType =>
      cases operation <;> simp [classHead, Lean.Expr.getAppFn] at root
  | range countValue initialValue yielding steps =>
    have root := congrArg Lean.Expr.getAppFn expressionEq
    change head.getAppFn = .const ``ForIn.forIn [.zero, .zero, .zero, .zero] at root
    cases meaning with
    | direct operation => cases operation <;> simp_all [classHead, Lean.Expr.getAppFn, Extremum.expr, Extremum.head]
    | canonical operation result left right instanceType =>
      cases operation <;> simp_all [classHead, Lean.Expr.getAppFn, Extremum.expr, Extremum.head]
  | _ =>
    cases meaning with
    | direct operation => cases operation <;> simp_all [classHead, literalExpr, typedLiteralExpr, Comparison.branch,
        CompoundGuard.branch, DecidedGuard.dependentBranch, BooleanIdentity.bind, BooleanLocalGuard.branch,
        BooleanLocalGuard.dependentBranch, Identity.run, Identity.pure, Identity.bind,
        UnitSyntax.value, Extremum.expr, ManyFunction.bind, Range.call, Range.head, idLetExpr]
    | canonical operation result left right instanceType => cases operation <;> simp_all [classHead, literalExpr, typedLiteralExpr, Comparison.branch,
        CompoundGuard.branch, DecidedGuard.dependentBranch, BooleanIdentity.bind, BooleanLocalGuard.branch,
        BooleanLocalGuard.dependentBranch, Identity.run, Identity.pure, Identity.bind,
        UnitSyntax.value, Extremum.expr, ManyFunction.bind, Range.call, Range.head, idLetExpr]

end LeanExe.Source.Scalar

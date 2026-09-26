import LeanExe.Source.ScalarHeadEvaluation

open LeanExe.Source.Scalar

theorem natural_literal_unique {number other : Nat} {expression otherExpression : Lean.Expr}
    (first : NaturalLiteral number expression) (second : NaturalLiteral other otherExpression)
    (same : expression = otherExpression) : number = other := by
  induction first generalizing other otherExpression with
  | raw => cases second <;> simp_all
  | ofNat type => cases second <;> simp_all
  | metadata first ih => cases second <;> simp_all

theorem typed_literal_numeral {firstType secondType : ResultType}
    {firstNumeral secondNumeral firstEvidence secondEvidence : Lean.Expr}
    (same : typedLiteralExpr firstType firstNumeral firstEvidence =
      typedLiteralExpr secondType secondNumeral secondEvidence) : firstNumeral = secondNumeral := by
  simp only [typedLiteralExpr, Lean.Expr.app.injEq] at same
  exact same.1.2

set_option linter.unusedSimpArgs false in
theorem literal_eval_inv {type : ResultType} {numeral evidence : Lean.Expr}
    {values : List Value} {value : UInt64} {number : Nat}
    (numberMeaning : NaturalLiteral number numeral)
    (evaluation : EvalWith (typedLiteralExpr type numeral evidence) values value) :
    value = UInt64.ofNat number := by
  generalize expressionEq : typedLiteralExpr type numeral evidence = expression at evaluation
  cases evaluation with
  | ofNat =>
    apply congrArg UInt64.ofNat
    exact (natural_literal_unique numberMeaning .raw (typed_literal_numeral expressionEq)).symm
  | ofNatInstance instanceMeaning =>
    apply congrArg UInt64.ofNat
    exact (natural_literal_unique numberMeaning .raw (typed_literal_numeral expressionEq)).symm
  | ofNatNatural otherNumber instanceMeaning =>
    apply congrArg UInt64.ofNat
    exact (natural_literal_unique numberMeaning otherNumber (typed_literal_numeral expressionEq)).symm
  | ofNatTyped otherNumber instanceMeaning =>
    apply congrArg UInt64.ofNat
    exact (natural_literal_unique numberMeaning otherNumber (typed_literal_numeral expressionEq)).symm
  | binary head left right =>
    cases head with
    | direct operation => cases operation <;> simp_all [typedLiteralExpr, classHead]
    | canonical operation result left right instanceType =>
      cases operation <;> simp_all [typedLiteralExpr, classHead]
  | complement complement argument => cases complement <;> simp_all [typedLiteralExpr]
  | extremum op left right => cases op <;> simp_all [typedLiteralExpr, Extremum.expr, Extremum.head]
  | manyApply call function arguments =>
    have root := congrArg Lean.Expr.getAppFn expressionEq
    rw [ManyCall.expr_root] at root
    simp [typedLiteralExpr, Lean.Expr.getAppFn] at root
  | range countValue initialValue yielding steps =>
    have root := congrArg Lean.Expr.getAppFn expressionEq
    change Lean.Expr.const ``OfNat.ofNat [.zero] = .const ``ForIn.forIn [.zero, .zero, .zero, .zero] at root
    contradiction
  | _ =>
    simp_all [literalExpr, typedLiteralExpr, Comparison.branch, CompoundGuard.branch,
      Guard.dependentBranch, BooleanIdentity.bind, BooleanLocalGuard.branch,
      BooleanLocalGuard.dependentBranch, Identity.run, Identity.pure, Identity.bind,
      UnitSyntax.value, Extremum.expr, ManyFunction.bind, Range.call, Range.head, idLetExpr]

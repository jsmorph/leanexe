import LeanExe.Extract.ScalarFunc

open LeanExe.Extract.Core
open LeanExe.Source.Scalar

run_elab do
  let word : Lean.Expr := .const ``UInt64 []
  let a : Lean.Expr := .bvar 1
  let b : Lean.Expr := .bvar 0
  let annotated : ResultType := .identity .word
  let numeral : Lean.Expr := .lit (.natVal 7)
  let wordInstance : Lean.Expr := .app (.const ``UInt64.instOfNat []) numeral
  let annotatedInstance := Lean.Expr.app (.app (.app (.const ``Id.instOfNat [.zero]) word) numeral) wordInstance
  let sourceNumber := typedLiteralExpr annotated numeral annotatedInstance
  let targetNumber := typedLiteralExpr .word numeral wordInstance
  let sourceAdd := Lean.Expr.app (.app (classHead ScalarPrimitive.add.classNames annotated .word .word .word) a) b
  let sourceMul := Lean.Expr.app (.app (classHead ScalarPrimitive.mul.classNames annotated .word .word .word) a) b
  let targetAdd := Lean.Expr.app (.app (.const ``UInt64.add []) a) b
  let targetMul := Lean.Expr.app (.app (.const ``UInt64.mul []) a) b
  let replaceOperand (operand : Lean.Expr) : Lean.Expr :=
    if LeanExe.Source.ExprEquality.same operand sourceAdd then targetAdd
    else if LeanExe.Source.ExprEquality.same operand sourceMul then targetMul
    else if LeanExe.Source.ExprEquality.same operand sourceNumber then targetNumber
    else operand
  let rec alternate (tree : Guard) : Lean.Expr :=
    match tree with
    | .compare op left right => op.evidenceWith left right (replaceOperand left) (replaceOperand right)
    | .junction n op left right =>
        GuardNegation.evidence n (op.condition left.condition right.condition)
          (op.evidence left.condition right.condition (alternate left) (alternate right))
    | guard => guard.evidence
  let left : Guard := .compare (.lt annotated) sourceAdd sourceNumber
  let right : Guard := .compare (.ne annotated) sourceMul sourceNumber
  let boolean : Guard := .boolean 1 2 .disjunction (.literal 0 false) (.compare .eq a b)
  let functionType := Lean.Expr.forallE `x word (.forallE `y word word .default) .default
  let body (condition evidence trueDomain falseDomain : Lean.Expr) := Lean.Expr.lam `x word
    (.lam `y word
      (.app (.app (.app (.app (.app (.const ``dite [.succ .zero]) word)
        condition) evidence) (.lam `proof trueDomain (.bvar 2) .default))
        (.lam `proof falseDomain (.bvar 1) .default)) .default) .default
  let inputs : List (UInt64 × UInt64) :=
    [(0, 0), (1, 0), (0xffffffffffffffff, 0), (0, 1), (1, 1),
     (0xffffffffffffffff, 1), (0x8000000000000000, 2), (42, 3),
     (0xffffffffffffffff, 63), (0x8000000000000001, 64), (0xffffffffffffffff, 65),
     (0x0123456789abcdef, 0xffffffffffffffff), (3, 17), (17, 3)]
  let mut comparisons : Nat := 0
  let mut rejected : Nat := 0
  for op in [Junction.conjunction, .disjunction] do
    for n in [0, 1, 2, 5] do
      for (l, r) in [(left, right),
          (Guard.junction 0 .disjunction left (.literal (.proposition 0 true)), right),
          (left, Guard.junction 1 .conjunction right boolean)] do
        let guard : Guard := .junction n op l r
        let evidence := alternate guard
        unless guardDecision? guard evidence && (dependentGuard? guard.condition evidence guard.condition (.app (.const ``Not []) guard.condition)).isSome do
          throwError "compound annotation decision rejected"
        let some func := extractScalarFunc `compound (some "entry") functionType (body guard.condition evidence guard.condition (.app (.const ``Not []) guard.condition)) |
          throwError "compound annotation extraction failed"
        let module_ : LeanExe.IR.Module := { funcs := #[func] }
        for (x, y) in inputs do
          let native (operand : Lean.Expr) : UInt64 :=
            if LeanExe.Source.ExprEquality.same operand sourceAdd then x + y
            else if LeanExe.Source.ExprEquality.same operand sourceMul then x * y
            else if LeanExe.Source.ExprEquality.same operand a then x
            else if LeanExe.Source.ExprEquality.same operand b then y
            else 7
          let expected := if guard.denote native then x else y
          let actual := module_.evalFunc 0 [x, y]
          unless actual == expected do throwError "compound decision({x}, {y}): native={expected}, IR={actual}"
          comparisons := comparisons + 1
        let other := match op with | .conjunction => Junction.disjunction | .disjunction => .conjunction
        let invalid : List Lean.Expr :=
          [GuardNegation.evidence n (op.condition l.condition r.condition)
            (other.evidence l.condition r.condition (alternate l) (alternate r)),
           GuardNegation.evidence n (op.condition l.condition r.condition)
            (op.evidence r.condition l.condition (alternate l) (alternate r)),
           GuardNegation.evidence n (op.condition l.condition r.condition)
            (op.evidence l.condition r.condition (alternate r) (alternate l)),
           GuardNegation.evidence n (op.condition l.condition r.condition)
            (op.evidence l.condition r.condition (.const `customDecision []) (alternate r)),
           GuardNegation.evidence n (op.condition l.condition r.condition)
            (op.evidence l.condition r.condition (alternate l) (.const `customDecision [])),
           .mdata {} evidence]
        for decision in invalid do
          unless !(guardDecision? guard decision) &&
              (extractScalarFunc `badCompound (some "entry") functionType (body guard.condition decision guard.condition (.app (.const ``Not []) guard.condition))).isNone do
            throwError "invalid compound decision accepted"
          rejected := rejected + 1
        let falseDomain := Lean.Expr.app (.const ``Not []) guard.condition
        for (trueDomain, falseDomain) in
            [(word, falseDomain), (falseDomain, falseDomain), (guard.condition, guard.condition),
             (guard.condition, word), (Lean.Expr.mdata {} guard.condition, falseDomain)] do
          unless (dependentGuard? guard.condition evidence trueDomain falseDomain).isNone &&
              (extractScalarFunc `badProofDomain (some "entry") functionType
                (body guard.condition evidence trueDomain falseDomain)).isNone do
            throwError "wrong dependent proof domain accepted"
          rejected := rejected + 1
  unless comparisons == 336 && rejected == 264 do throwError "unexpected counts: {comparisons}, {rejected}"
  Lean.logInfo m!"{comparisons} native/dependent-decision-syntax IR comparisons and {rejected} invalid-input rejections passed"

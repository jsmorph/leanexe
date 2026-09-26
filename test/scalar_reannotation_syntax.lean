import LeanExe.Extract.ScalarFunc

open LeanExe.Extract.Core
open LeanExe.Source.Scalar

run_elab do
  let word : Lean.Expr := .const ``UInt64 []
  let a : Lean.Expr := .bvar 1
  let b : Lean.Expr := .bvar 0
  let annotated : ResultType := .identity (.identity .word)
  let numeral : Lean.Expr := .lit (.natVal 7)
  let wordInstance : Lean.Expr := .app (.const ``UInt64.instOfNat []) numeral
  let wrapInstance (type : ResultType) (evidence : Lean.Expr) : Lean.Expr :=
    .app (.app (.app (.const ``Id.instOfNat [.zero]) type.expr) numeral) evidence
  let annotatedInstance := wrapInstance (.identity .word) (wrapInstance .word wordInstance)
  let sourceRight := typedLiteralExpr annotated numeral annotatedInstance
  let targetRight := typedLiteralExpr .word numeral wordInstance
  let functionType := Lean.Expr.forallE `x word (.forallE `y word word .default) .default
  let body (condition evidence : Lean.Expr) := Lean.Expr.lam `x word
    (.lam `y word
      (.app (.app (.app (.app (.app (.const ``ite [.succ .zero]) word)
        condition) evidence) a) b) .default) .default
  let operations : List Comparison := [.eq annotated, .ne annotated, .lt annotated, .le annotated,
    .gt annotated, .ge annotated, .beq, .bne, .boolNot (.negate .eq), .negate (.ne annotated)]
  let inputs : List (UInt64 × UInt64) :=
    [(0, 0), (1, 0), (0xffffffffffffffff, 0), (0, 1), (1, 1),
     (0xffffffffffffffff, 1), (0x8000000000000000, 2), (42, 3),
     (0xffffffffffffffff, 63), (0x8000000000000001, 64), (0xffffffffffffffff, 65),
     (0x0123456789abcdef, 0xffffffffffffffff), (3, 17), (17, 3)]
  let mut comparisons : Nat := 0
  let mut rejected : Nat := 0
  for primitive in ScalarPrimitive.all do
    let sourceHead := classHead primitive.classNames annotated .word annotated .word
    let sourceLeft := Lean.Expr.mdata {} (.app (.app sourceHead a) b)
    let targetLeft := Lean.Expr.mdata {} (.app (.app (.const primitive.name []) a) b)
    unless reannotation? sourceLeft targetLeft && reannotation? sourceRight targetRight do
      throwError "{primitive.name}: standard annotation equivalence rejected"
    for op in operations do
      let condition := op.condition sourceLeft sourceRight
      let evidence := op.evidenceWith sourceLeft sourceRight targetLeft targetRight
      unless (reannotatedComparison? condition evidence).isSome do
        throwError "{primitive.name}, {repr op}: standard reannotated decision rejected"
      let some func := extractScalarFunc `reannotation (some "entry") functionType (body condition evidence) |
        throwError "{primitive.name}, {repr op}: reannotated extraction failed"
      let module_ : LeanExe.IR.Module := { funcs := #[func] }
      for (x, y) in inputs do
        let expected := if op.denote (primitive.denote x y) 7 then x else y
        let actual := module_.evalFunc 0 [x, y]
        unless actual == expected do
          throwError "{primitive.name}, {repr op}({x}, {y}): native={expected}, IR={actual}"
        comparisons := comparisons + 1
      let alteredOperands : List (Lean.Expr × Lean.Expr) :=
        [(b, targetRight), (targetLeft, a), (targetRight, targetLeft),
         (.app (.app (.const `customArithmetic []) a) b, targetRight),
         (targetLeft, typedLiteralExpr .word (.lit (.natVal 8)) wordInstance),
         (targetLeft, typedLiteralExpr annotated numeral wordInstance),
         (targetLeft, typedLiteralExpr .word numeral (.const `customNumeral []))]
      for (left, right) in alteredOperands do
        let invalid := op.evidenceWith sourceLeft sourceRight left right
        unless (reannotatedComparison? condition invalid).isNone &&
            (extractScalarFunc `invalid (some "entry") functionType (body condition invalid)).isNone do
          throwError "{primitive.name}, {repr op}: mismatched decision operands accepted"
        rejected := rejected + 1
      for invalid in [Lean.Expr.const `customDecision [], .mdata {} evidence] do
        unless (reannotatedComparison? condition invalid).isNone &&
            (extractScalarFunc `invalid (some "entry") functionType (body condition invalid)).isNone do
          throwError "{primitive.name}, {repr op}: custom decision expression accepted"
        rejected := rejected + 1
    for other in ScalarPrimitive.all do
      if primitive != other then
        let different := Lean.Expr.mdata {} (.app (.app (.const other.name []) a) b)
        unless !(reannotation? sourceLeft different) do
          throwError "{primitive.name}: different operation accepted"
        rejected := rejected + 1
  unless comparisons == 1400 && rejected == 990 do
    throwError "unexpected test counts: {comparisons}, {rejected}"
  Lean.logInfo m!"{comparisons} native/reannotated-syntax IR comparisons and {rejected} invalid-input rejections passed"

import LeanExe.Extract.ScalarFunc

open LeanExe.Extract.Core
open LeanExe.Source.Scalar

run_elab do
  let word : Lean.Expr := .const ``UInt64 []
  let inputs : List (UInt64 × UInt64) :=
    [(0, 0), (1, 0), (0xffffffffffffffff, 0), (0, 1), (1, 1),
     (0xffffffffffffffff, 1), (0x8000000000000000, 2), (42, 3),
     (0xffffffffffffffff, 63), (0x8000000000000001, 64), (0xffffffffffffffff, 65),
     (0x0123456789abcdef, 0xffffffffffffffff), (3, 17), (17, 3)]
  let functionType := Lean.Expr.forallE `x word (.forallE `y word word .default) .default
  let body (head : Lean.Expr) := Lean.Expr.lam `x word
    (.lam `y word (.app (.app head (.bvar 1)) (.bvar 0)) .default) .default
  let make (left right result instanceType : Lean.Expr)
      (projection adapter instanceName : Lean.Name)
      (projectionLevels adapterLevels instanceLevels : List Lean.Level) : Lean.Expr :=
    .app (.app (.app (.app (.const projection projectionLevels) left) right) result)
      (.app (.app (.const adapter adapterLevels) instanceType) (.const instanceName instanceLevels))
  let one := ResultType.identity .word
  let three := ResultType.identity (.identity (.identity .word))
  let variants : List (ResultType × ResultType × ResultType × ResultType) :=
    [(.word, .word, .word, .word), (.word, one, .word, .word),
     (.word, .word, three, .word), (.word, .word, .word, one),
     (three, .word, .word, .word), (one, three, one, three)]
  let mut comparisons : Nat := 0
  let mut rejected : Nat := 0
  for p in ScalarPrimitive.all do
    for (result, left, right, instanceType) in variants do
      let head := classHead p.classNames result left right instanceType
      unless ScalarPrimitive.ofHead? head == some p do
        throwError "{p.name}: valid annotated arithmetic head rejected"
      let some func := extractScalarFunc `idPrimitive (some "entry") functionType (body head) |
        throwError "{p.name}: annotated operation extraction failed"
      let module_ : LeanExe.IR.Module := { funcs := #[func] }
      for (x, y) in inputs do
        let expected := p.denote x y
        let actual := module_.evalFunc 0 [x, y]
        unless actual == expected do
          throwError "{p.name}({x}, {y}): native={expected}, IR={actual}"
        comparisons := comparisons + 1
    let badTypes := [Lean.Expr.const ``Bool [], .const ``Nat [],
      .app (.const ``Id [.zero]) (.const ``Nat []),
      .app (.const ``Id [.succ .zero]) word,
      .const ``UInt64 [.zero], .const ``Id [.zero]]
    let standard := fun left right result instanceType =>
      make left right result instanceType p.classNames.1 p.classNames.2.1 p.classNames.2.2
        [.zero, .zero, .zero] [.zero] []
    let invalid := badTypes.flatMap (fun bad =>
      [standard bad one.expr three.expr one.expr,
       standard three.expr bad one.expr three.expr,
       standard one.expr three.expr bad one.expr,
       standard three.expr one.expr three.expr bad]) ++
      [make one.expr three.expr one.expr three.expr p.classNames.1 p.classNames.2.1 p.classNames.2.2
        [.succ .zero, .zero, .zero] [.zero] [],
       make three.expr one.expr three.expr one.expr p.classNames.1 p.classNames.2.1 p.classNames.2.2
        [.zero, .zero, .zero] [.succ .zero] [],
       make one.expr three.expr one.expr three.expr p.classNames.1 p.classNames.2.1 p.classNames.2.2
        [.zero, .zero, .zero] [.zero] [.zero],
       make three.expr one.expr three.expr one.expr p.classNames.1 `notTheStandardAdapter p.classNames.2.2
        [.zero, .zero, .zero] [.zero] [],
       make one.expr three.expr one.expr three.expr p.classNames.1 p.classNames.2.1 `notTheStandardInstance
        [.zero, .zero, .zero] [.zero] [],
       make three.expr one.expr three.expr one.expr `notTheStandardOperation p.classNames.2.1 p.classNames.2.2
        [.zero, .zero, .zero] [.zero] []]
    for head in invalid do
      unless (ScalarPrimitive.ofHead? head).isNone &&
          (extractScalarFunc `badIdPrimitive (some "entry") functionType (body head)).isNone do
        throwError "{p.name}: malformed type or instance evidence accepted"
      rejected := rejected + 1
  unless comparisons == 840 && rejected == 300 do
    throwError "unexpected primitive test counts: {comparisons}, {rejected}"
  Lean.logInfo m!"{comparisons} native/primitive-Id IR comparisons and {rejected} malformed-head rejections passed"

import LeanExe.Extract.ScalarFunc

open LeanExe.Extract.Core
open LeanExe.Source.Scalar

run_elab do
  let word : Lean.Expr := .const ``UInt64 []
  let boolean : Lean.Expr := .const ``Bool []
  let inputs : List (UInt64 × UInt64) :=
    [(0, 0), (1, 0), (0xffffffffffffffff, 0), (0, 1), (1, 1),
     (0xffffffffffffffff, 1), (0x8000000000000000, 2), (42, 3),
     (0xffffffffffffffff, 63), (0x8000000000000001, 64), (0xffffffffffffffff, 65),
     (0x0123456789abcdef, 0xffffffffffffffff), (3, 17), (17, 3)]
  let functionType := Lean.Expr.forallE `x word (.forallE `y word word .default) .default
  let body (head : Lean.Expr) := Lean.Expr.lam `x word
    (.lam `y word (.app (.app head (.bvar 1)) (.bvar 0)) .default) .default
  let make (p : ScalarPrimitive) (left right result instanceType : Lean.Expr)
      (adapter instanceName : Lean.Name) : Lean.Expr :=
    .app (.app (.app (.app (.const p.classNames.1 [.zero, .zero, .zero]) left) right) result)
      (.app (.app (.const adapter [.zero]) instanceType) (.const instanceName []))
  let mut comparisons : Nat := 0
  let mut rejected : Nat := 0
  for p in ScalarPrimitive.all do
    for annotation in [ResultType.word, .identity .word, .identity (.identity (.identity .word))] do
      let head := classHead p.classNames annotation
      unless ScalarPrimitive.ofHead? head == some p do
        throwError "{p.name}: valid result annotation rejected"
      let some func := extractScalarFunc `resultAnnotation (some "entry") functionType (body head) |
        throwError "{p.name}: annotated operation extraction failed"
      let module_ : LeanExe.IR.Module := { funcs := #[func] }
      for (x, y) in inputs do
        let expected := p.denote x y
        let actual := module_.evalFunc 0 [x, y]
        unless actual == expected do
          throwError "{p.name}({x}, {y}): native={expected}, IR={actual}"
        comparisons := comparisons + 1
    let badResults := [boolean, .const ``Nat [],
      .app (.const ``Id [.zero]) (.const ``Nat []),
      .app (.const ``Id [.succ .zero]) word,
      .const ``UInt64 [.zero], .const ``Id [.zero]]
    let invalid := badResults.map (fun result =>
      make p word word result word p.classNames.2.1 p.classNames.2.2) ++
      [make p boolean word word word p.classNames.2.1 p.classNames.2.2,
       make p word boolean word word p.classNames.2.1 p.classNames.2.2,
       make p word word word boolean p.classNames.2.1 p.classNames.2.2,
       make p word word word word p.classNames.2.1 `notTheStandardInstance]
    for head in invalid do
      unless (ScalarPrimitive.ofHead? head).isNone &&
          (extractScalarFunc `badResultAnnotation (some "entry") functionType (body head)).isNone do
        throwError "{p.name}: malformed type or instance evidence accepted"
      rejected := rejected + 1
  unless comparisons == 420 && rejected == 100 do
    throwError "unexpected primitive test counts: {comparisons}, {rejected}"
  Lean.logInfo m!"{comparisons} native/primitive-result IR comparisons and {rejected} malformed-head rejections passed"

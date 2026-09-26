import LeanExe.Extract.ScalarFunc

open LeanExe.Extract.Core
open LeanExe.Source.Scalar

run_elab do
  let word : Lean.Expr := .const ``UInt64 []
  let a : Lean.Expr := .bvar 1
  let b : Lean.Expr := .bvar 0
  let functionType := Lean.Expr.forallE `x word (.forallE `y word word .default) .default
  let body (condition evidence : Lean.Expr) := Lean.Expr.lam `x word
    (.lam `y word
      (.app (.app (.app (.app (.app (.const ``ite [.succ .zero]) word)
        condition) evidence) a) b) .default) .default
  let shape (name : Lean.Name) (levels : List Lean.Level) (type : Lean.Expr)
      (instanceName : Option Lean.Name) : Lean.Expr :=
    let head := .app (.const name levels) type
    let head := match instanceName with
      | none => head
      | some instanceName => .app head (.const instanceName [])
    .app (.app head a) b
  let operations : List (Lean.Name × Option Lean.Name × (ResultType → Comparison)) :=
    [(``Eq, none, @Comparison.eq), (``Ne, none, @Comparison.ne),
     (``LT.lt, some ``instLTUInt64, @Comparison.lt),
     (``LE.le, some ``instLEUInt64, @Comparison.le),
     (``GT.gt, some ``instLTUInt64, @Comparison.gt),
     (``GE.ge, some ``instLEUInt64, @Comparison.ge)]
  let types : List ResultType := [.word, .identity .word, .identity (.identity (.identity .word))]
  let inputs : List (UInt64 × UInt64) :=
    [(0, 0), (1, 0), (0xffffffffffffffff, 0), (0, 1), (1, 1),
     (0xffffffffffffffff, 1), (0x8000000000000000, 2), (42, 3),
     (0xffffffffffffffff, 63), (0x8000000000000001, 64), (0xffffffffffffffff, 65),
     (0x0123456789abcdef, 0xffffffffffffffff), (3, 17), (17, 3)]
  let badTypes : List Lean.Expr := [.const ``Bool [], .const ``Nat [],
    .app (.const ``Id [.zero]) (.const ``Nat []),
    .app (.const ``Id [.succ .zero]) word, .const ``UInt64 [.zero], .const ``Id [.zero]]
  let mut comparisons : Nat := 0
  let mut rejected : Nat := 0
  for (name, instanceName, operation) in operations do
    let levels := if instanceName.isSome then [Lean.Level.zero] else [.succ .zero]
    for type in types do
      let op := operation type
      let condition := shape name levels type.expr instanceName
      let evidence := op.evidence a b
      unless comparison? condition evidence == some (op, a, b) do
        throwError "{name}: standard annotated comparison rejected"
      let some func := extractScalarFunc `comparison (some "entry") functionType (body condition evidence) |
        throwError "{name}: annotated comparison extraction failed"
      let module_ : LeanExe.IR.Module := { funcs := #[func] }
      for (x, y) in inputs do
        let expected := if op.denote x y then x else y
        let actual := module_.evalFunc 0 [x, y]
        unless actual == expected do
          throwError "{name}({x}, {y}): native={expected}, IR={actual}"
        comparisons := comparisons + 1
      let invalidConditions := badTypes.map (fun bad => shape name levels bad instanceName) ++
        [shape name [] type.expr instanceName,
         shape name [.succ (.succ .zero)] type.expr instanceName] ++
        (if instanceName.isSome then [shape name levels type.expr (some `customOrder)] else [])
      for invalid in invalidConditions do
        unless (comparison? invalid evidence).isNone &&
            (extractScalarFunc `badComparison (some "entry") functionType (body invalid evidence)).isNone do
          throwError "{name}: invalid comparison type, universe, or instance accepted"
        rejected := rejected + 1
      for invalid in [Lean.Expr.const `customDecision [], op.evidence b a, .mdata {} evidence] do
        unless (comparison? condition invalid).isNone &&
            (extractScalarFunc `badDecision (some "entry") functionType (body condition invalid)).isNone do
          throwError "{name}: mismatched decision evidence accepted"
        rejected := rejected + 1
  unless comparisons == 252 && rejected == 210 do
    throwError "unexpected comparison test counts: {comparisons}, {rejected}"
  Lean.logInfo m!"{comparisons} native/comparison-head IR comparisons and {rejected} malformed-input rejections passed"

import LeanExe.Extract.ScalarFunc

open LeanExe.Extract.Core
open LeanExe.Source.Scalar

run_elab do
  let word : Lean.Expr := .const ``UInt64 []
  let boolean : Lean.Expr := .const ``Bool []
  let signature := Lean.Expr.forallE `x word (.forallE `y word word .default) .default
  let toWord (value : Lean.Expr) := Lean.Expr.app (.const ``Bool.toUInt64 []) value
  let truth (value : Lean.Expr) := Lean.mkAppN (.const ``Eq [.succ .zero]) #[boolean, value, booleanLiteralExpr true]
  let decision (value : Lean.Expr) := Lean.mkAppN (.const ``instDecidableEqBool []) #[value, booleanLiteralExpr true]
  let wrap (body : Lean.Expr) := Lean.Expr.lam `x word (.lam `y word body .default) .default
  let add (x y : Lean.Expr) := Lean.mkAppN (.const ``UInt64.add []) #[x, y]
  let mul (x y : Lean.Expr) := Lean.mkAppN (.const ``UInt64.mul []) #[x, y]
  let call (index : Nat) (x y : Lean.Expr) := Lean.Expr.app (.app (.bvar index) x) y
  let inputs : List (UInt64 × UInt64) :=
    [(0, 0), (1, 0), (0, 1), (1, 1), (42, 3), (3, 17), (17, 3),
     (0xffffffffffffffff, 0), (0xffffffffffffffff, 1),
     (0x8000000000000000, 2), (0xffffffffffffffff, 63),
     (0x8000000000000001, 64), (0xffffffffffffffff, 65),
     (0x0123456789abcdef, 0xffffffffffffffff)]
  let mut comparisons : Nat := 0
  let mut rejected : Nat := 0
  let mut controls : Nat := 0
  for depth in [0, 1, 2] do
    let result := (List.range depth).foldl (fun type _ => BooleanType.identity type) .boolean
    for firstInfo in [Lean.BinderInfo.default, .implicit] do
      for secondInfo in [Lean.BinderInfo.default, .strictImplicit] do
        for nondep in [false, true] do
          for wrappers in [0, 1, 2] do
            let rawBody := (BooleanLocal.compare .eq (add (.bvar 1) (mul (literalExpr 3) (.bvar 0))) (add (.bvar 3) (.bvar 2))).expr
            let body := if wrappers == 0 then rawBody else if wrappers == 1 then BooleanIdentity.pure rawBody result
              else BooleanIdentity.run (.mdata {} (BooleanIdentity.pure rawBody result)) (.identity result)
            let helper (firstType secondType firstDomain secondDomain output value tail : Lean.Expr) :=
              Lean.Expr.letE `f (.forallE `a firstType (.forallE `b secondType output secondInfo) firstInfo)
                (.lam `a firstDomain (.lam `b secondDomain value secondInfo) firstInfo) tail nondep
            let typedHelper := helper word word word word result.expr
            for unused in [false, true] do
              for disjoin in [false, true] do
                let continuation := if unused then (BooleanLocal.compare .eq (.bvar 2) (.bvar 1)).expr
                  else Lean.mkAppN (.const (if disjoin then ``Bool.or else ``Bool.and) [])
                    #[call 0 (.bvar 2) (.bvar 1), call 0 (.bvar 1) (.bvar 2)]
                let source := typedHelper body continuation
                unless (booleanLocalOperands? source).isNone && (booleanBinaryHelper? source).isSome &&
                    (booleanBinaryCall? (call 0 (.bvar 2) (.bvar 1))).isSome do
                  throwError "binary helper/call recognition failed"
                controls := controls + 1
                for mode in ([0, 1, 2, 3] : List Nat) do
                  let expression (value evidence td fd : Lean.Expr) : Lean.Expr :=
                    if mode == 0 then toWord value
                    else if mode == 1 then Lean.mkAppN (.const ``ite [.succ .zero]) #[word, truth value, evidence, .bvar 1, .bvar 0]
                    else if mode == 2 then Lean.mkAppN (.const ``dite [.succ .zero]) #[word, truth value, evidence,
                      .lam `proof td (.bvar 2) firstInfo, .lam `proof fd (.bvar 1) secondInfo]
                    else value
                  let make (value : Lean.Expr) :=
                    if mode == 3 then
                      match value with
                      | .letE n t v tail nd => wrap (.letE n t v (toWord tail) nd)
                      | _ => wrap value
                    else wrap (expression value (decision value) (truth value) (.app (.const ``Not []) (truth value)))
                  let some func := extractScalarFunc `binaryHelper (some "entry") signature (make source) |
                    throwError "binary helper rejected: result depth {depth}, mode {mode}"
                  let module_ : LeanExe.IR.Module := { funcs := #[func] }
                  for (x, y) in inputs do
                    let f := fun a b : UInt64 => a + 3 * b == x + y
                    let flag := if unused then x == y else if disjoin then f x y || f y x else f x y && f y x
                    let expected := if mode == 0 || mode == 3 then flag.toUInt64 else if flag then x else y
                    let actual := module_.evalFunc 0 [x, y]
                    unless actual == expected do throwError "binary helper argument order/capture: {actual} != {expected}"
                    comparisons := comparisons + 1
                  let unknown := Lean.Expr.const `unsupportedBinaryHelper []
                  let wrongId := Lean.Expr.app (.const ``Id [.succ .zero]) boolean
                  for bad in [
                      helper boolean word word word result.expr body continuation,
                      helper word boolean word word result.expr body continuation,
                      helper word word boolean word result.expr body continuation,
                      helper word word word boolean result.expr body continuation,
                      helper (.app (.const ``Id [.zero]) word) word word word result.expr body continuation,
                      helper word (.const ``Nat []) word word result.expr body continuation,
                      helper word word word (.const ``Nat []) result.expr body continuation,
                      helper word word word word wrongId body continuation,
                      helper word word word word word body continuation,
                      typedHelper unknown continuation, typedHelper (literalExpr 0) continuation,
                      typedHelper body unknown, typedHelper body (literalExpr 0),
                      typedHelper body (.bvar 0), typedHelper body (.app (.bvar 0) (.bvar 2)),
                      typedHelper body (.app (call 0 (.bvar 2) (.bvar 1)) (.bvar 1)),
                      typedHelper body (call 9 (.bvar 2) (.bvar 1)),
                      typedHelper body (call 0 (booleanLiteralExpr true) (.bvar 1)),
                      typedHelper body (call 0 (.bvar 2) (booleanLiteralExpr false)),
                      typedHelper body (call 0 unknown (.bvar 1)),
                      typedHelper body (call 0 (.bvar 2) unknown)] do
                    unless (extractScalarFunc `invalidBinaryHelper none signature (make bad)).isNone do
                      throwError "invalid binary helper admitted, mode {mode}"
                    rejected := rejected + 1
                  if mode == 1 || mode == 2 then
                    for evidence in [.const `customDecision [], .mdata {} (decision source), decision (booleanLiteralExpr true)] do
                      unless (extractScalarFunc `invalidDecision none signature
                          (wrap (expression source evidence (truth source) (.app (.const ``Not []) (truth source))))).isNone do
                        throwError "invalid binary helper decision admitted"
                      rejected := rejected + 1
                  if mode == 2 then
                    for (td, fd) in [(word, .app (.const ``Not []) (truth source)),
                        (truth source, word), (truth source, truth source)] do
                      unless (extractScalarFunc `invalidDomain none signature
                          (wrap (expression source (decision source) td fd))).isNone do
                        throwError "invalid binary helper proof domain admitted"
                      rejected := rejected + 1
                unless (extractScalarFunc `wrongResultKind none signature
                    (wrap (typedHelper body (call 0 (.bvar 2) (.bvar 1))))).isNone do
                  throwError "Boolean-returning helper used as a word function"
                rejected := rejected + 1
  unless comparisons == 16128 && rejected == 27072 && controls == 288 do
    throwError "unexpected counts {comparisons}, {rejected}, {controls}"
  Lean.logInfo m!"{comparisons} native/binary Boolean helper IR comparisons, {rejected} invalid-input tests and {controls} admission controls passed"

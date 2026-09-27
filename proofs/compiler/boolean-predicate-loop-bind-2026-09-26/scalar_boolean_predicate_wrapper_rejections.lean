import LeanExe.Extract.ScalarFunc

open LeanExe.Extract.Core
open LeanExe.Source.Scalar

run_elab do
  let word : Lean.Expr := .const ``UInt64 []
  let boolean : Lean.Expr := .const ``Bool []
  let functionType := Lean.Expr.forallE `x word (.forallE `y word word .default) .default
  let toWord (value : Lean.Expr) := Lean.Expr.app (.const ``Bool.toUInt64 []) value
  let pureInstance := (BooleanIdentity.pure (.bvar 0)).getAppArgs[1]!
  let pureExpr (levels : List Lean.Level) (monad evidence type body : Lean.Expr) :=
    Lean.mkAppN (.const ``Pure.pure levels) #[monad, evidence, type, body]
  let runExpr (levels : List Lean.Level) (type body : Lean.Expr) :=
    Lean.mkAppN (.const ``Id.run levels) #[type, body]
  let mut rejected : Nat := 0
  let mut controls : Nat := 0
  for scope in [0, 1, 2] do
    let index := if scope == 2 then 2 else 0
    let wrap (result : Lean.Expr) :=
      let helper (body : Lean.Expr) := Lean.Expr.letE `predicate
        (.forallE `b boolean boolean .default) (.lam `b boolean (.bvar 0) .default) body false
      let body := if scope == 0 then helper result else if scope == 1 then
        Range.call (.bvar 1) (.bvar 0) `i `a .default .default (helper (Step.yieldDirect result))
        else helper (Range.call (.bvar 2) (.bvar 1) `i `a .default .default (Step.yieldDirect result))
      Lean.Expr.lam `x word (.lam `y word body .default) .default
    let check (body : Lean.Expr) := extractScalarFunc `predicateWrapper (some "entry") functionType (wrap body)
    for flag in [false, true] do
      let call := Lean.Expr.app (.bvar index) (booleanLiteralExpr flag)
      for wrapper in [BooleanWrapper.pure .boolean, .run .boolean, .metadata {}] do
        let valid := wrapper.expr call
        for body in [toWord valid, Lean.Expr.letE `unused boolean valid (literalExpr 7) false] do
          unless (check body).isSome do throwError "valid wrapped predicate rejected"
          controls := controls + 1
        for input in [Lean.Expr.bvar index, .bvar (index + 1), .const `unsupportedInner [], literalExpr 0] do
          for body in [wrapper.expr input, wrapper.expr (wrapper.expr input)] do
            unless (check (toWord body)).isNone do throwError "invalid wrapped body accepted"
            rejected := rejected + 1
        let invalid := match wrapper with
          | .pure _ =>
            [pureExpr [.zero, .zero] (.const ``Id [.zero]) pureInstance word call,
             pureExpr [.zero, .zero] (.const ``Id [.zero]) pureInstance (.const ``Nat []) call,
             pureExpr [.zero, .zero] (.const ``Id [.zero]) pureInstance (.const ``Bool [.zero]) call,
             pureExpr [.zero, .zero] (.const ``Id [.zero]) (.const `customPure []) boolean call,
             pureExpr [.succ .zero, .zero] (.const ``Id [.zero]) pureInstance boolean call,
             pureExpr [.zero, .zero] (.const `customMonad []) pureInstance boolean call]
          | .run _ =>
            [runExpr [.zero] word call, runExpr [.zero] (.const ``Nat []) call,
             runExpr [.zero] (.const ``Bool [.zero]) call,
             runExpr [.succ .zero] boolean call]
          | .metadata _ => []
        for value in invalid do
          unless (check (toWord value)).isNone do throwError "invalid wrapper type/instance/universe accepted"
          rejected := rejected + 1
  unless controls == 36 && rejected == 204 do throwError "unexpected counts {controls}, {rejected}"
  Lean.logInfo m!"{controls} wrapper admission controls and {rejected} type/instance/inner-value rejection tests passed"

import LeanExe.Extract.ScalarFunc

open LeanExe.Extract.Core
open LeanExe.Source.Scalar

run_elab do
  let word : Lean.Expr := .const ``UInt64 []
  let boolean : Lean.Expr := .const ``Bool []
  let functionType := Lean.Expr.forallE `x word (.forallE `y word word .default) .default
  let toWord (body : Lean.Expr) := Lean.Expr.app (.const ``Bool.toUInt64 []) body
  let mut rejected : Nat := 0
  let mut controls : Nat := 0
  for scope in [0, 1, 2] do
    let index := if scope == 2 then 2 else 0
    let wordIndex := if scope == 2 then 0 else 1
    let wrap (result : Lean.Expr) :=
      let helper (body : Lean.Expr) := Lean.Expr.letE `predicate
        (.forallE `b boolean boolean .default) (.lam `b boolean (.bvar 0) .default) body false
      let body := if scope == 0 then helper result else if scope == 1 then
        Range.call (.bvar 1) (.bvar 0) `i `a .default .default (helper (Step.yieldDirect result))
        else helper (Range.call (.bvar 2) (.bvar 1) `i `a .default .default (Step.yieldDirect result))
      Lean.Expr.lam `x word (.lam `y word body .default) .default
    let check (value : Lean.Expr) := extractScalarFunc `predicateLet (some "entry") functionType (wrap value)
    for nondep in [false, true] do
      for flag in [false, true] do
        let literal := booleanLiteralExpr flag
        let call := Lean.Expr.app (.bvar index) literal
        let make (value body : Lean.Expr) := Lean.Expr.letE `flag boolean value body nondep
        for body in [toWord (.bvar 0), literalExpr 0] do
          unless (check (make call body)).isSome do throwError "valid used/unused Boolean let rejected"
          controls := controls + 1
          for value in [literalExpr 0, Lean.Expr.bvar index, .bvar wordIndex,
              .const `unsupportedValue [], .app (.bvar index) (literalExpr 0),
              .app (.bvar wordIndex) literal, .app (.bvar index) (.bvar wordIndex)] do
            unless (check (make value body)).isNone do throwError "invalid used/unused Boolean let accepted"
            rejected := rejected + 1
        for body in [Lean.Expr.bvar 0, .app (.bvar 0) literal, toWord (.bvar (index + 1))] do
          unless (check (make call body)).isNone do throwError "Boolean let changed a value or function kind"
          rejected := rejected + 1
  unless controls == 24 && rejected == 204 do throwError "unexpected counts {controls}, {rejected}"
  Lean.logInfo m!"{controls} Boolean let admission controls and {rejected} type/unused-value rejection tests passed"

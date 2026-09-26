import LeanExe.Extract.ScalarFunc

open LeanExe.Extract.Core
open LeanExe.Source.Scalar

run_elab do
  let word : Lean.Expr := .const ``UInt64 []
  let boolean : Lean.Expr := .const ``Bool []
  let functionType := Lean.Expr.forallE `count word (.forallE `seed word word .default) .default
  let toWord (body : Lean.Expr) := Lean.Expr.app (.const ``Bool.toUInt64 []) body
  let helper (body : Lean.Expr) := Lean.Expr.letE `predicate
    (.forallE `b boolean boolean .default) (.lam `b boolean (.bvar 0) .default) body false
  let mut rejected : Nat := 0
  let mut controls : Nat := 0
  for outside in [false, true] do
    for nondep in [false, true] do
      for flag in [false, true] do
        let literal := booleanLiteralExpr flag
        let call := Lean.Expr.app (.bvar 0) literal
        let wrap (value result : Lean.Expr) :=
          let body := if outside then helper (.letE `flag boolean value
            (Range.call (.bvar 3) (.bvar 2) `i `a .default .default
              (Step.yieldDirect (LeanExe.Source.ExprProofBinder.lift 0
                (LeanExe.Source.ExprProofBinder.lift 0 result)))) nondep)
            else Range.call (.bvar 1) (.bvar 0) `i `a .default .default
              (helper (.letE `flag boolean value (Step.yieldDirect result) nondep))
          Lean.Expr.lam `count word (.lam `seed word body .default) .default
        let check (value result : Lean.Expr) :=
          extractScalarFunc `loopBooleanLet (some "entry") functionType (wrap value result)
        for result in [toWord (.bvar 0), literalExpr 0] do
          unless (check call result).isSome do throwError "valid used/unused loop Boolean let rejected"
          controls := controls + 1
          for value in [literalExpr 0, Lean.Expr.bvar 0, .bvar 1,
              .const `unsupportedValue [], .app (.bvar 0) (literalExpr 0),
              .app (.bvar 1) literal, .app (.bvar 0) (.bvar 1)] do
            unless (check value result).isNone do throwError "invalid used/unused loop Boolean let accepted"
            rejected := rejected + 1
        for result in [Lean.Expr.bvar 0, .app (.bvar 0) literal, toWord (.bvar 1)] do
          unless (check call result).isNone do throwError "loop Boolean let changed a value/function kind"
          rejected := rejected + 1
  unless controls == 16 && rejected == 136 do throwError "unexpected counts {controls}, {rejected}"
  Lean.logInfo m!"{controls} loop Boolean let admission controls and {rejected} type/unused-value rejection tests passed"

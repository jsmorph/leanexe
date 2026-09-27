import LeanExe.Extract.ScalarFunc

open LeanExe.Extract.Core
open LeanExe.Source.Scalar

run_elab do
  let word : Lean.Expr := .const ``UInt64 []
  let boolean : Lean.Expr := .const ``Bool []
  let functionType := Lean.Expr.forallE `count word (.forallE `seed word word .default) .default
  let wrap (body : Lean.Expr) := Lean.Expr.lam `count word (.lam `seed word body .default) .default
  let toWord (body : Lean.Expr) := Lean.Expr.app (.const ``Bool.toUInt64 []) body
  let add (left right : Lean.Expr) := Lean.Expr.app (.app (.const ``UInt64.add []) left) right
  let inputs : List (UInt64 × UInt64) :=
    ([0, 1, 2, 7, 16, 31] : List UInt64).flatMap fun n =>
      ([0, 1, 0x8000000000000000, 0xffffffffffffffff] : List UInt64).map fun seed => (n, seed)
  let mut comparisons : Nat := 0
  let mut rejected : Nat := 0
  for binder in [Lean.BinderInfo.default, .implicit] do
    for depth in [0, 2] do
      let bt := (List.range depth).foldl (fun t _ => BooleanType.identity t) .boolean
      for negations in [0, 1, 2, 3] do
        for nondep in [false, true] do
          for flag in [false, true] do
            let literal := booleanLiteralExpr flag
            let helperBody : BooleanLocal := .junction 0 .conjunction
              (.var 0 0) (.compare .ne (.bvar 1) (literalExpr 0))
            let bound := BooleanGuardNegation.expr negations (.app (.bvar 0) literal)
            let indexWord : Lean.Expr := .app (.const ``UInt64.ofNat []) (.bvar 1)
            let body := Step.branch .eq .word (toWord (.bvar 2)) (literalExpr 1)
              (Step.doneDirect (add (.bvar 0) (literalExpr 7)))
              (Step.yieldDirect (add (add (.bvar 0) indexWord) (literalExpr 1)))
            let make (input result domain value savedType saved step : Lean.Expr) :=
              Lean.Expr.letE `predicate (.forallE `typeInput input result binder)
                (.lam `valueInput domain value binder)
                (.letE `saved savedType saved
                  (Range.call (.bvar 3) (.bvar 2) `i `a .default .default step) nondep) nondep
            let source := make boolean bt.expr boolean helperBody.expr bt.expr bound body
            let some func := extractScalarFunc `outerBooleanLet (some "entry") functionType (wrap source) |
              throwError "outer Boolean let rejected"
            let module_ : LeanExe.IR.Module := { funcs := #[func] }
            for (count, seed) in inputs do
              let saved := GuardNegation.denote negations (flag && seed != 0)
              let expected := forIn (m := Id) [:count.toNat] seed fun i a =>
                if saved then .done (a + 7) else .yield (a + UInt64.ofNat i + 1)
              let actual := module_.evalFunc 0 [count, seed]
              unless actual == expected do throwError "outer Boolean let {actual}, expected {expected}"
              comparisons := comparisons + 1
            let invalid := [make word bt.expr boolean helperBody.expr bt.expr bound body,
              make boolean word boolean helperBody.expr bt.expr bound body,
              make boolean bt.expr word helperBody.expr bt.expr bound body,
              make boolean bt.expr boolean (.bvar 1) bt.expr bound body,
              make boolean bt.expr boolean helperBody.expr word bound body,
              make boolean bt.expr boolean helperBody.expr bt.expr (literalExpr 0) body,
              make boolean bt.expr boolean helperBody.expr bt.expr (.bvar 0) body,
              make boolean bt.expr boolean helperBody.expr bt.expr (.bvar 1) body,
              make boolean bt.expr boolean helperBody.expr bt.expr (.app (.bvar 0) (.bvar 1)) body,
              make boolean bt.expr boolean helperBody.expr bt.expr bound (Step.yieldDirect (.bvar 2))]
            for source in invalid do
              unless (extractScalarFunc `invalidOuterBooleanLet (some "entry") functionType (wrap source)).isNone do
                throwError "invalid outer Boolean let accepted"
              rejected := rejected + 1
  unless comparisons == 1536 && rejected == 640 do throwError "unexpected counts {comparisons}, {rejected}"
  Lean.logInfo m!"{comparisons} native/outer Boolean let IR comparisons and {rejected} type rejection tests passed"

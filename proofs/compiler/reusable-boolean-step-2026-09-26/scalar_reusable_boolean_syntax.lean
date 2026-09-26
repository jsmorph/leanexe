import LeanExe.Extract.ScalarFunc

open LeanExe.Extract.Core
open LeanExe.Source.Scalar

run_elab do
  let word : Lean.Expr := .const ``UInt64 []
  let boolean : Lean.Expr := .const ``Bool []
  let functionType := Lean.Expr.forallE `x word (.forallE `y word word .default) .default
  let wrap (body : Lean.Expr) := Lean.Expr.lam `x word (.lam `y word body .default) .default
  let toWord (body : Lean.Expr) := Lean.Expr.app (.const ``Bool.toUInt64 []) body
  let inputs : List (UInt64 × UInt64) :=
    [(0, 0), (1, 0), (0, 1), (1, 1), (42, 3), (3, 17), (17, 3),
     (0xffffffffffffffff, 0), (0xffffffffffffffff, 1),
     (0x8000000000000000, 2), (0xffffffffffffffff, 63),
     (0x8000000000000001, 64), (0xffffffffffffffff, 65),
     (0x0123456789abcdef, 0xffffffffffffffff)]
  let mut comparisons : Nat := 0
  let mut rejected : Nat := 0
  for binder in [Lean.BinderInfo.default, .implicit, .strictImplicit, .instImplicit] do
    for depth in [0, 1, 3] do
      let bt := (List.range depth).foldl (fun t _ => BooleanType.identity t) .boolean
      for negations in [0, 1, 2] do
        for nondep in [false, true] do
          let helperBody : BooleanLocal := .compare .eq (.bvar 0) (.bvar 1)
          let calls : BooleanLocal := .junction 0 .conjunction
            (.predicate negations 0 (.bvar 2)) (.predicate negations 0 (.bvar 1))
          let helper (input result domain value body : Lean.Expr) :=
            Lean.Expr.letE `predicate (.forallE `typeInput input result binder)
              (.lam `valueInput domain value binder) body nondep
          let source := helper word bt.expr word helperBody.expr (toWord calls.expr)
          let some func := extractScalarFunc `reusableSyntax (some "entry") functionType (wrap source) |
            throwError "reusable helper compiler rejected syntax"
          let module_ : LeanExe.IR.Module := { funcs := #[func] }
          for (x, y) in inputs do
            let expected := ((GuardNegation.denote negations (x == y)) &&
              (GuardNegation.denote negations true)).toUInt64
            let actual := module_.evalFunc 0 [x, y]
            unless actual == expected do throwError "reusable helper result {actual}, expected {expected}"
            comparisons := comparisons + 1
          let invalid : List Lean.Expr :=
            [helper word bt.expr boolean helperBody.expr (toWord calls.expr),
             helper boolean bt.expr word helperBody.expr (toWord calls.expr),
             helper word (.const ``Nat []) word helperBody.expr (toWord calls.expr),
             helper word word word helperBody.expr (toWord calls.expr),
             helper word bt.expr word (.bvar 0) (toWord calls.expr),
             helper word bt.expr word helperBody.expr (.bvar 0),
             helper word bt.expr word helperBody.expr
               (toWord (.app (.bvar 0) (.const ``Bool.true []))),
             helper word bt.expr word helperBody.expr (toWord (.bvar 0)),
             helper word bt.expr word (.app (.bvar 0) (.bvar 1)) (literalExpr 0),
             helper word bt.expr word (.const `unsupportedPredicate []) (literalExpr 0),
             helper word bt.expr word helperBody.expr
               (toWord (.app (.bvar 0) (.const `unsupportedArgument []))),
             helper word bt.expr word helperBody.expr
               (toWord (.app (.bvar 1) (.bvar 2)))]
          for body in invalid do
            if (extractScalarFunc `invalidReusable (some "entry") functionType (wrap body)).isSome then
              throwError "invalid reusable helper was admitted"
            rejected := rejected + 1
  unless comparisons == 1008 && rejected == 864 do
    throwError "unexpected counts {comparisons}, {rejected}"
  Lean.logInfo m!"{comparisons} native/reusable-Boolean syntax comparisons and {rejected} invalid-input tests passed"

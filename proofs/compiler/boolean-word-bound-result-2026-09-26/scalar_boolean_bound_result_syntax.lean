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
  let mut controls : Nat := 0
  for binder in [Lean.BinderInfo.default, .implicit] do
    for depth in [0, 2] do
      let bt := (List.range depth).foldl (fun t _ => BooleanType.identity t) .boolean
      let shape : BooleanFunctionBinding := {
        functionName := `transform
        typeName := `input
        typeInfo := binder
        valueInfo := binder
        result := bt
        nondep := false }
      for negations in [0, 1, 2, 3] do
        for form in [BooleanBindingForm.letE false, .letE true, .application binder, .namedApplication shape] do
          for callValue in [false, true] do
            for callBody in [false, true] do
              for flag in [false, true] do
                let fBody : BooleanLocal := .junction 0 .conjunction
                  (.var 0 0) (.compare .ne (.bvar 2) (.bvar 1))
                let outer (body : Lean.Expr) := Lean.Expr.letE `f
                  (.forallE `b boolean bt.expr binder) (.lam `b boolean fBody.expr binder) body false
                let value : BooleanLocal := if callValue then .predicate 0 0 (booleanLiteralExpr flag) else .literal 0 flag
                let body : BooleanLocal := if callBody then .predicate 0 1 (BooleanGuardNegation.expr 1 (.bvar 0)) else .var 0 0
                let make (type value body : Lean.Expr) := outer (toWord
                  (BooleanGuardNegation.expr negations (form.expr `saved type value body)))
                let source := make bt.expr value.expr body.expr
                let some func := extractScalarFunc `booleanBoundResult (some "entry") functionType (wrap source) |
                  throwError "Boolean bound result rejected"
                let module_ : LeanExe.IR.Module := { funcs := #[func] }
                for (x, y) in inputs do
                  let saved := if callValue then flag && x != y else flag
                  let result := if callBody then !saved && x != y else saved
                  let expected := (GuardNegation.denote negations result).toUInt64
                  let actual := module_.evalFunc 0 [x, y]
                  unless actual == expected do throwError "Boolean bound result {actual}, expected {expected}"
                  comparisons := comparisons + 1
                unless (extractScalarFunc `unusedBound (some "entry") functionType
                    (wrap (make bt.expr value.expr (booleanLiteralExpr true)))).isSome do
                  throwError "valid unused Boolean bound result rejected"
                controls := controls + 1
                for source in [make bt.expr (literalExpr 0) body.expr,
                    make bt.expr (.bvar 0) body.expr,
                    make bt.expr (.app (.bvar 0) (literalExpr 0)) body.expr,
                    make bt.expr value.expr (literalExpr 0),
                    make bt.expr value.expr (.app (.bvar 0) (booleanLiteralExpr true)),
                    make bt.expr value.expr (.app (.bvar 1) (literalExpr 0)),
                    make bt.expr (.const `unsupportedUnusedFlag []) (booleanLiteralExpr false),
                    make (.const ``Nat []) value.expr body.expr] do
                  unless (extractScalarFunc `invalidBoundResult (some "entry") functionType (wrap source)).isNone do
                    throwError "invalid Boolean bound result admitted"
                  rejected := rejected + 1
  unless comparisons == 7168 && rejected == 4096 && controls == 512 do
    throwError "unexpected counts {comparisons}, {rejected}, {controls}"
  Lean.logInfo m!"{comparisons} native/Boolean bound-result IR comparisons, {rejected} invalid-input tests and {controls} admission controls passed"

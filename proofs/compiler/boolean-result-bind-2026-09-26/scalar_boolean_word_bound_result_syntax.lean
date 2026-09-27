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
      let wt := (List.range depth).foldl (fun t _ => ResultType.identity t) .word
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
                let flagWord := if flag then 1 else 0
                let base := Lean.Expr.app (.app (.const ``UInt64.add []) (.bvar 2)) (literalExpr flagWord)
                let value := if callValue then Lean.Expr.app (.app (.const ``UInt64.add []) base)
                  (toWord (.app (.bvar 0) (booleanLiteralExpr true))) else base
                let comparison := (BooleanLocal.compare .eq (.bvar 0) (.bvar 2)).expr
                let body := if callBody then Lean.Expr.app (.bvar 1) comparison else comparison
                let make (type value body : Lean.Expr) := outer (toWord
                  (BooleanGuardNegation.expr negations (form.expr `saved type value body)))
                let source := make wt.expr value body
                let some func := extractScalarFunc `booleanBoundResult (some "entry") functionType (wrap source) |
                  throwError "Boolean word-bound result rejected"
                let module_ : LeanExe.IR.Module := { funcs := #[func] }
                for (x, y) in inputs do
                  let saved := x + UInt64.ofNat flagWord + (if callValue then (x != y).toUInt64 else 0)
                  let result := if callBody then saved == y && x != y else saved == y
                  let expected := (GuardNegation.denote negations result).toUInt64
                  let actual := module_.evalFunc 0 [x, y]
                  unless actual == expected do throwError "Boolean word-bound result {actual}, expected {expected}"
                  comparisons := comparisons + 1
                unless (extractScalarFunc `unusedBound (some "entry") functionType
                    (wrap (make wt.expr value (booleanLiteralExpr true)))).isSome do
                  throwError "valid unused Boolean word-bound result rejected"
                controls := controls + 1
                for source in [make wt.expr (booleanLiteralExpr flag) body,
                    make wt.expr (.bvar 0) body,
                    make wt.expr (.app (.bvar 0) (booleanLiteralExpr true)) body,
                    make wt.expr value (.bvar 0),
                    make wt.expr value (literalExpr 0),
                    make wt.expr value (.app (.bvar 0) (booleanLiteralExpr true)),
                    make wt.expr value (.app (.bvar 1) (.bvar 0)),
                    make wt.expr (.const `unsupportedUnusedWord []) (booleanLiteralExpr false),
                    make (.const ``Nat []) value body] do
                  unless (extractScalarFunc `invalidBoundResult (some "entry") functionType (wrap source)).isNone do
                    throwError "invalid Boolean word-bound result admitted"
                  rejected := rejected + 1
  unless comparisons == 7168 && rejected == 4608 && controls == 512 do
    throwError "unexpected counts {comparisons}, {rejected}, {controls}"
  Lean.logInfo m!"{comparisons} native/Boolean word-bound-result IR comparisons, {rejected} invalid-input tests and {controls} admission controls passed"

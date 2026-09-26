import LeanExe.Extract.ScalarFunc

open LeanExe.Extract.Core
open LeanExe.Source.Scalar

run_elab do
  let word : Lean.Expr := .const ``UInt64 []
  let boolean : Lean.Expr := .const ``Bool []
  let functionType := Lean.Expr.forallE `x word (.forallE `y word word .default) .default
  let wrap (body : Lean.Expr) := Lean.Expr.lam `x word (.lam `y word body .default) .default
  let toWord (body : Lean.Expr) := Lean.Expr.app (.const ``Bool.toUInt64 []) body
  let add (left right : Lean.Expr) := Lean.Expr.app (.app (.const ``UInt64.add []) left) right
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
      for negations in [0, 1, 2, 3] do
        for form in [BooleanChoiceForm.ordinary, .dependent ⟨`yesProof, `noProof, binder, binder⟩] do
          for unequal in [false, true] do
            let call (argument : Lean.Expr) := toWord
              (form.local negations unequal
                (.predicate negations 0 argument) (.literal 0 false)
                (.predicate (negations + 1) 0 (BooleanGuardNegation.expr 1 argument))
                (.predicate 0 0 (booleanLiteralExpr true))).expr
            for nondep in [false, true] do
              for flag in [false, true] do
                let helperBody : BooleanLocal := .junction 0 .conjunction
                  (.var 0 0) (.compare .eq (.bvar 2) (.bvar 1))
                let argument : BooleanLocal := .compare .ne (.bvar 2) (literalExpr 0)
                let literal := booleanLiteralExpr flag
                let continuation := add (call argument.expr) (call literal)
                let helper (input result domain value body : Lean.Expr) :=
                  Lean.Expr.letE `predicate (.forallE `typeInput input result binder)
                    (.lam `valueInput domain value binder) body nondep
                let source := helper boolean bt.expr boolean helperBody.expr continuation
                let some func := extractScalarFunc `booleanPredicateSyntax (some "entry") functionType (wrap source) |
                  throwError "Boolean-input predicate compiler rejected syntax"
                let module_ : LeanExe.IR.Module := { funcs := #[func] }
                for (x, y) in inputs do
                  let base := fun b => b && x == y
                  let f := fun b => GuardNegation.denote negations
                    (if booleanRelationDecision unequal (GuardNegation.denote negations (base b)) false
                     then GuardNegation.denote (negations + 1) (base (!b)) else base true)
                  let expected := (f (x != 0)).toUInt64 + (f flag).toUInt64
                  let actual := module_.evalFunc 0 [x, y]
                  unless actual == expected do throwError "Boolean-input predicate result {actual}, expected {expected}"
                  comparisons := comparisons + 1
                let unused := helper boolean bt.expr boolean helperBody.expr
                  (.letE `unused boolean (.app (.bvar 0) literal) (literalExpr 0) false)
                unless (extractScalarFunc `unusedBooleanLet (some "entry") functionType (wrap unused)).isSome do
                  throwError "valid unused Boolean let was rejected"
                controls := controls + 1
                let invalid : List Lean.Expr :=
                  [helper boolean bt.expr word helperBody.expr continuation,
                   helper word bt.expr boolean helperBody.expr continuation,
                   helper boolean (.const ``Nat []) boolean helperBody.expr continuation,
                   helper boolean word boolean helperBody.expr continuation,
                   helper boolean bt.expr boolean (.bvar 1) continuation,
                   helper boolean bt.expr boolean helperBody.expr (.bvar 0),
                   helper boolean bt.expr boolean helperBody.expr (call (.bvar 2)),
                   helper boolean bt.expr boolean helperBody.expr (call (literalExpr 0)),
                   helper boolean bt.expr boolean helperBody.expr (call (.bvar 0)),
                   helper boolean bt.expr boolean helperBody.expr (toWord (.bvar 0)),
                   helper boolean bt.expr boolean (.const `unsupportedPredicate []) (literalExpr 0),
                   helper boolean bt.expr boolean helperBody.expr (call (.const `unsupportedArgument [])),
                   helper boolean bt.expr boolean helperBody.expr
                     (toWord (.app (.bvar 1) literal)),
                   helper boolean bt.expr boolean (.app (.bvar 0) literal) (literalExpr 0)]
                for body in invalid do
                  if (extractScalarFunc `invalidBooleanPredicate (some "entry") functionType (wrap body)).isSome then
                    throwError "invalid Boolean-input predicate was admitted"
                  rejected := rejected + 1
  unless comparisons == 3584 && rejected == 3584 && controls == 256 do
    throwError "unexpected counts {comparisons}, {rejected}"
  Lean.logInfo m!"{comparisons} native/Boolean-input predicate choice syntax comparisons and {rejected} invalid-input tests and {controls} admission controls passed"

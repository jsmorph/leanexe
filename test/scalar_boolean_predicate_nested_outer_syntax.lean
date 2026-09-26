import LeanExe.Extract.ScalarFunc

open LeanExe.Extract.Core
open LeanExe.Source.Scalar

run_elab do
  let word : Lean.Expr := .const ``UInt64 []
  let boolean : Lean.Expr := .const ``Bool []
  let functionType := Lean.Expr.forallE `count word (.forallE `seed word word .default) .default
  let wrap (body : Lean.Expr) := Lean.Expr.lam `count word (.lam `seed word body .default) .default
  let loop (body : Lean.Expr) := Range.call (.bvar 2) (.bvar 1) `i `a .default .default body
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
        for nesting in [1, 2, 4] do
          let call (argument : Lean.Expr) := toWord
            (BooleanGuardNegation.expr negations (.app (.bvar 2)
              ((List.range nesting).foldl (fun value _ =>
                BooleanGuardNegation.expr (negations + 1) (.app (.bvar 2) value)) argument)))
          for nondep in [false, true] do
            for flag in [false, true] do
              let helperBody : BooleanLocal := .junction 0 .conjunction
                (.var 0 0) (.compare .ne (.bvar 1) (literalExpr 0))
              let indexWord : Lean.Expr := .app (.const ``UInt64.ofNat []) (.bvar 1)
              let argument : BooleanLocal := .compare .eq indexWord (.bvar 3)
              let literal := booleanLiteralExpr flag
              let continuation := Step.branch .eq .word (call argument.expr) (literalExpr 1)
                (Step.doneDirect (add (add (.bvar 0) (call literal)) (literalExpr 7)))
                (Step.yieldDirect (add (add (add (.bvar 0) indexWord) (call literal)) (literalExpr 1)))
              let helper (input result domain value body : Lean.Expr) :=
                Lean.Expr.letE `predicate (.forallE `typeInput input result binder)
                  (.lam `valueInput domain value binder) (loop body) nondep
              let source := helper boolean bt.expr boolean helperBody.expr continuation
              let some func := extractScalarFunc `booleanPredicateOuterSyntax (some "entry") functionType (wrap source) |
                throwError "Boolean-input predicate compiler rejected syntax"
              let module_ : LeanExe.IR.Module := { funcs := #[func] }
              for (count, seed) in inputs do
                let expected := forIn (m := Id) [:count.toNat] seed fun i a =>
                  let base := fun b => b && seed != 0
                  let f := fun b => GuardNegation.denote negations
                    (base ((List.range nesting).foldl (fun value _ =>
                      GuardNegation.denote (negations + 1) (base value)) b))
                  if f (UInt64.ofNat i == seed) then .done (a + (f flag).toUInt64 + 7)
                  else .yield (a + UInt64.ofNat i + (f flag).toUInt64 + 1)
                let actual := module_.evalFunc 0 [count, seed]
                unless actual == expected do throwError "outer Boolean-input predicate result {actual}, expected {expected}"
                comparisons := comparisons + 1
              let invalid : List Lean.Expr :=
                [helper boolean bt.expr word helperBody.expr continuation,
                 helper word bt.expr boolean helperBody.expr continuation,
                 helper boolean (.const ``Nat []) boolean helperBody.expr continuation,
                 helper boolean word boolean helperBody.expr continuation,
                 helper boolean bt.expr boolean (.bvar 1) continuation,
                 helper boolean bt.expr boolean helperBody.expr (Step.yieldDirect (.bvar 2)),
                 helper boolean bt.expr boolean helperBody.expr (Step.yieldDirect (call (.bvar 0))),
                 helper boolean bt.expr boolean helperBody.expr (Step.yieldDirect (call (literalExpr 0))),
                 helper boolean bt.expr boolean helperBody.expr (Step.yieldDirect (call (.bvar 2))),
                 helper boolean bt.expr boolean helperBody.expr (Step.yieldDirect (toWord (.bvar 2))),
                 helper boolean bt.expr boolean (.const `unsupportedPredicate []) (Step.yieldDirect (.bvar 0)),
                 helper boolean bt.expr boolean helperBody.expr (Step.yieldDirect (call (.const `unsupportedArgument []))),
                 helper boolean bt.expr boolean helperBody.expr
                   (Step.yieldDirect (toWord (.app (.bvar 0) literal))),
                 helper boolean bt.expr boolean helperBody.expr
                   (.letE `unused boolean (.app (.bvar 2) literal) (Step.yieldDirect (.bvar 0)) false),
                 helper boolean bt.expr boolean (.app (.bvar 0) literal) (Step.yieldDirect (.bvar 0))]
              for body in invalid do
                if (extractScalarFunc `invalidBooleanPredicateOuter (some "entry") functionType (wrap body)).isSome then
                  throwError "invalid Boolean-input predicate was admitted"
                rejected := rejected + 1
  unless comparisons == 4608 && rejected == 2880 do
    throwError "unexpected counts {comparisons}, {rejected}"
  Lean.logInfo m!"{comparisons} native/outer Boolean-input predicate nested-call syntax comparisons and {rejected} invalid-input tests passed"

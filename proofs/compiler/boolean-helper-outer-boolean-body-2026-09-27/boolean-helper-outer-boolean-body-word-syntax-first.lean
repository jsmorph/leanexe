import LeanExe.Extract.ScalarFunc

open LeanExe.Extract.Core
open LeanExe.Source.Scalar

run_elab do
  let word : Lean.Expr := .const ``UInt64 []
  let boolean : Lean.Expr := .const ``Bool []
  let functionType := Lean.Expr.forallE `count word (.forallE `seed word boolean .default) .default
  let wrap (body : Lean.Expr) := Lean.Expr.lam `count word (.lam `seed word body .default) .default
  let loop (body : Lean.Expr) := Lean.Expr.letE `value word
    (Range.call (.bvar 2) (.bvar 1) `i `a .default .default body)
    (BooleanLocal.compare .eq (.bvar 0) (.bvar 2)).expr false
  let toWord (body : Lean.Expr) := Lean.Expr.app (.const ``Bool.toUInt64 []) body
  let add (a b : Lean.Expr) := Lean.Expr.app (.app (.const ``UInt64.add []) a) b
  let inputs : List (UInt64 × UInt64) :=
    ([0, 1, 2, 7, 16, 31] : List UInt64).flatMap fun n =>
      ([0, 1, 0x8000000000000000, 0xffffffffffffffff] : List UInt64).map fun seed => (n, seed)
  let mut comparisons : Nat := 0
  let mut rejected : Nat := 0
  for binder in [Lean.BinderInfo.default, .implicit, .strictImplicit, .instImplicit] do
    for depth in [0, 1, 3] do
      let bt := (List.range depth).foldl (fun t _ => BooleanType.identity t) .boolean
      for negations in [0, 1, 2] do
        for nondep in [false, true] do
          let helperBody : BooleanLocal := .compare .eq (.bvar 0) (.bvar 1)
          let indexWord : Lean.Expr := .app (.const ``UInt64.ofNat []) (.bvar 1)
          let calls : BooleanLocal := .junction 0 .disjunction
            (.predicate negations 2 (.bvar 0)) (.predicate negations 2 indexWord)
          let guard : BooleanLocalGuard := { value := calls, expanded := rfl }
          let branches := guard.branch (Step.resultType .word)
            (Step.doneDirect (add (.bvar 0) (literalExpr 7)))
            (Step.yieldDirect (add (add (.bvar 0) indexWord) (literalExpr 1)))
          let helper (input result domain value body : Lean.Expr) :=
            Lean.Expr.letE `predicate (.forallE `typeInput input result binder)
              (.lam `valueInput domain value binder) (loop body) nondep
          let innerShape : BooleanFunctionBinding := ⟨`g, `arg, binder, binder, bt, nondep⟩
          let innerTail := Lean.Expr.app (.app (.const ``Bool.or []) (.app (.bvar 0) (booleanLiteralExpr false))) (.app (.bvar 0) (booleanLiteralExpr true))
          let nested (rawBody : Lean.Expr) := booleanHelperExpr true innerShape `arg rawBody innerTail
          let nestedBody := nested (helperBody.expr.liftLooseBVars 0 1)
          let source := helper word bt.expr word nestedBody branches
          let some func := extractScalarFunc `outerPredicateSyntax (some "entry") functionType (wrap source) |
            throwError "outer predicate helper compiler rejected syntax"
          let module_ : LeanExe.IR.Module := { funcs := #[func] }
          for (count, seed) in inputs do
            let expected := forIn (m := Id) [:count.toNat] seed fun i a =>
              if GuardNegation.denote negations (a == seed) ||
                  GuardNegation.denote negations (UInt64.ofNat i == seed) then .done (a + 7)
              else .yield (a + UInt64.ofNat i + 1)
            let actual := module_.evalFunc 0 [count, seed]
            unless actual == (expected == seed).toUInt64 do throwError "outer predicate result {actual}, expected {expected}"
            comparisons := comparisons + 1
          let unused := helper word bt.expr word nestedBody (Step.yieldDirect (add (.bvar 0) (literalExpr 1)))
          let some unusedFunc := extractScalarFunc `validUnused (some "entry") functionType (wrap unused) |
            throwError "valid unused outer predicate rejected"
          let unusedModule : LeanExe.IR.Module := { funcs := #[unusedFunc] }
          for (count, seed) in inputs do
            unless unusedModule.evalFunc 0 [count, seed] == (seed + count == seed).toUInt64 do
              throwError "unused outer predicate changes loop result"
            comparisons := comparisons + 1
          let invalid : List Lean.Expr :=
            [helper word bt.expr boolean nestedBody branches,
             helper boolean bt.expr word nestedBody branches,
             helper word (.const ``Nat []) word nestedBody branches,
             helper word word word nestedBody branches,
             helper word bt.expr word (.bvar 0) branches,
             helper word bt.expr word nestedBody (Step.yieldDirect (.bvar 2)),
             helper word bt.expr word nestedBody
               (Step.yieldDirect (toWord (.app (.bvar 2) (.const ``Bool.true [])))),
             helper word bt.expr word nestedBody (Step.yieldDirect (toWord (.bvar 2))),
             helper word bt.expr word (.app (.bvar 0) (.bvar 1)) (Step.yieldDirect (.bvar 0)),
             helper word bt.expr word (.const `unsupportedPredicate []) (Step.yieldDirect (.bvar 0)),
             helper word bt.expr word nestedBody
               (Step.yieldDirect (toWord (.app (.bvar 2) (.const `unsupportedArgument [])))),
             helper word bt.expr word nestedBody
               (Step.yieldDirect (toWord (.app (.bvar 0) (.bvar 3)))),
           helper word bt.expr word (nested (.const `unsupportedNestedPredicate [])) (Step.yieldDirect (.bvar 0)),
           helper word bt.expr word (nested (.bvar 9)) (Step.yieldDirect (.bvar 0)),
           helper word bt.expr word (nested (literalExpr 0)) (Step.yieldDirect (.bvar 0)),
           helper word bt.expr word (nested (.const `unsupportedNestedPredicate [])) branches]
          for body in invalid do
            if (extractScalarFunc `invalidOuterPredicate (some "entry") functionType (wrap body)).isSome then
              throwError "invalid outer predicate helper was admitted"
            rejected := rejected + 1
  unless comparisons == 3456 && rejected == 1152 do
    throwError "unexpected counts {comparisons}, {rejected}"
  Lean.logInfo m!"{comparisons} native/Boolean-result outer word-input body syntax comparisons and {rejected} invalid-input tests passed"

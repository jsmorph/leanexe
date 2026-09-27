import LeanExe.Extract.ScalarFunc

open LeanExe.Extract.Core
open LeanExe.Source.Scalar

run_elab do
  let word : Lean.Expr := .const ``UInt64 []
  let boolean : Lean.Expr := .const ``Bool []
  let functionType := Lean.Expr.forallE `count word (.forallE `seed word word .default) .default
  let wrap (body : Lean.Expr) := Lean.Expr.lam `count word (.lam `seed word
    (Range.call (.bvar 1) (.bvar 0) `i `a .default .default body) .default) .default
  let toWord (body : Lean.Expr) := Lean.Expr.app (.const ``Bool.toUInt64 []) body
  let add (a b : Lean.Expr) := Lean.Expr.app (.app (.const ``UInt64.add []) a) b
  let inputs : List (UInt64 × UInt64) :=
    ([0, 1, 2, 7, 16, 31] : List UInt64).flatMap fun n =>
      ([0, 1, 0x8000000000000000, 0xffffffffffffffff] : List UInt64).map fun seed => (n, seed)
  let mut comparisons : Nat := 0
  let mut rejected : Nat := 0
  for binder in [Lean.BinderInfo.default, .implicit, .strictImplicit, .instImplicit] do
    for inputDepth in [1, 3] do
      for depth in [0, 1, 3] do
        let wt := (List.range inputDepth).foldl (fun t _ => ResultType.identity t) .word
        let bt := (List.range depth).foldl (fun t _ => BooleanType.identity t) .boolean
        for negations in [0, 1, 2] do
          for nondep in [false, true] do
            let helperBody : BooleanLocal := .compare .eq (.bvar 0) (.bvar 3)
            let indexWord : Lean.Expr := .app (.const ``UInt64.ofNat []) (.bvar 2)
            let calls : BooleanLocal := .junction 0 .disjunction
              (.predicate negations 0 (.bvar 1)) (.predicate negations 0 indexWord)
            let guard : BooleanLocalGuard := { value := calls, expanded := rfl }
            let branches := guard.branch (Step.resultType .word)
              (Step.doneDirect (add (.bvar 1) (literalExpr 7)))
              (Step.yieldDirect (add (add (.bvar 1) indexWord) (literalExpr 1)))
            let helper (input result domain value body : Lean.Expr) :=
              Lean.Expr.letE `predicate (.forallE `typeInput input result binder)
                (.lam `valueInput domain value binder) body nondep
            let source := helper wt.expr bt.expr wt.expr helperBody.expr branches
            let some func := extractScalarFunc `predicateInputStepSyntax (some "entry") functionType (wrap source) |
              throwError "reusable step helper compiler rejected syntax"
            let module_ : LeanExe.IR.Module := { funcs := #[func] }
            for (count, seed) in inputs do
              let expected := forIn (m := Id) [:count.toNat] seed fun i a =>
                if GuardNegation.denote negations (a == seed) ||
                    GuardNegation.denote negations (UInt64.ofNat i == seed) then .done (a + 7)
                else .yield (a + UInt64.ofNat i + 1)
              let actual := module_.evalFunc 0 [count, seed]
              unless actual == expected do throwError "reusable step result {actual}, expected {expected}"
              comparisons := comparisons + 1
            let invalid : List Lean.Expr :=
              [helper wt.expr bt.expr word helperBody.expr branches,
               helper word bt.expr wt.expr helperBody.expr branches,
               helper wt.expr bt.expr (ResultType.identity wt).expr helperBody.expr branches,
               helper (.app (.const ``Id [.zero]) (.const ``Nat [])) bt.expr
                 (.app (.const ``Id [.zero]) (.const ``Nat [])) helperBody.expr branches,
               helper wt.expr word wt.expr helperBody.expr branches,
               helper word bt.expr boolean helperBody.expr branches,
               helper boolean bt.expr word helperBody.expr branches,
               helper word (.const ``Nat []) word helperBody.expr branches,
               helper word word word helperBody.expr branches,
               helper word bt.expr word (.bvar 0) branches,
               helper word bt.expr word helperBody.expr (Step.yieldDirect (.bvar 0)),
               helper word bt.expr word helperBody.expr
                 (Step.yieldDirect (toWord (.app (.bvar 0) (.const ``Bool.true [])))),
               helper word bt.expr word helperBody.expr (Step.yieldDirect (toWord (.bvar 0))),
               helper word bt.expr word (.app (.bvar 0) (.bvar 1)) (Step.yieldDirect (.bvar 1)),
               helper word bt.expr word (.const `unsupportedPredicate []) (Step.yieldDirect (.bvar 1)),
               helper word bt.expr word helperBody.expr
                 (Step.yieldDirect (toWord (.app (.bvar 0) (.const `unsupportedArgument [])))),
               helper word bt.expr word helperBody.expr
                 (Step.yieldDirect (toWord (.app (.bvar 1) (.bvar 3))))]
            for body in invalid do
              if (extractScalarFunc `invalidReusableStep (some "entry") functionType (wrap body)).isSome then
                throwError "invalid reusable step helper was admitted"
              rejected := rejected + 1
  unless comparisons == 3456 && rejected == 2448 do
    throwError "unexpected counts {comparisons}, {rejected}"
  Lean.logInfo m!"{comparisons} native/predicate-input step syntax comparisons and {rejected} invalid-input tests passed"

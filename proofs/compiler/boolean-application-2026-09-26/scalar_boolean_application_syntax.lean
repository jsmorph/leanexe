import LeanExe.Extract.ScalarFunc

open LeanExe.Extract.Core
open LeanExe.Source.Scalar

run_elab do
  let word : Lean.Expr := .const ``UInt64 []
  let boolean : Lean.Expr := .const ``Bool []
  let functionType := Lean.Expr.forallE `x word (.forallE `y word word .default) .default
  let wrap (body : Lean.Expr) := Lean.Expr.lam `x word (.lam `y word
    (.app (.const ``Bool.toUInt64 []) body) .default) .default
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
      let wt := (List.range depth).foldl (fun t _ => ResultType.identity t) .word
      let bt := (List.range depth).foldl (fun t _ => BooleanType.identity t) .boolean
      for negations in [0, 1, 2] do
        let argument : BooleanLocal := .compare .eq (.bvar 1) (.bvar 0)
        let wordBody : BooleanLocal := .compare .eq (.bvar 0) (.bvar 1)
        let boolBody : BooleanLocal := .junction 0 .disjunction (.var 1 0)
          (.compare .eq (.bvar 2) (.bvar 1))
        let values : List (BooleanLocal × (UInt64 → UInt64 → Bool)) :=
          [(.wordBinding negations `n (.application binder) (.bvar 1) wordBody wt,
            fun x y => GuardNegation.denote negations (x == y)),
           (.binding negations `flag (.application binder) argument boolBody bt,
            fun _ _ => GuardNegation.denote negations true)]
        for (value, native) in values do
          let some parsed := booleanLocalOperands? value.expr | throwError "application parser rejected syntax"
          unless LeanExe.Source.ExprEquality.same parsed.expr value.expr do
            throwError "application parser changed source syntax"
          let some func := extractScalarFunc `applicationSyntax (some "entry") functionType (wrap value.expr) |
            throwError "application compiler rejected syntax"
          let module_ : LeanExe.IR.Module := { funcs := #[func] }
          for (x, y) in inputs do
            let expected := (native x y).toUInt64
            let actual := module_.evalFunc 0 [x, y]
            unless actual == expected do throwError "application result {actual}, expected {expected}"
            comparisons := comparisons + 1
        -- Domains and lexical value kinds are checked before lowering.
        let invalid : List Lean.Expr :=
          [ .app (.lam `n (.const ``Nat []) wordBody.expr binder) (.bvar 1),
            .app (.lam `flag boolean (.bvar 0) binder) (.bvar 1),
            .app (.lam `n word (.bvar 0) binder) (.bvar 1),
            .app (.lam `n word wordBody.expr binder) (.const ``Bool.true []),
            .app (.lam `n word (.const ``UInt64.add []) binder) (.bvar 1),
            .app (.lam `flag boolean (.bvar 3) binder) argument.expr ]
        for body in invalid do
          if (extractScalarFunc `invalidApplication (some "entry") functionType (wrap body)).isSome then
            throwError "invalid application was admitted"
          rejected := rejected + 1
  unless comparisons == 1008 && rejected == 216 do
    throwError "unexpected counts {comparisons}, {rejected}"
  Lean.logInfo m!"{comparisons} native/Boolean-application syntax comparisons and {rejected} invalid-input tests passed"

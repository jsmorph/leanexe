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
        for wordInput in [false, true] do
          let input := if wordInput then word else boolean
          let other := if wordInput then boolean else word
          for wrapper in [none, some (BooleanWrapper.pure bt), some (.run bt), some (.metadata {})] do
            let action (value : Lean.Expr) := match wrapper with
              | none => value
              | some wrapper => wrapper.expr value
            for nondep in [false, true] do
              for flag in [false, true] do
                let outerBody : BooleanLocal := .junction 0 .conjunction
                  (.var 0 0) (.compare .eq (.bvar 2) (.bvar 1))
                let outer (body : Lean.Expr) := Lean.Expr.letE `f
                  (.forallE `arg boolean bt.expr binder) (.lam `arg boolean outerBody.expr binder) body nondep
                let innerArgument := if wordInput then (BooleanLocal.compare .eq (.bvar 0) (.bvar 2)).expr else .bvar 0
                let innerBody := action (BooleanGuardNegation.expr negations (.app (.bvar 1) innerArgument))
                let inner (inputType domain result value body : Lean.Expr) := outer (.letE `g
                  (.forallE `arg inputType result binder) (.lam `arg domain value binder) body nondep)
                let firstArgument := if wordInput then Lean.Expr.bvar 3 else
                  (BooleanLocal.compare .ne (.bvar 3) (literalExpr 0)).expr
                let secondArgument := if wordInput then literalExpr flag.toUInt64.toNat else booleanLiteralExpr flag
                let continuation := add (toWord (.app (.bvar 0) firstArgument))
                  (toWord (.app (.bvar 0) secondArgument))
                let source := inner input input bt.expr innerBody continuation
                let some func := extractScalarFunc `predicateResult (some "entry") functionType (wrap source) |
                  throwError "direct Boolean helper result rejected"
                let module_ : LeanExe.IR.Module := { funcs := #[func] }
                for (x, y) in inputs do
                  let f := fun b => GuardNegation.denote negations (b && x == y)
                  let expected := (f (if wordInput then x == y else x != 0)).toUInt64 +
                    (f (if wordInput then flag.toUInt64 == y else flag)).toUInt64
                  let actual := module_.evalFunc 0 [x, y]
                  unless actual == expected do throwError "direct Boolean helper {actual}, expected {expected}"
                  comparisons := comparisons + 1
                unless (extractScalarFunc `unusedResult (some "entry") functionType
                    (wrap (inner input input bt.expr innerBody (literalExpr 0)))).isSome do
                  throwError "valid unused Boolean helper rejected"
                controls := controls + 1
                for source in [inner input other bt.expr innerBody continuation,
                    inner other input bt.expr innerBody continuation,
                    inner input input word innerBody continuation,
                    inner input input (.const ``Nat []) innerBody continuation,
                    inner input input bt.expr (.const `unsupportedResult []) continuation,
                    inner input input bt.expr (.bvar 1) continuation,
                    inner input input bt.expr (.app (.bvar 0) (booleanLiteralExpr true)) continuation,
                    inner input input bt.expr (.app (.bvar 1) (literalExpr 0)) continuation,
                    inner input input bt.expr (.const `unsupportedUnusedResult []) (literalExpr 0),
                    inner input input bt.expr innerBody (toWord (.bvar 0))] do
                  unless (extractScalarFunc `invalidResult (some "entry") functionType (wrap source)).isNone do
                    throwError "invalid Boolean helper declaration/body admitted"
                  rejected := rejected + 1
  unless comparisons == 7168 && rejected == 5120 && controls == 512 do
    throwError "unexpected counts {comparisons}, {rejected}, {controls}"
  Lean.logInfo m!"{comparisons} native/direct Boolean helper IR comparisons, {rejected} invalid-input tests and {controls} admission controls passed"

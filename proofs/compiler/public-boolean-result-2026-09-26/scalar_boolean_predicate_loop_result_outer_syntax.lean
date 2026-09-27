import LeanExe.Extract.ScalarFunc

open LeanExe.Extract.Core
open LeanExe.Source.Scalar

run_elab do
  let word : Lean.Expr := .const ``UInt64 []
  let boolean : Lean.Expr := .const ``Bool []
  let functionType := Lean.Expr.forallE `count word (.forallE `seed word word .default) .default
  let wrap (body : Lean.Expr) := Lean.Expr.lam `count word (.lam `seed word
    body .default) .default
  let toWord (body : Lean.Expr) := Lean.Expr.app (.const ``Bool.toUInt64 []) body
  let add (left right : Lean.Expr) := Lean.Expr.app (.app (.const ``UInt64.add []) left) right
  let inputs : List (UInt64 × UInt64) :=
    ([0, 1, 2, 7, 16, 31] : List UInt64).flatMap fun n =>
      ([0, 1, 0x8000000000000000, 0xffffffffffffffff] : List UInt64).map fun seed => (n, seed)
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
                  (.var 0 0) (.compare .ne (.bvar 1) (literalExpr 0))
                let outer (body : Lean.Expr) := Lean.Expr.letE `f
                  (.forallE `arg boolean bt.expr binder) (.lam `arg boolean outerBody.expr binder) body nondep
                let innerArgument := if wordInput then (BooleanLocal.compare .eq (.bvar 0) (.bvar 2)).expr else .bvar 0
                let innerBody := action (BooleanGuardNegation.expr negations (.app (.bvar 1) innerArgument))
                let inner (inputType domain result value body : Lean.Expr) := outer (.letE `g
                  (.forallE `arg inputType result binder) (.lam `arg domain value binder) body nondep)
                let argument := if wordInput then (if flag then Lean.Expr.bvar 4 else literalExpr 0) else booleanLiteralExpr flag
                let indexWord : Lean.Expr := .app (.const ``UInt64.ofNat []) (.bvar 1)
                let stepBody := Step.branch .eq .word (toWord (.app (.bvar 2) argument)) (literalExpr 1)
                  (Step.doneDirect (add (.bvar 0) (literalExpr 7)))
                  (Step.yieldDirect (add (add (.bvar 0) indexWord) (literalExpr 1)))
                let continuation := (Range.call (.bvar 3) (.bvar 2) `i `a .default .default stepBody)
                let unused := (Range.call (.bvar 3) (.bvar 2) `i `a .default .default (Step.yieldDirect (literalExpr 0)))
                let source := inner input input bt.expr innerBody continuation
                let some func := extractScalarFunc `predicateLoopResult (some "entry") functionType (wrap source) |
                  throwError "direct outer Boolean helper result rejected"
                let module_ : LeanExe.IR.Module := { funcs := #[func] }
                for (count, seed) in inputs do
                  let expected := forIn (m := Id) [:count.toNat] seed fun i a =>
                    let flag := if wordInput then ((if flag then seed else 0) == seed) else flag
                    let result := GuardNegation.denote negations (flag && seed != 0)
                    if result then .done (a + 7) else .yield (a + UInt64.ofNat i + 1)
                  let actual := module_.evalFunc 0 [count, seed]
                  unless actual == expected do throwError "direct outer Boolean helper {actual}, expected {expected}"
                  comparisons := comparisons + 1
                unless (extractScalarFunc `unusedResult (some "entry") functionType
                    (wrap (inner input input bt.expr innerBody unused))).isSome do
                  throwError "valid unused outer Boolean helper rejected"
                controls := controls + 1
                for source in [inner input other bt.expr innerBody continuation,
                    inner other input bt.expr innerBody continuation,
                    inner input input word innerBody continuation,
                    inner input input (.const ``Nat []) innerBody continuation,
                    inner input input bt.expr (.const `unsupportedResult []) continuation,
                    inner input input bt.expr (.bvar 1) continuation,
                    inner input input bt.expr (.app (.bvar 0) (booleanLiteralExpr true)) continuation,
                    inner input input bt.expr (.app (.bvar 1) (literalExpr 0)) continuation,
                    inner input input bt.expr (.const `unsupportedUnusedResult []) unused] do
                  unless (extractScalarFunc `invalidResult (some "entry") functionType (wrap source)).isNone do
                    throwError "invalid outer Boolean helper declaration/body admitted"
                  rejected := rejected + 1
  unless comparisons == 12288 && rejected == 4608 && controls == 512 do
    throwError "unexpected counts {comparisons}, {rejected}, {controls}"
  Lean.logInfo m!"{comparisons} native/direct outer Boolean helper IR comparisons, {rejected} invalid-input tests and {controls} admission controls passed"

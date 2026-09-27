import LeanExe.Extract.ScalarFunc

open LeanExe.Extract.Core
open LeanExe.Source.Scalar

run_elab do
  let word : Lean.Expr := .const ``UInt64 []
  let boolean : Lean.Expr := .const ``Bool []
  let nat : Lean.Expr := .const ``Nat []
  let functionType := Lean.Expr.forallE `count word (.forallE `seed word boolean .default) .default
  let wrap (body : Lean.Expr) := Lean.Expr.lam `count word (.lam `seed word body .default) .default
  let negate (body : Lean.Expr) := Lean.Expr.app (.const ``Bool.not []) body
  let indexWord : Lean.Expr := .app (.const ``UInt64.ofNat []) (.bvar 1)
  let inputs : List (UInt64 × UInt64) :=
    ([0, 1, 2, 7, 16, 31] : List UInt64).flatMap fun count =>
      ([0, 1, 0x8000000000000000, 0xffffffffffffffff] : List UInt64).map fun seed => (count, seed)
  let mut comparisons := 0
  let mut rejected := 0
  for binder in [Lean.BinderInfo.default, .implicit, .strictImplicit, .instImplicit] do
    for depth in [0, 1, 3] do
      let bt := (List.range depth).foldl (fun t _ => BooleanType.identity t) .boolean
      let wt := (List.range depth).foldl (fun t _ => ResultType.identity t) .word
      for nondep in [false, true] do
        for stride in ([⟨1, by decide, by decide, .const ``Nat.zero_lt_one []⟩,
            ⟨3, by decide, by decide, .app (.const ``Nat.zero_lt_succ []) (Range.natLiteral 2)⟩] : List Range.Exit.Stride) do
          for start in ([0, 2] : List Nat) do
            let first : Range.Exit.Count := if start == 0 then .literal 0 (by decide) else .literal 2 (by decide)
            let count : Range.Exit.Count := .word (.bvar 1)
            let initial := (BooleanLocal.compare .eq (.bvar 0) (literalExpr 0)).expr
            let make (initial body : Lean.Expr) := BooleanAccumulator.call ⟨nat, rfl⟩ stride first count initial `index `flag binder binder body
            for mode in List.range 6 do
              let test := Comparison.eq.condition indexWord (.bvar 2)
              let evidence := Comparison.eq.evidence indexWord (.bvar 2)
              let body := match mode with
                | 0 => BooleanStep.yieldDirect (negate (.bvar 0))
                | 1 => BooleanStep.doneDirect (negate (.bvar 0))
                | 2 => BooleanStep.choiceExpr bt test evidence
                    (BooleanStep.doneDirect (negate (.bvar 0))) (BooleanStep.yieldDirect (.bvar 0))
                | 3 => Lean.Expr.letE `next bt.expr (negate (.bvar 0)) (BooleanStep.yieldDirect (.bvar 0)) nondep
                | 4 => Lean.Expr.letE `index wt.expr indexWord
                    (BooleanStep.yieldDirect (BooleanLocal.compare .eq (.bvar 0) (.bvar 3)).expr) nondep
                | _ => Lean.Expr.mdata {} (BooleanStep.idRun bt (BooleanStep.idPure bt (BooleanStep.yieldDirect (negate (.bvar 0)))))
              let source := make initial body
              let some func := extractScalarFunc `booleanAccumulatorSyntax (some "entry") functionType (wrap source) |
                throwError "Boolean accumulator syntax rejected: mode {mode}, depth {depth}"
              let module_ : LeanExe.IR.Module := { funcs := #[func] }
              for (count, seed) in inputs do
                let range : Std.Legacy.Range := ⟨start, count.toNat, stride.number, stride.positive⟩
                let expected : Bool := Id.run <| forIn (m := Id) range (seed == 0) fun i flag =>
                  match mode with
                  | 0 => .yield (!flag)
                  | 1 => .done (!flag)
                  | 2 => if UInt64.ofNat i == seed then .done (!flag) else .yield flag
                  | 3 => .yield (!flag)
                  | 4 => .yield (UInt64.ofNat i == seed)
                  | _ => .yield (!flag)
                let actual := module_.evalFunc 0 [count, seed]
                unless actual == expected.toUInt64 do
                  throwError "mode {mode}, start {start}, stride {stride.number}, count {count}, seed {seed}: {actual} != {expected}"
                comparisons := comparisons + 1
              let invalidSteps : List Lean.Expr := [
                BooleanStep.yieldDirect (literalExpr 0),
                BooleanStep.doneDirect (.bvar 1),
                Step.yieldDirect (literalExpr 0),
                BooleanStep.yieldDirect (.bvar 9),
                .letE `unused word (booleanLiteralExpr true) body nondep,
                .letE `unused boolean (literalExpr 0) body nondep,
                BooleanStep.choiceExpr bt (Comparison.eq.condition (literalExpr 0) (literalExpr 0))
                  (Comparison.eq.evidence (literalExpr 0) (literalExpr 0)) body (.const `unsupportedStep []),
                .app (.app (.const ``Id.run [.zero]) (Step.resultType .word)) body]
              for invalid in invalidSteps do
                if (extractScalarFunc `invalidStep none functionType (wrap (make initial invalid))).isSome then
                  throwError "invalid step admitted"
                rejected := rejected + 1
              for invalid in [make (literalExpr 0) body,
                  make (.const `unsupportedInitial []) body,
                  BooleanAccumulator.call ⟨nat, rfl⟩ stride first (.literal 0 (by decide)) (.const `unsupportedInitial []) `i `a binder binder body] do
                if (extractScalarFunc `invalidInitial none functionType (wrap invalid)).isSome then
                  throwError "invalid initial value admitted"
                rejected := rejected + 1
              let badHead := Lean.mkAppN (.const `customForIn []) #[count.range first stride.number stride.evidence, initial,
                .lam `i nat (.lam `flag boolean body binder) binder]
              if (extractScalarFunc `invalidHead none functionType (wrap badHead)).isSome then
                throwError "custom ForIn head admitted"
              rejected := rejected + 1
  unless comparisons == 13824 && rejected == 6912 do
    throwError "unexpected counts: {comparisons}, {rejected}"
  Lean.logInfo m!"{comparisons} native/Boolean accumulator syntax comparisons and {rejected} invalid-input tests passed"

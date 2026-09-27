import LeanExe.Extract.ScalarFunc

open LeanExe.Extract.Core
open LeanExe.Source.Scalar

run_elab do
  let word : Lean.Expr := .const ``UInt64 []
  let boolean : Lean.Expr := .const ``Bool []
  let nat : Lean.Expr := .const ``Nat []
  let functionType := Lean.Expr.forallE `count word (.forallE `seed word boolean .default) .default
  let wrap (body : Lean.Expr) := Lean.Expr.lam `count word (.lam `seed word body .default) .default
  let add (a b : Lean.Expr) := Lean.Expr.app (.app (.const ``UInt64.add []) a) b
  let modWord (a b : Lean.Expr) := Lean.Expr.app (.app (.const ``UInt64.mod []) a) b
  let indexWord : Lean.Expr := .app (.const ``UInt64.ofNat []) (.bvar 1)
  let stride : Range.Exit.Stride := ⟨1, by decide, by decide, .const ``Nat.zero_lt_one []⟩
  let first : Range.Exit.Count := .literal 0 (by decide)
  let initial := (BooleanLocal.compare .eq (.bvar 0) (literalExpr 0)).expr
  let loop (count : Range.Exit.Count) (step : Lean.Expr) :=
    BooleanAccumulator.call ⟨nat, rfl⟩ stride first count initial `i `flag .default .default step
  let inputs : List (UInt64 × UInt64) :=
    ([0, 1, 2, 7, 16, 31] : List UInt64).flatMap fun count =>
      ([0, 1, 0x8000000000000000, 0xffffffffffffffff] : List UInt64).map fun seed => (count, seed)
  let mut comparisons : Nat := 0
  let mut rejected : Nat := 0
  for binder in [Lean.BinderInfo.default, .implicit, .strictImplicit, .instImplicit] do
    for inputDepth in [0, 1, 3] do
      let bt := (List.range inputDepth).foldl (fun t _ => BooleanType.identity t) .boolean
      let wt := (List.range inputDepth).foldl (fun t _ => ResultType.identity t) .word
      for outputDepth in [0, 1, 3] do
        let output := (List.range outputDepth).foldl (fun t _ => BooleanType.identity t) .boolean
        for flagInput in [false, true] do
          let input := if flagInput then bt.expr else wt.expr
          let opposite := if flagInput then wt.expr else bt.expr
          let raw := if flagInput then (BooleanLocal.compare .eq indexWord (.bvar 2)).expr
            else add indexWord (.bvar 2)
          let value := if flagInput then BooleanIdentity.pure raw bt else Identity.pure raw wt
          let bound := if flagInput then Lean.Expr.bvar 0
            else (BooleanLocal.compare .eq (modWord (.bvar 0) (literalExpr 3)) (literalExpr 0)).expr
          let next := booleanEqualityExpr true (.bvar 1) bound
          for wrapped in [false, true] do
            for mode in List.range 4 do
              let body := match mode with
                | 0 => BooleanStep.yieldDirect next
                | 1 => BooleanStep.doneDirect next
                | 2 => BooleanStep.choiceExpr output (booleanRelationCondition false bound (booleanLiteralExpr true))
                    (booleanRelationEvidence false bound (booleanLiteralExpr true))
                    (BooleanStep.doneDirect next) (BooleanStep.yieldDirect next)
                | _ => BooleanStep.yieldDirect (.bvar 1)
              let body := if wrapped then BooleanStep.idRun output (BooleanStep.idPure output body) else body
              let make (input domain result value body : Lean.Expr) := Lean.mkAppN (.const ``Bind.bind [.zero, .zero]) #[
                .const ``Id [.zero], .app (.app (.const ``Monad.toBind [.zero, .zero]) (.const ``Id [.zero]))
                  (.const ``Id.instMonad [.zero]), input, result, value, .lam `bound domain body binder]
              let step := make input input (BooleanStep.resultType output) value body
              let source := loop (.word (.bvar 1)) step
              let some func := extractScalarFunc `booleanStepBind (some "entry") functionType (wrap source) |
                throwError "Boolean step bind rejected: {flagInput}, {inputDepth}, {outputDepth}, {mode}"
              let module_ : LeanExe.IR.Module := { funcs := #[func] }
              for (count, seed) in inputs do
                let expected : Bool := Id.run <| forIn (m := Id) [:count.toNat] (seed == 0) fun i flag =>
                  let bound := if flagInput then UInt64.ofNat i == seed else (UInt64.ofNat i + seed) % 3 == 0
                  let next := flag != bound
                  match mode with
                  | 0 => .yield next
                  | 1 => .done next
                  | 2 => if bound then .done next else .yield next
                  | _ => .yield flag
                let actual := module_.evalFunc 0 [count, seed]
                unless actual == expected.toUInt64 do throwError "Boolean bind result {actual} != {expected}"
                comparisons := comparisons + 1
              let unsupported : Lean.Expr := .const `unsupportedBound []
              let invalid : List Lean.Expr := [
                make input opposite (BooleanStep.resultType output) value body,
                make opposite input (BooleanStep.resultType output) value body,
                make input (.app (.const ``Id [.zero]) input) (BooleanStep.resultType output) value body,
                make nat nat (BooleanStep.resultType output) value body,
                make input input word value body,
                make input input boolean value body,
                make input input (Step.resultType .word) value body,
                make input input (BooleanStep.resultType output) unsupported body,
                make input input (BooleanStep.resultType output) unsupported (BooleanStep.yieldDirect (.bvar 1)),
                make input input (BooleanStep.resultType output) (if flagInput then literalExpr 0 else booleanLiteralExpr true) body,
                make input input (BooleanStep.resultType output) value (BooleanStep.yieldDirect (.bvar 9)),
                Lean.mkAppN (.const ``Bind.bind [.zero, .zero]) #[.const ``Id [.zero], .const `customBind [],
                  input, BooleanStep.resultType output, value, .lam `bound input body binder]]
              for bad in invalid do
                if (extractScalarFunc `invalidBooleanStepBind none functionType (wrap (loop (.word (.bvar 1)) bad))).isSome then
                  throwError "invalid Boolean step bind admitted"
                rejected := rejected + 1
              if (extractScalarFunc `invalidEmptyBooleanStepBind none functionType
                  (wrap (loop (.literal 0 (by decide)) (make input input (BooleanStep.resultType output) unsupported body)))).isSome then
                throwError "invalid bind in empty range admitted"
              rejected := rejected + 1
  unless comparisons == 13824 && rejected == 7488 do
    throwError "unexpected counts: {comparisons}, {rejected}"
  Lean.logInfo m!"{comparisons} native/Boolean step bind syntax comparisons and {rejected} invalid-input tests passed"

import LeanExe.Extract.ScalarFunc

open LeanExe.Extract.Core
open LeanExe.Source.Scalar

run_elab do
  let word : Lean.Expr := .const ``UInt64 []
  let boolean : Lean.Expr := .const ``Bool []
  let nat : Lean.Expr := .const ``Nat []
  let functionType := Lean.Expr.forallE `count word (.forallE `seed word boolean .default) .default
  let wrap (body : Lean.Expr) := Lean.Expr.lam `count word (.lam `seed word body .default) .default
  let indexWord : Lean.Expr := .app (.const ``UInt64.ofNat []) (.bvar 1)
  let neg (value : Lean.Expr) := Lean.Expr.app (.const ``Bool.not []) value
  let stride : Range.Exit.Stride := ⟨1, by decide, by decide, .const ``Nat.zero_lt_one []⟩
  let loop (count : Range.Exit.Count) (step : Lean.Expr) :=
    BooleanAccumulator.call ⟨nat, rfl⟩ stride (.literal 0 (by decide)) count
      (BooleanLocal.compare .eq (.bvar 0) (literalExpr 0)).expr `i `flag .default .default step
  let inputs : List (UInt64 × UInt64) :=
    ([0, 1, 2, 7, 16, 31] : List UInt64).flatMap fun count =>
      ([0, 1, 0x8000000000000000, 0xffffffffffffffff] : List UInt64).map fun seed => (count, seed)
  let mut comparisons : Nat := 0
  let mut rejected : Nat := 0
  for binder in [Lean.BinderInfo.default, .implicit, .strictImplicit, .instImplicit] do
    for inputDepth in [0, 1, 3] do
      let input := (List.range inputDepth).foldl (fun t _ => BooleanType.identity t) .boolean
      for outputDepth in [0, 2] do
        let output := (List.range outputDepth).foldl (fun t _ => BooleanType.identity t) .boolean
        for nondep in [false, true] do
          for monadic in [false, true] do
            let make (type domain result value body : Lean.Expr) := if monadic then
              Lean.mkAppN (.const ``Bind.bind [.zero, .zero]) #[.const ``Id [.zero],
                .app (.app (.const ``Monad.toBind [.zero, .zero]) (.const ``Id [.zero])) (.const ``Id.instMonad [.zero]),
                type, result, value, .lam `saved domain body binder]
              else Lean.Expr.letE `saved type value body nondep
            for mode in List.range 4 do
              let condition := Comparison.eq.condition indexWord (.bvar 2)
              let evidence := Comparison.eq.evidence indexWord (.bvar 2)
              let value := BooleanStep.choiceExpr input condition evidence
                (BooleanStep.doneDirect (neg (.bvar 0))) (BooleanStep.yieldDirect (.bvar 0))
              let body := match mode with
                | 0 => Lean.Expr.bvar 0
                | 1 => BooleanStep.yieldDirect (.bvar 1)
                | 2 => Lean.Expr.letE `alias (BooleanStep.resultType input) (.bvar 0) (.bvar 0) nondep
                | _ => BooleanStep.functionExpr boolean output `f `typeArg `arg binder binder
                    (.bvar 1) (.app (.bvar 0) (booleanLiteralExpr false)) nondep
              for wrapped in [false, true] do
                let body := if wrapped then Lean.Expr.mdata {} (BooleanStep.idRun output (BooleanStep.idPure output body)) else body
                let step := make (BooleanStep.resultType input) (BooleanStep.resultType input)
                  (BooleanStep.resultType output) value body
                let some func := extractScalarFunc `booleanStepResult (some "entry") functionType (wrap (loop (.word (.bvar 1)) step)) |
                  throwError "Boolean step result rejected: {inputDepth}, {outputDepth}, {mode}, {monadic}"
                let module_ : LeanExe.IR.Module := { funcs := #[func] }
                for (count, seed) in inputs do
                  let expected : Bool := Id.run <| forIn (m := Id) [:count.toNat] (seed == 0) fun i flag =>
                    let value : ForInStep Bool := if UInt64.ofNat i == seed then .done (!flag) else .yield flag
                    if mode == 1 then .yield flag else value
                  let actual := module_.evalFunc 0 [count, seed]
                  unless actual == expected.toUInt64 do throwError "step result {actual} != {expected}, mode {mode}"
                  comparisons := comparisons + 1
                let resultType := BooleanStep.resultType input
                let outputType := BooleanStep.resultType output
                let unsupported : Lean.Expr := .const `unsupportedStep []
                let invalid : List Lean.Expr := [
                  make resultType resultType outputType (literalExpr 0) body,
                  make resultType resultType outputType (booleanLiteralExpr false) body,
                  make resultType resultType outputType unsupported body,
                  make boolean boolean outputType value body,
                  make word word outputType value body,
                  make resultType resultType outputType
                    (BooleanStep.choiceExpr input (Comparison.eq.condition (literalExpr 0) (literalExpr 0))
                      (Comparison.eq.evidence (literalExpr 0) (literalExpr 0)) value unsupported) body,
                  make resultType resultType outputType (Step.yieldDirect (literalExpr 0)) body,
                  make resultType resultType outputType value (BooleanStep.yieldDirect (.bvar 0)),
                  make resultType resultType outputType value (literalExpr 0),
                  make resultType resultType outputType value (.app (.bvar 0) (booleanLiteralExpr false))]
                for bad in invalid do
                  if (extractScalarFunc `invalidBooleanStepResult none functionType (wrap (loop (.word (.bvar 1)) bad))).isSome then
                    throwError "invalid Boolean step result admitted"
                  rejected := rejected + 1
                if monadic then
                  for bad in [make resultType word outputType value body,
                      make resultType (.app (.const ``Id [.zero]) resultType) outputType value body,
                      make resultType resultType boolean value body] do
                    if (extractScalarFunc `invalidBooleanStepResultBind none functionType (wrap (loop (.word (.bvar 1)) bad))).isSome then
                      throwError "invalid Boolean result bind annotations admitted"
                    rejected := rejected + 1
                if (extractScalarFunc `invalidEmptyBooleanStepResult none functionType
                    (wrap (loop (.literal 0 (by decide)) (make resultType resultType outputType unsupported
                      (BooleanStep.yieldDirect (.bvar 1)))))).isSome then
                  throwError "invalid ignored result in empty range admitted"
                rejected := rejected + 1
  unless comparisons == 18432 && rejected == 9600 do
    throwError "unexpected counts: {comparisons}, {rejected}"
  Lean.logInfo m!"{comparisons} native/Boolean step result syntax comparisons and {rejected} invalid-input tests passed"

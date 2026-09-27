import LeanExe.Extract.ScalarFunc

open LeanExe.Extract.Core
open LeanExe.Source.Scalar

run_elab do
  let word : Lean.Expr := .const ``UInt64 []
  let boolean : Lean.Expr := .const ``Bool []
  let nat : Lean.Expr := .const ``Nat []
  let functionType := Lean.Expr.forallE `count word (.forallE `seed word boolean .default) .default
  let wrap (body : Lean.Expr) := Lean.Expr.lam `count word (.lam `seed word body .default) .default
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
          let resultType := BooleanStep.resultType input
          let outputType := BooleanStep.resultType output
          let make (type domain result value body : Lean.Expr) :=
            Lean.Expr.letE `f (.forallE `typeArg type result binder) (.lam `arg domain value binder) body nondep
          for mode in List.range 6 do
            let indexWord : Lean.Expr := .app (.const ``UInt64.ofNat []) (.bvar 2)
            let condition := Comparison.eq.condition indexWord (.bvar 3)
            let evidence := Comparison.eq.evidence indexWord (.bvar 3)
            let argument := BooleanStep.choiceExpr input condition evidence
              (BooleanStep.doneDirect (neg (.bvar 1))) (BooleanStep.yieldDirect (.bvar 1))
            let value := match mode with
              | 1 => BooleanStep.yieldDirect (neg (.bvar 1))
              | 2 => BooleanStep.choiceExpr output condition evidence (.bvar 0) (BooleanStep.yieldDirect (.bvar 1))
              | 3 => Lean.Expr.letE `saved resultType (.bvar 0) (.bvar 0) nondep
              | 4 => BooleanStep.functionExpr resultType output `g `typeArg `arg binder binder
                  (.bvar 0) (.app (.bvar 0) (.bvar 1)) nondep
              | _ => Lean.Expr.bvar 0
            let body := if mode == 5 then Lean.Expr.letE `first outputType (.app (.bvar 0) argument)
                (.app (.bvar 1) (.bvar 0)) nondep
              else Lean.Expr.app (.bvar 0) argument
            for wrapped in [false, true] do
              let value := if wrapped then Lean.Expr.mdata {} (BooleanStep.idRun output (BooleanStep.idPure output value)) else value
              let step := make resultType resultType outputType value body
              let some func := extractScalarFunc `booleanStepResultFunction (some "entry") functionType (wrap (loop (.word (.bvar 1)) step)) |
                throwError "step result function rejected: {inputDepth}, {outputDepth}, {mode}"
              let module_ : LeanExe.IR.Module := { funcs := #[func] }
              for (count, seed) in inputs do
                let expected : Bool := Id.run <| forIn (m := Id) [:count.toNat] (seed == 0) fun i flag =>
                  if mode == 1 then .yield (!flag)
                  else if UInt64.ofNat i == seed then .done (!flag) else .yield flag
                let actual := module_.evalFunc 0 [count, seed]
                unless actual == expected.toUInt64 do throwError "step result function {actual} != {expected}, mode {mode}"
                comparisons := comparisons + 1
              let unsupported : Lean.Expr := .const `unsupportedStep []
              let invalid : List Lean.Expr := [
                make resultType word outputType value body,
                make resultType boolean outputType value body,
                make resultType (.app (.const ``Id [.zero]) resultType) outputType value body,
                make resultType resultType boolean value body,
                make resultType resultType word value body,
                make resultType resultType (.app (.const ``ForInStep [.zero]) word) value body,
                make resultType resultType outputType unsupported body,
                make resultType resultType outputType (literalExpr 0) body,
                make resultType resultType outputType (booleanLiteralExpr false) body,
                make resultType resultType outputType value (.app (.bvar 0) (literalExpr 0)),
                make resultType resultType outputType value (.app (.bvar 0) (booleanLiteralExpr false)),
                make resultType resultType outputType value (.app (.bvar 0) unsupported),
                make resultType resultType outputType (BooleanStep.yieldDirect (.bvar 0)) body]
              for bad in invalid do
                if (extractScalarFunc `invalidBooleanStepResultFunction none functionType (wrap (loop (.word (.bvar 1)) bad))).isSome then
                  throwError "invalid Boolean step result function admitted"
                rejected := rejected + 1
              if (extractScalarFunc `invalidEmptyBooleanStepResultFunction none functionType
                  (wrap (loop (.literal 0 (by decide)) (make resultType resultType outputType unsupported
                    (BooleanStep.yieldDirect (.bvar 1)))))).isSome then
                throwError "invalid unused function in empty range admitted"
              rejected := rejected + 1
  unless comparisons == 13824 && rejected == 8064 do
    throwError "unexpected counts: {comparisons}, {rejected}"
  Lean.logInfo m!"{comparisons} native/Boolean step result function syntax comparisons and {rejected} invalid-input tests passed"

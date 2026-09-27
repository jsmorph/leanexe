import LeanExe.Extract.ScalarFunc

open LeanExe.Extract.Core
open LeanExe.Source.Scalar

run_elab do
  let word : Lean.Expr := .const ``UInt64 []
  let boolean : Lean.Expr := .const ``Bool []
  let nat : Lean.Expr := .const ``Nat []
  let stepType := BooleanStep.resultType .boolean
  let functionType := Lean.Expr.forallE `count word (.forallE `seed word boolean .default) .default
  let wrap (body : Lean.Expr) := Lean.Expr.lam `count word (.lam `seed word body .default) .default
  let indexWord (index : Nat) := Lean.Expr.app (.const ``UInt64.ofNat []) (.bvar index)
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
    for outputDepth in [0, 1, 3] do
      let output := (List.range outputDepth).foldl (fun t _ => BooleanType.identity t) .boolean
      let make (motiveDomain result doneDomain yieldDomain value doneBody yieldBody : Lean.Expr) :=
        Lean.mkAppN (.const ``ForInStep.casesOn [.succ .zero, .zero]) #[boolean,
          .lam `motive motiveDomain result binder, value,
          .lam `payload doneDomain doneBody binder, .lam `payload yieldDomain yieldBody binder]
      for inputMode in List.range 4 do
        let conditional := BooleanStep.choiceExpr .boolean (Comparison.eq.condition (indexWord 1) (.bvar 2))
          (Comparison.eq.evidence (indexWord 1) (.bvar 2))
          (BooleanStep.doneDirect (neg (.bvar 0))) (BooleanStep.yieldDirect (.bvar 0))
        let value := match inputMode with
          | 0 => BooleanStep.doneDirect (booleanLiteralExpr false)
          | 1 => BooleanStep.yieldDirect (booleanLiteralExpr true)
          | 2 => conditional
          | _ => Lean.Expr.letE `saved (BooleanStep.resultType (.identity .boolean)) conditional
              (BooleanStep.idRun .boolean (.bvar 0)) false
        for mode in List.range 4 do
          let doneBody := match mode with
            | 0 => BooleanStep.doneDirect (.bvar 0)
            | 1 => BooleanStep.yieldDirect (.bvar 0)
            | 2 => BooleanStep.yieldDirect (neg (.bvar 0))
            | _ => BooleanStep.casesExpr output `nested `inner `inner binder binder binder
                (BooleanStep.yieldDirect (neg (.bvar 0)))
                (BooleanStep.doneDirect (booleanEqualityExpr true (.bvar 0) (.bvar 2)))
                (BooleanStep.yieldDirect (.bvar 0))
          let yieldBody := match mode with
            | 0 => BooleanStep.yieldDirect (.bvar 0)
            | 1 => BooleanStep.doneDirect (.bvar 0)
            | 2 => BooleanStep.yieldDirect (neg (.bvar 0))
            | _ => BooleanStep.yieldDirect (booleanEqualityExpr true (.bvar 0) (.bvar 1))
          for wrappedInput in [false, true] do
            let value := if wrappedInput then Lean.Expr.mdata {} (BooleanStep.idRun output (BooleanStep.idPure output value)) else value
            for wrappedBody in [false, true] do
              let doneBody := if wrappedBody then BooleanStep.idRun output (BooleanStep.idPure output doneBody) else doneBody
              let yieldBody := if wrappedBody then Lean.Expr.mdata {} (BooleanStep.idRun output yieldBody) else yieldBody
              let step := make stepType (BooleanStep.resultType output) boolean boolean value doneBody yieldBody
              let some func := extractScalarFunc `booleanStepCases (some "entry") functionType
                  (wrap (loop (.word (.bvar 1)) step)) |
                throwError "cases rejected: {inputMode}, {mode}, {outputDepth}"
              let module_ : LeanExe.IR.Module := { funcs := #[func] }
              for (count, seed) in inputs do
                let expected : Bool := Id.run <| forIn (m := Id) [:count.toNat] (seed == 0) fun i flag =>
                  let isDone := if inputMode == 0 then true else if inputMode == 1 then false else UInt64.ofNat i == seed
                  let payload := if inputMode == 0 then false else if inputMode == 1 then true else if isDone then !flag else flag
                  if mode == 0 then (if isDone then .done payload else .yield payload)
                  else if mode == 1 then (if isDone then .yield payload else .done payload)
                  else if mode == 2 then .yield (!payload)
                  else .yield (if isDone then !payload else payload != flag)
                let actual := module_.evalFunc 0 [count, seed]
                unless actual == expected.toUInt64 do throwError "cases {actual} != {expected}: {inputMode}, {mode}"
                comparisons := comparisons + 1
              let unsupported : Lean.Expr := .const `unsupportedStep []
              let outputType := BooleanStep.resultType output
              let invalid : List Lean.Expr := [
                make word outputType boolean boolean value doneBody yieldBody,
                make stepType boolean boolean boolean value doneBody yieldBody,
                make stepType word boolean boolean value doneBody yieldBody,
                make stepType (.bvar 0) boolean boolean value doneBody yieldBody,
                make stepType outputType word boolean value doneBody yieldBody,
                make stepType outputType boolean word value doneBody yieldBody,
                make stepType outputType boolean boolean (literalExpr 0) doneBody yieldBody,
                make stepType outputType boolean boolean (booleanLiteralExpr false) doneBody yieldBody,
                make stepType outputType boolean boolean unsupported doneBody yieldBody,
                make stepType outputType boolean boolean value (literalExpr 0) yieldBody,
                make stepType outputType boolean boolean value doneBody (BooleanStep.yieldDirect (literalExpr 0)),
                make stepType outputType boolean boolean value (BooleanStep.yieldDirect (.bvar 100)) yieldBody]
              for bad in invalid do
                if (extractScalarFunc `invalidBooleanStepCases none functionType (wrap (loop (.word (.bvar 1)) bad))).isSome then
                  throwError "invalid cases admitted"
                rejected := rejected + 1
              for bound in [Range.Exit.Count.word (.bvar 1), .literal 0 (by decide)] do
                if (extractScalarFunc `invalidUnusedBooleanStepCase none functionType
                    (wrap (loop bound (make stepType outputType boolean boolean
                      (BooleanStep.doneDirect (booleanLiteralExpr false)) doneBody unsupported)))).isSome then
                  throwError "invalid unused case branch admitted"
                rejected := rejected + 1
  unless comparisons == 18432 && rejected == 10752 do
    throwError "unexpected counts: {comparisons}, {rejected}"
  Lean.logInfo m!"{comparisons} native/Boolean step cases syntax comparisons and {rejected} invalid-input tests passed"

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
  let indexWord (index : Nat) := Lean.Expr.app (.const ``UInt64.ofNat []) (.bvar index)
  let neg (value : Lean.Expr) := Lean.Expr.app (.const ``Bool.not []) value
  let choose (output : BooleanType) (condition yes no : Lean.Expr) :=
    BooleanStep.choiceExpr output (booleanRelationCondition false condition (booleanLiteralExpr true))
      (booleanRelationEvidence false condition (booleanLiteralExpr true)) yes no
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
      let bt := (List.range inputDepth).foldl (fun t _ => BooleanType.identity t) .boolean
      let wt := (List.range inputDepth).foldl (fun t _ => ResultType.identity t) .word
      for outputDepth in [0, 1, 3] do
        let output := (List.range outputDepth).foldl (fun t _ => BooleanType.identity t) .boolean
        for flagInput in [false, true] do
          let input := if flagInput then bt.expr else wt.expr
          let opposite := if flagInput then wt.expr else bt.expr
          let predicate := if flagInput then Lean.Expr.bvar 0
            else (BooleanLocal.compare .eq (modWord (.bvar 0) (literalExpr 3)) (literalExpr 0)).expr
          let argument (index seed : Nat) := if flagInput then (BooleanLocal.compare .eq (indexWord index) (.bvar seed)).expr
            else add (indexWord index) (.bvar seed)
          let alternative := if flagInput then booleanLiteralExpr false else literalExpr 0
          for wrapped in [false, true] do
            let value := choose output predicate (BooleanStep.doneDirect (neg (.bvar 1))) (BooleanStep.yieldDirect (.bvar 1))
            let value := if wrapped then BooleanStep.idRun output (BooleanStep.idPure output value) else value
            for nondep in [false, true] do
              let make (input domain result value body : Lean.Expr) := Lean.Expr.letE `f
                (.forallE `typeArg input result binder) (.lam `arg domain value binder) body nondep
              for mode in List.range 3 do
                let body := match mode with
                  | 0 => Lean.Expr.app (.bvar 0) (argument 2 3)
                  | 1 => BooleanStep.yieldDirect (.bvar 1)
                  | _ => BooleanStep.functionExpr boolean output `g `typeArg `arg binder binder
                      (choose output (.bvar 0) (.app (.bvar 1) (argument 3 4)) (.app (.bvar 1) alternative))
                      (.app (.bvar 0) (BooleanLocal.compare .eq (indexWord 3) (.bvar 4)).expr) nondep
                let step := make input input (BooleanStep.resultType output) value body
                let source := loop (.word (.bvar 1)) step
                let some func := extractScalarFunc `booleanStepFunction (some "entry") functionType (wrap source) |
                  throwError "Boolean step function rejected: {flagInput}, {inputDepth}, {outputDepth}, {mode}"
                let module_ : LeanExe.IR.Module := { funcs := #[func] }
                for (count, seed) in inputs do
                  let expected : Bool := Id.run <| forIn (m := Id) [:count.toNat] (seed == 0) fun i flag =>
                    let branch := UInt64.ofNat i == seed
                    let pred := if flagInput then (if mode == 2 && !branch then false else branch)
                      else (if mode == 2 && !branch then 0 else UInt64.ofNat i + seed) % 3 == 0
                    if mode == 1 then .yield flag
                    else if pred then .done (!flag) else .yield flag
                  let actual := module_.evalFunc 0 [count, seed]
                  unless actual == expected.toUInt64 do throwError "Boolean function result {actual} != {expected}: mode {mode}"
                  comparisons := comparisons + 1
                let unsupported : Lean.Expr := .const `unsupportedStep []
                let invalid : List Lean.Expr := [
                  make input opposite (BooleanStep.resultType output) value body,
                  make opposite input (BooleanStep.resultType output) value body,
                  make input (.app (.const ``Id [.zero]) input) (BooleanStep.resultType output) value body,
                  make input input boolean value body,
                  make input input (Step.resultType .word) value body,
                  make input input (BooleanStep.resultType output) unsupported body,
                  make input input (BooleanStep.resultType output)
                    (choose output (booleanLiteralExpr true) value unsupported) body,
                  make input input (BooleanStep.resultType output) (BooleanStep.yieldDirect (literalExpr 0)) body,
                  make input input (BooleanStep.resultType output) value
                    (.app (.bvar 0) (if flagInput then literalExpr 0 else booleanLiteralExpr true)),
                  make input input (BooleanStep.resultType output) value (.app (.bvar 0) (.const `unsupportedArgument [])),
                  make input input (BooleanStep.resultType output) value (BooleanStep.yieldDirect (.bvar 0)),
                  make input input (BooleanStep.resultType output) value (.app (.bvar 1) (argument 2 3))]
                for bad in invalid do
                  if (extractScalarFunc `invalidBooleanStepFunction none functionType (wrap (loop (.word (.bvar 1)) bad))).isSome then
                    throwError "invalid Boolean step function admitted"
                  rejected := rejected + 1
                if (extractScalarFunc `invalidEmptyBooleanStepFunction none functionType
                    (wrap (loop (.literal 0 (by decide)) (make input input (BooleanStep.resultType output) unsupported
                      (BooleanStep.yieldDirect (.bvar 1)))))).isSome then
                  throwError "invalid unused function in empty range admitted"
                rejected := rejected + 1
  unless comparisons == 20736 && rejected == 11232 do
    throwError "unexpected counts: {comparisons}, {rejected}"
  Lean.logInfo m!"{comparisons} native/Boolean step function syntax comparisons and {rejected} invalid-input tests passed"

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
  let mul (a b : Lean.Expr) := Lean.Expr.app (.app (.const ``UInt64.mul []) a) b
  let modWord (a b : Lean.Expr) := Lean.Expr.app (.app (.const ``UInt64.mod []) a) b
  let indexWord (index : Nat) := Lean.Expr.app (.const ``UInt64.ofNat []) (.bvar index)
  let neg (value : Lean.Expr) := Lean.Expr.app (.const ``Bool.not []) value
  let wordChoice (flag yes no : Lean.Expr) := Lean.mkAppN (.const ``ite [.succ .zero]) #[word,
    booleanRelationCondition false flag (booleanLiteralExpr true),
    booleanRelationEvidence false flag (booleanLiteralExpr true), yes, no]
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
      let bi := (List.range inputDepth).foldl (fun t _ => BooleanType.identity t) .boolean
      let wi := (List.range inputDepth).foldl (fun t _ => ResultType.identity t) .word
      for outputDepth in [0, 2] do
        let bo := (List.range outputDepth).foldl (fun t _ => BooleanType.identity t) .boolean
        let wo := (List.range outputDepth).foldl (fun t _ => ResultType.identity t) .word
        for flagInput in [false, true] do
          for flagOutput in [false, true] do
            let input := if flagInput then bi.expr else wi.expr
            let opposite := if flagInput then wi.expr else bi.expr
            let output := if flagOutput then bo.expr else wo.expr
            let value := if flagInput then
                if flagOutput then booleanEqualityExpr true (.bvar 0) (BooleanLocal.compare .eq (indexWord 2) (.bvar 3)).expr
                else wordChoice (.bvar 0) (add (.bvar 3) (literalExpr 1)) (mul (.bvar 3) (literalExpr 3))
              else if flagOutput then (BooleanLocal.compare .eq (modWord (.bvar 0) (literalExpr 3)) (.bvar 3)).expr
              else add (.bvar 0) (.bvar 3)
            let callback (call : Lean.Expr) (flag index : Nat) := if flagOutput then BooleanStep.yieldDirect call else
              let right := if flagInput then indexWord index else literalExpr 0
              BooleanStep.choiceExpr .boolean (Comparison.eq.condition call right) (Comparison.eq.evidence call right)
                (BooleanStep.doneDirect (neg (.bvar flag))) (BooleanStep.yieldDirect (.bvar flag))
            let argument (flag index : Nat) := if flagInput then Lean.Expr.bvar flag else indexWord index
            for nondep in [false, true] do
              let make (input domain output value body : Lean.Expr) := Lean.Expr.letE `f
                (.forallE `typeArg input output binder) (.lam `arg domain value binder) body nondep
              for mode in List.range 3 do
                let body := match mode with
                  | 0 => callback (.app (.bvar 0) (argument 1 2)) 1 2
                  | 1 => BooleanStep.yieldDirect (.bvar 1)
                  | _ => make input input output (.app (.bvar 1) (.bvar 0))
                      (callback (.app (.bvar 0) (argument 2 3)) 2 3)
                for wrapped in [false, true] do
                  let value := if wrapped then Lean.Expr.mdata {} (if flagOutput then
                      BooleanIdentity.run (BooleanIdentity.pure value bo) bo
                    else Identity.run (Identity.pure value wo) wo) else value
                  let step := make input input output value body
                  let some func := extractScalarFunc `booleanStepScalarFunction (some "entry") functionType
                      (wrap (loop (.word (.bvar 1)) step)) |
                    throwError "scalar helper rejected: {flagInput}, {flagOutput}, {inputDepth}, {outputDepth}, {mode}"
                  let module_ : LeanExe.IR.Module := { funcs := #[func] }
                  for (count, seed) in inputs do
                    let expected : Bool := Id.run <| forIn (m := Id) [:count.toNat] (seed == 0) fun i flag =>
                      if mode == 1 then .yield flag
                      else if flagOutput then
                        .yield (if flagInput then flag != (UInt64.ofNat i == seed) else UInt64.ofNat i % 3 == seed)
                      else
                        let result := if flagInput then (if flag then seed + 1 else seed * 3) else UInt64.ofNat i + seed
                        let right := if flagInput then UInt64.ofNat i else 0
                        if result == right then .done (!flag) else .yield flag
                    let actual := module_.evalFunc 0 [count, seed]
                    unless actual == expected.toUInt64 do throwError "scalar helper {actual} != {expected}: {flagInput}, {flagOutput}, {mode}"
                    comparisons := comparisons + 1
                  let unsupported : Lean.Expr := .const `unsupportedScalar []
                  let wrongArg := if flagInput then literalExpr 0 else booleanLiteralExpr false
                  let wrongResult := if flagOutput then literalExpr 0 else booleanLiteralExpr false
                  let invalid : List Lean.Expr := [
                    make input opposite output value body,
                    make opposite input output value body,
                    make input (.app (.const ``Id [.zero]) input) output value body,
                    make input input (BooleanStep.resultType .boolean) value body,
                    make input input nat value body,
                    make input input output unsupported body,
                    make input input output wrongResult body,
                    make input input output (.bvar 100) body,
                    make input input output (BooleanStep.doneDirect (booleanLiteralExpr false)) body,
                    make input input output value (callback (.app (.bvar 0) wrongArg) 1 2),
                    make input input output value (callback (.app (.bvar 0) unsupported) 1 2),
                    make input input output value (callback (.app (.bvar 1) (argument 1 2)) 1 2),
                    make input input output value (BooleanStep.yieldDirect (.bvar 0))]
                  for bad in invalid do
                    if (extractScalarFunc `invalidBooleanStepScalarFunction none functionType
                        (wrap (loop (.word (.bvar 1)) bad))).isSome then
                      throwError "invalid scalar helper admitted: {flagInput}, {flagOutput}"
                    rejected := rejected + 1
                  if (extractScalarFunc `invalidEmptyBooleanStepScalarFunction none functionType
                      (wrap (loop (.literal 0 (by decide)) (make input input output unsupported
                        (BooleanStep.yieldDirect (.bvar 1)))))).isSome then
                    throwError "invalid unused scalar helper in empty range admitted"
                  rejected := rejected + 1
  unless comparisons == 27648 && rejected == 16128 do
    throwError "unexpected counts: {comparisons}, {rejected}"
  Lean.logInfo m!"{comparisons} native/Boolean step scalar function syntax comparisons and {rejected} invalid-input tests passed"

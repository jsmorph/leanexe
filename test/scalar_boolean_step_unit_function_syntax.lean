import LeanExe.Extract.ScalarFunc

open LeanExe.Extract.Core
open LeanExe.Source.Scalar

run_elab do
  let word : Lean.Expr := .const ``UInt64 []
  let boolean : Lean.Expr := .const ``Bool []
  let signature := Lean.Expr.forallE `count word (.forallE `seed word boolean .default) .default
  let stride : Range.Exit.Stride := ⟨1, by decide, by decide, .const ``Nat.zero_lt_one []⟩
  let wrap (empty : Bool) (body : Lean.Expr) := Lean.Expr.lam `count word (.lam `seed word
    (BooleanAccumulator.call ⟨.const ``Nat [], rfl⟩ stride (.literal 0 (by decide))
      (if empty then .literal 0 (by decide) else .word (.bvar 1))
      (BooleanLocal.compare .eq (.bvar 0) (literalExpr 0)).expr `i `flag .default .default body) .default) .default
  let toWord (value : Lean.Expr) := Lean.Expr.app (.const ``Bool.toUInt64 []) value
  let neg (value : Lean.Expr) := Lean.Expr.app (.const ``Bool.not []) value
  let indexWord (i : Nat) := Lean.Expr.app (.const ``UInt64.ofNat []) (.bvar i)
  let add (x y : Lean.Expr) := Lean.mkAppN (.const ``UInt64.add []) #[x, y]
  let mod7 (x : Lean.Expr) := Lean.mkAppN (.const ``UInt64.mod []) #[x, literalExpr 7]
  let call (index : Nat) (unit argument : Lean.Expr) := Lean.Expr.app (.app (.bvar index) unit) argument
  let inputs : List (UInt64 × UInt64) :=
    ([0, 1, 2, 7, 16, 31] : List UInt64).flatMap fun n =>
      ([0, 1, 0x8000000000000000, 0xffffffffffffffff] : List UInt64).map fun seed => (n, seed)
  let mut comparisons : Nat := 0
  let mut rejected : Nat := 0
  let mut controls : Nat := 0
  for inputDepth in [0, 2] do
    let input := (List.range inputDepth).foldl (fun t _ => BooleanType.identity t) .boolean
    for outputDepth in [0, 1, 3] do
      let output := (List.range outputDepth).foldl (fun t _ => BooleanType.identity t) .boolean
      for unitForm in [UnitSyntax.unit, .punit] do
        let other := if unitForm == .unit then UnitSyntax.punit else .unit
        for unitInfo in [Lean.BinderInfo.default, .implicit] do
          for flagInfo in [Lean.BinderInfo.default, .strictImplicit] do
            for nondep in [false, true] do
              let helper (unitType unitDomain input domain result value tail : Lean.Expr) := Lean.Expr.letE `f
                (.forallE `unitType unitType (.forallE `flagType input result flagInfo) unitInfo)
                (.lam `unitValue unitDomain (.lam `flagValue domain value flagInfo) unitInfo) tail nondep
              let typed := helper unitForm.type unitForm.type input.expr input.expr (BooleanStep.resultType output)
              let left := mod7 (add (indexWord 3) (.bvar 4))
              let right := toWord (.bvar 0)
              let rawBody := BooleanStep.choiceExpr output
                (Comparison.eq.condition left right) (Comparison.eq.evidence left right)
                (BooleanStep.doneDirect (booleanEqualityExpr true (.bvar 0) (.bvar 2)))
                (BooleanStep.yieldDirect (neg (.bvar 0)))
              for wrapped in [false, true] do
                let body := if wrapped then Lean.Expr.mdata {}
                  (BooleanStep.idPure output (BooleanStep.idRun output rawBody)) else rawBody
                for mode in ([0, 1, 2, 3] : List Nat) do
                  let applied := call 0 unitForm.value (.bvar 1)
                  let tail := if mode == 1 then BooleanStep.yieldDirect (.bvar 1)
                    else if mode == 2 then helper other.type other.type input.expr input.expr (BooleanStep.resultType output)
                      (call 2 unitForm.value (neg (.bvar 0))) (call 0 other.value (.bvar 2))
                    else if mode == 3 then Lean.Expr.letE `saved (BooleanStep.resultType output) applied
                      (BooleanStep.casesExpr .boolean `result `doneFlag `yieldFlag .default unitInfo flagInfo (.bvar 0)
                        (BooleanStep.yieldDirect (.bvar 0)) (BooleanStep.doneDirect (neg (.bvar 0)))) nondep
                    else applied
                  let source := typed body tail
                  unless (booleanUnitStepFunction? source).isSome &&
                      (booleanStepUnitValue? unitForm.value).isSome do throwError "unit-step recognition failed"
                  controls := controls + 1
                  let some func := extractScalarFunc `unitBooleanStep (some "entry") signature (wrap false source) |
                    throwError "unit-step rejected: {inputDepth}, {outputDepth}, {reprStr unitForm}, {mode}"
                  let module_ : LeanExe.IR.Module := { funcs := #[func] }
                  for (count, seed) in inputs do
                    let expected : Bool := forIn (m := Id) [:count.toNat] (seed == 0) fun i flag =>
                      let f := fun b : Bool =>
                        if (UInt64.ofNat i + seed) % 7 == b.toUInt64 then ForInStep.done (b != flag)
                        else ForInStep.yield (!b)
                      if mode == 1 then .yield flag
                      else if mode == 2 then f (!flag)
                      else if mode == 3 then
                        match f flag with
                        | .done b => .yield b
                        | .yield b => .done (!b)
                      else f flag
                    let actual := module_.evalFunc 0 [count, seed]
                    unless actual == expected.toUInt64 do
                      throwError "unit-step capture/result mismatch: {actual} != {expected}, mode {mode}"
                    comparisons := comparisons + 1
                  let unknown := Lean.Expr.const `unsupportedUnitBooleanStep []
                  let invalid := [
                    helper other.type unitForm.type input.expr input.expr (BooleanStep.resultType output) body tail,
                    helper unitForm.type other.type input.expr input.expr (BooleanStep.resultType output) body tail,
                    helper word word input.expr input.expr (BooleanStep.resultType output) body tail,
                    helper unitForm.type unitForm.type word input.expr (BooleanStep.resultType output) body tail,
                    helper unitForm.type unitForm.type input.expr word (BooleanStep.resultType output) body tail,
                    helper unitForm.type unitForm.type (.app (.const ``Id [.succ .zero]) boolean) input.expr (BooleanStep.resultType output) body tail,
                    helper unitForm.type unitForm.type input.expr input.expr word body tail,
                    helper unitForm.type unitForm.type input.expr input.expr boolean body tail,
                    helper unitForm.type unitForm.type input.expr input.expr (.const ``Nat []) body tail,
                    helper unitForm.type unitForm.type input.expr input.expr (.app (.const ``Id [.succ .zero]) (BooleanStep.resultType output)) body tail,
                    typed unknown tail,
                    typed (booleanLiteralExpr true) tail,
                    typed (literalExpr 0) tail,
                    typed (.bvar 1) tail,
                    typed body unknown,
                    typed unknown (BooleanStep.yieldDirect (.bvar 1)),
                    typed body (.app (.bvar 0) (.bvar 1)),
                    typed body (.app (.bvar 0) unitForm.value),
                    typed body (call 0 other.value (.bvar 1)),
                    typed body (call 0 unknown (.bvar 1)),
                    typed body (call 0 unitForm.value unknown),
                    typed body (call 0 unitForm.value (literalExpr 0)),
                    typed body (call 99 unitForm.value (.bvar 1)),
                    typed body (.app applied (.bvar 1)),
                    typed body (BooleanStep.yieldDirect (.bvar 0)),
                    typed body (call 0 (.bvar 1) (.bvar 1))]
                  for bad in invalid do
                    for empty in [false, true] do
                      unless (extractScalarFunc `invalidUnitBooleanStep none signature (wrap empty bad)).isNone do
                        throwError "invalid unit-step admitted: {reprStr unitForm}, mode {mode}, empty {empty}"
                      rejected := rejected + 1
  unless comparisons == 18432 && rejected == 39936 && controls == 768 do
    throwError "unexpected counts {comparisons}, {rejected}, {controls}"
  Lean.logInfo m!"{comparisons} native/Unit-prefixed Boolean step IR comparisons, {rejected} invalid-input tests and {controls} admission controls passed"

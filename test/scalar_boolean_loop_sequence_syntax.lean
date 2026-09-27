import LeanExe.Extract.ScalarFunc

open LeanExe.Extract.Core
open LeanExe.Source.Scalar

run_elab do
  let word : Lean.Expr := .const ``UInt64 []
  let boolean : Lean.Expr := .const ``Bool []
  let signature := Lean.Expr.forallE `count word (.forallE `seed word boolean .default) .default
  let wrap (body : Lean.Expr) := Lean.Expr.lam `count word (.lam `seed word body .default) .default
  let add (a b : Lean.Expr) := Lean.mkAppN (.const ``UInt64.add []) #[a, b]
  let mul (a b : Lean.Expr) := Lean.mkAppN (.const ``UInt64.mul []) #[a, b]
  let mod (a : Lean.Expr) (n : Nat) := Lean.mkAppN (.const ``UInt64.mod []) #[a, literalExpr n]
  let eq (a b : Lean.Expr) := (BooleanLocal.compare .eq a b).expr
  let eqZero (a : Lean.Expr) := eq a (literalExpr 0)
  let choose (result flag yes no : Lean.Expr) := Lean.mkAppN (.const ``ite [.succ .zero])
    #[result, booleanRelationCondition false flag (booleanLiteralExpr true),
      booleanRelationEvidence false flag (booleanLiteralExpr true), yes, no]
  let index := Lean.Expr.app (.const ``UInt64.ofNat []) (.bvar 1)
  let stride : Range.Exit.Stride := ⟨1, by decide, by decide, .const ``Nat.zero_lt_one []⟩
  let flagRange (bound initial step : Lean.Expr) (binder : Lean.BinderInfo) :=
    BooleanAccumulator.call ⟨.const ``Nat [], rfl⟩ stride
      (.literal 0 (by decide)) (.word bound) initial `i `a binder binder step
  let inputs := ([0, 1, 2, 7, 16, 31] : List UInt64).flatMap fun n =>
    ([0, 1, 0x8000000000000000, 0xffffffffffffffff] : List UInt64).map fun seed => (n, seed)
  let unknown := Lean.Expr.const `unsupportedBooleanSequenceValue []
  let rawBind (input output domain value body : Lean.Expr) (binder : Lean.BinderInfo) :=
    Lean.Expr.app (.app (.app (.app (.app (.app (.const ``Bind.bind [.zero, .zero]) (.const ``Id [.zero]))
      (.app (.app (.const ``Monad.toBind [.zero, .zero]) (.const ``Id [.zero])) (.const ``Id.instMonad [.zero])))
      input) output) value) (.lam `saved domain body binder)
  let mut comparisons : Nat := 0
  let mut rejected : Nat := 0
  let mut controls : Nat := 0
  for depth in [0, 1, 2] do
    let wordType := (List.range depth).foldl (fun type _ => ResultType.identity type) .word
    let boolType := (List.range depth).foldl (fun type _ => BooleanType.identity type) .boolean
    for monadic in [false, true] do
      for binder in [Lean.BinderInfo.default, .implicit] do
        for nondep in [false, true] do
          let save (value body : Lean.Expr) := if monadic then BooleanRange.bind `saved binder wordType boolType value body
            else Lean.Expr.letE `saved wordType.expr value body nondep
          let saveWord (value body : Lean.Expr) := if monadic then Identity.bind `saved binder value body wordType wordType
            else Lean.Expr.letE `saved wordType.expr value body nondep
          for wrapper in ([0, 1, 2] : List Nat) do
            let wrapped (source : Lean.Expr) := if wrapper == 0 then source else if wrapper == 1 then
                BooleanIdentity.run (BooleanIdentity.pure source boolType) (.identity boolType)
              else Lean.Expr.mdata {} source
            for three in [false, true] do
              for dependent in [false, true] do
                for exits in [false, true] do
                  let firstNext := add (add (.bvar 0) index) (literalExpr 1)
                  let firstStep := if exits then choose (Step.resultType .word) (eqZero (mod firstNext 7))
                      (Step.doneDirect firstNext) (Step.yieldDirect firstNext)
                    else Step.yieldDirect firstNext
                  let firstBase := Range.call (.bvar 1) (.bvar 0) `i `a binder binder firstStep
                  let prefixStep := Step.yieldDirect (add (add (.bvar 0) (.bvar 2)) (mul (literalExpr 2) index))
                  let nextWord :=  Range.call (.bvar 2) (add (.bvar 0) (.bvar 1)) `j `b binder binder prefixStep
                  let first := if three then saveWord firstBase nextWord else firstBase
                  let next := booleanEqualityExpr true (.bvar 0) (eq (mod index 7) (mod (.bvar 2) 7))
                  let step := if exits then choose (BooleanStep.resultType .boolean) (eqZero (mod index 3))
                      (BooleanStep.yieldDirect (.bvar 0))
                      (choose (BooleanStep.resultType .boolean) next
                        (BooleanStep.doneDirect next) (BooleanStep.yieldDirect next))
                    else BooleanStep.yieldDirect next
                  let bound := if dependent then mod (.bvar 0) 7 else .bvar 2
                  let initial := eqZero (mod (add (.bvar 0) (.bvar 1)) 3)
                  let second := flagRange bound initial step binder
                  let source := wrapped (save first second)
                  unless (extractScalarBooleanRangeWith (publicBindings (publicInputs signature)) 2 source).isNone do
                    throwError "Boolean sequence control unexpectedly uses a single-loop plan"
                  controls := controls + 1
                  let some func := extractScalarFunc `booleanLoopSequence (some "entry") signature (wrap source) |
                    throwError "Boolean sequence rejected: depth {depth}, wrapper {wrapper}, three {three}"
                  let module_ : LeanExe.IR.Module := { funcs := #[func] }
                  for (count, seed) in inputs do
                    let a : UInt64 := forIn (m := Id) [:count.toNat] seed fun i a =>
                      let next := a + UInt64.ofNat i + 1
                      if exits && next % 7 == 0 then .done next else .yield next
                    let a : UInt64 := if three then forIn (m := Id) [:count.toNat] (a + seed) fun i b =>
                        .yield (b + a + 2 * UInt64.ofNat i)
                      else a
                    let n := if dependent then a % 7 else count
                    let flag : Bool := forIn (m := Id) [:n.toNat] ((a + seed) % 3 == 0) fun i b =>
                      let next := b != (UInt64.ofNat i % 7 == a % 7)
                      if exits && UInt64.ofNat i % 3 == 0 then .yield b
                      else if exits && next then .done next else .yield next
                    let actual := module_.evalFunc 0 [count, seed]
                    unless actual == flag.toUInt64 do throwError "Boolean sequence capture/state: {actual} != {flag}"
                    comparisons := comparisons + 1
                  for empty in [false, true] do
                    let first := Range.call (if empty then literalExpr 0 else .bvar 1) (.bvar 0) `i `a binder binder firstStep
                    let second := flagRange (if empty then literalExpr 0 else bound) initial step binder
                    let invalid := [
                      Lean.Expr.letE `saved boolean first second nondep,
                      .letE `saved (.const ``Nat []) first second nondep,
                      .letE `saved (.app (.const ``Id [.succ .zero]) word) first second nondep,
                      save unknown second, save first unknown,
                      save (Range.call (literalExpr 0) (.bvar 0) `i `a binder binder
                        (Step.yieldDirect (booleanLiteralExpr true))) second,
                      save first (flagRange (literalExpr 0) initial (BooleanStep.yieldDirect (literalExpr 0)) binder),
                      save (Range.call (booleanLiteralExpr false) (.bvar 0) `i `a binder binder firstStep) second,
                      save first (flagRange (booleanLiteralExpr false) initial step binder),
                      save first (flagRange (literalExpr 0) (literalExpr 0) step binder),
                      rawBind wordType.expr boolType.expr boolean first second binder,
                      rawBind (.const ``Nat []) boolType.expr (.const ``Nat []) first second binder,
                      rawBind wordType.expr wordType.expr wordType.expr first second binder,
                      .app (.app (.const `unsupportedBooleanSequenceBind []) first) (.lam `saved wordType.expr second binder),
                      .app (.app (.const ``Id.run [.succ .zero]) boolType.expr) (save first second),
                      save unknown (flagRange (literalExpr 0) (booleanLiteralExpr false) (BooleanStep.yieldDirect (.bvar 0)) binder)]
                    for bad in invalid do
                      unless (extractScalarFunc `invalidBooleanSequence none signature (wrap (wrapped bad))).isNone do
                        throwError "invalid Boolean sequence admitted: empty {empty}, three {three}"
                      rejected := rejected + 1
  unless comparisons == 13824 && rejected == 18432 && controls == 576 do
    throwError "unexpected counts {comparisons}, {rejected}, {controls}"
  Lean.logInfo m!"{comparisons} native/Boolean-result sequential-loop IR comparisons, {rejected} invalid-input tests and {controls} admission controls passed"

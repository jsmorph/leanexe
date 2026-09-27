import LeanExe.Extract.ScalarFunc

open LeanExe.Extract.Core
open LeanExe.Source.Scalar

run_elab do
  let word : Lean.Expr := .const ``UInt64 []
  let boolean : Lean.Expr := .const ``Bool []
  let signature := Lean.Expr.forallE `count word (.forallE `seed word word .default) .default
  let wrap (body : Lean.Expr) := Lean.Expr.lam `count word (.lam `seed word body .default) .default
  let add (a b : Lean.Expr) := Lean.mkAppN (.const ``UInt64.add []) #[a, b]
  let mul (a b : Lean.Expr) := Lean.mkAppN (.const ``UInt64.mul []) #[a, b]
  let mod (a : Lean.Expr) (n : Nat) := Lean.mkAppN (.const ``UInt64.mod []) #[a, literalExpr n]
  let eqZero (a : Lean.Expr) := (BooleanLocal.compare .eq a (literalExpr 0)).expr
  let stepChoice (flag yes no : Lean.Expr) := Lean.mkAppN (.const ``ite [.succ .zero])
    #[Step.resultType .word, booleanRelationCondition false flag (booleanLiteralExpr true),
      booleanRelationEvidence false flag (booleanLiteralExpr true), yes, no]
  let index := Lean.Expr.app (.const ``UInt64.ofNat []) (.bvar 1)
  let inputs := ([0, 1, 2, 7, 16, 31] : List UInt64).flatMap fun n =>
    ([0, 1, 0x8000000000000000, 0xffffffffffffffff] : List UInt64).map fun seed => (n, seed)
  let unknown := Lean.Expr.const `unsupportedSequenceValue []
  let rawBind (input output domain value body : Lean.Expr) (binder : Lean.BinderInfo) :=
    Lean.Expr.app (.app (.app (.app (.app (.app (.const ``Bind.bind [.zero, .zero]) (.const ``Id [.zero]))
      (.app (.app (.const ``Monad.toBind [.zero, .zero]) (.const ``Id [.zero])) (.const ``Id.instMonad [.zero])))
      input) output) value) (.lam `saved domain body binder)
  let mut comparisons : Nat := 0
  let mut rejected : Nat := 0
  let mut controls : Nat := 0
  for depth in [0, 1, 2] do
    let type := (List.range depth).foldl (fun type _ => ResultType.identity type) .word
    for monadic in [false, true] do
      for binder in [Lean.BinderInfo.default, .implicit] do
        for nondep in [false, true] do
          let save (value body : Lean.Expr) := if monadic then Identity.bind `saved binder value body type type
            else Lean.Expr.letE `saved type.expr value body nondep
          for wrapper in ([0, 1, 2] : List Nat) do
            let wrapped (source : Lean.Expr) := if wrapper == 0 then source else if wrapper == 1 then
                Identity.run (Identity.pure source type) (.identity type)
              else Lean.Expr.mdata {} source
            for three in [false, true] do
              for dependent in [false, true] do
                for exits in [false, true] do
                  let firstNext := add (add (.bvar 0) index) (literalExpr 1)
                  let firstStep := if exits then stepChoice (eqZero (mod firstNext 7))
                      (Step.doneDirect firstNext) (Step.yieldDirect firstNext)
                    else Step.yieldDirect firstNext
                  let first := Range.call (.bvar 1) (.bvar 0) `i `a binder binder firstStep
                  let secondNext := add (add (.bvar 0) (.bvar 2)) (mul (literalExpr 2) index)
                  let secondStep := if exits then stepChoice (eqZero (mod index 3))
                      (Step.yieldDirect (.bvar 0)) (stepChoice (eqZero (mod secondNext 11))
                        (Step.doneDirect secondNext) (Step.yieldDirect secondNext))
                    else Step.yieldDirect secondNext
                  let secondBound := if dependent then mod (.bvar 0) 7 else .bvar 2
                  let second := Range.call secondBound (add (.bvar 0) (.bvar 1)) `j `b binder binder secondStep
                  let thirdStep := Step.yieldDirect (Lean.mkAppN (.const ``UInt64.xor []) #[.bvar 0, index])
                  let third := Range.call (.bvar 3) (add (.bvar 0) (.bvar 2)) `k `c binder binder thirdStep
                  let result := if three then save third (add (add (.bvar 0) (.bvar 1)) (.bvar 2))
                    else add (.bvar 0) (.bvar 1)
                  let continuation := save second result
                  let source := wrapped (save first continuation)
                  unless (extractScalarWordRangeWith (publicBindings (publicInputs signature)) 2 source).isNone do
                    throwError "sequence control unexpectedly uses a single-loop plan"
                  controls := controls + 1
                  let some func := extractScalarFunc `loopSequence (some "entry") signature (wrap source) |
                    throwError "sequence rejected: depth {depth}, wrapper {wrapper}, three {three}"
                  let module_ : LeanExe.IR.Module := { funcs := #[func] }
                  for (count, seed) in inputs do
                    let a : UInt64 := forIn (m := Id) [:count.toNat] seed fun i a =>
                      let next := a + UInt64.ofNat i + 1
                      if exits && next % 7 == 0 then .done next else .yield next
                    let bound := if dependent then a % 7 else count
                    let b : UInt64 := forIn (m := Id) [:bound.toNat] (a + seed) fun i b =>
                      let next := b + a + 2 * UInt64.ofNat i
                      if exits && UInt64.ofNat i % 3 == 0 then .yield b
                      else if exits && next % 11 == 0 then .done next else .yield next
                    let c : UInt64 := forIn (m := Id) [:count.toNat] (b + seed) fun i c =>
                      .yield (c ^^^ UInt64.ofNat i)
                    let expected := if three then c + b + a else b + a
                    let actual := module_.evalFunc 0 [count, seed]
                    unless actual == expected do throwError "sequence capture/state: {actual} != {expected}"
                    comparisons := comparisons + 1
                  for empty in [false, true] do
                    let first := Range.call (if empty then literalExpr 0 else .bvar 1) (.bvar 0) `i `a binder binder firstStep
                    let second := Range.call (if empty then literalExpr 0 else secondBound)
                      (add (.bvar 0) (.bvar 1)) `j `b binder binder secondStep
                    let tail := save second result
                    let invalid := [
                      Lean.Expr.letE `saved boolean first tail nondep,
                      .letE `saved (.const ``Nat []) first tail nondep,
                      .letE `saved (.app (.const ``Id [.succ .zero]) word) first tail nondep,
                      save unknown tail, save first (save unknown result),
                      save first (save second unknown),
                      save (Range.call (literalExpr 0) (.bvar 0) `i `a binder binder
                        (Step.yieldDirect (booleanLiteralExpr true))) tail,
                      save first (save (Range.call (literalExpr 0) (.bvar 0) `j `b binder binder
                        (Step.yieldDirect (booleanLiteralExpr true))) result),
                      save (Range.call (booleanLiteralExpr false) (.bvar 0) `i `a binder binder firstStep) tail,
                      save first (save (Range.call (literalExpr 0) (booleanLiteralExpr true) `j `b binder binder secondStep) result),
                      rawBind type.expr type.expr boolean first tail binder,
                      rawBind (.const ``Nat []) type.expr (.const ``Nat []) first tail binder,
                      rawBind type.expr boolean type.expr first tail binder,
                      .app (.app (.const `unsupportedSequenceBind []) first) (.lam `saved type.expr tail binder),
                      .app (.app (.const ``Id.run [.succ .zero]) type.expr) (save first tail),
                      save unknown (save second (.bvar 0))]
                    for bad in invalid do
                      unless (extractScalarFunc `invalidSequence none signature (wrap (wrapped bad))).isNone do
                        throwError "invalid sequence admitted: empty {empty}, three {three}"
                      rejected := rejected + 1
  unless comparisons == 13824 && rejected == 18432 && controls == 576 do
    throwError "unexpected counts {comparisons}, {rejected}, {controls}"
  Lean.logInfo m!"{comparisons} native/sequential-loop IR comparisons, {rejected} invalid-input tests and {controls} admission controls passed"

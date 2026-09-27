import LeanExe.Extract.ScalarFunc

open LeanExe.Extract.Core
open LeanExe.Source.Scalar

run_elab do
  let word : Lean.Expr := .const ``UInt64 []
  let boolean : Lean.Expr := .const ``Bool []
  let wrap (body : Lean.Expr) := Lean.Expr.lam `count word (.lam `seed word body .default) .default
  let add (a b : Lean.Expr) := Lean.mkAppN (.const ``UInt64.add []) #[a, b]
  let mul (a b : Lean.Expr) := Lean.mkAppN (.const ``UInt64.mul []) #[a, b]
  let mod (a : Lean.Expr) (n : Nat) := Lean.mkAppN (.const ``UInt64.mod []) #[a, literalExpr n]
  let eq (a b : Lean.Expr) := (BooleanLocal.compare .eq a b).expr
  let eqZero (a : Lean.Expr) := eq a (literalExpr 0)
  let toWord (a : Lean.Expr) := Lean.Expr.app (.const ``Bool.toUInt64 []) a
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
  let unknown := Lean.Expr.const `unsupportedBooleanPrefixValue []
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
          for wrapper in ([0, 1, 2] : List Nat) do
            for boolResult in [false, true] do
              let resultType := if boolResult then boolType.expr else wordType.expr
              let signature := Lean.Expr.forallE `count word (.forallE `seed word resultType .default) .default
              let save (value body : Lean.Expr) := if monadic then
                  rawBind boolType.expr resultType boolType.expr value body binder
                else Lean.Expr.letE `saved boolType.expr value body nondep
              let wrapped (source : Lean.Expr) := if wrapper == 0 then source else if wrapper == 1 then
                  if boolResult then BooleanIdentity.run (BooleanIdentity.pure source boolType) (.identity boolType)
                  else Identity.run (Identity.pure source wordType) (.identity wordType)
                else Lean.Expr.mdata {} source
              for dependent in [false, true] do
                for exits in [false, true] do
                  let firstNext := booleanEqualityExpr true (.bvar 0) (eq (mod index 7) (mod (.bvar 2) 7))
                  let firstStep := if exits then choose (BooleanStep.resultType .boolean) (eqZero (mod index 3))
                      (BooleanStep.yieldDirect (.bvar 0))
                      (choose (BooleanStep.resultType .boolean) firstNext
                        (BooleanStep.doneDirect firstNext) (BooleanStep.yieldDirect firstNext))
                    else BooleanStep.yieldDirect firstNext
                  let first := flagRange (.bvar 1) (eqZero (.bvar 0)) firstStep binder
                  let wordNext := choose word (.bvar 2) (add (.bvar 0) index) (add (mul (.bvar 0) (literalExpr 3)) index)
                  let boolNext := booleanEqualityExpr true (.bvar 0) (eq (mod index 7) (mod (.bvar 3) 7))
                  let next := if boolResult then boolNext else wordNext
                  let done := if boolResult then BooleanStep.doneDirect next else Step.doneDirect next
                  let yieldNext := if boolResult then BooleanStep.yieldDirect next else Step.yieldDirect next
                  let condition := if boolResult then next else eqZero (mod next 11)
                  let step := if exits then choose (if boolResult then BooleanStep.resultType .boolean else Step.resultType .word)
                      condition done yieldNext else yieldNext
                  let bound := if dependent then choose word (.bvar 0) (.bvar 2) (mod (.bvar 2) 7) else .bvar 2
                  let initial := if boolResult then .bvar 0 else add (.bvar 1) (toWord (.bvar 0))
                  let second (bound initial step : Lean.Expr) := if boolResult then flagRange bound initial step binder
                    else Range.call bound initial `j `b binder binder step
                  let source := wrapped (save first (second bound initial step))
                  let old := if boolResult then extractScalarBooleanRangeWith (publicBindings (publicInputs signature)) 2 source
                    else extractScalarWordRangeWith (publicBindings (publicInputs signature)) 2 source
                  unless old.isNone do throwError "Boolean prefix control unexpectedly uses a single-loop plan"
                  controls := controls + 1
                  let some func := extractScalarFunc `booleanPrefix (some "entry") signature (wrap source) |
                    throwError "Boolean prefix rejected: depth {depth}, wrapper {wrapper}, Boolean result {boolResult}"
                  let module_ : LeanExe.IR.Module := { funcs := #[func] }
                  for (count, seed) in inputs do
                    let flag : Bool := forIn (m := Id) [:count.toNat] (seed == 0) fun i a =>
                      let next := a != (UInt64.ofNat i % 7 == seed % 7)
                      if exits && UInt64.ofNat i % 3 == 0 then .yield a
                      else if exits && next then .done next else .yield next
                    let n := if dependent then (if flag then count else count % 7) else count
                    let result : UInt64 := if boolResult then
                        (forIn (m := Id) [:n.toNat] flag fun i a =>
                          let next := a != (UInt64.ofNat i % 7 == seed % 7)
                          if exits && next then .done next else .yield next).toUInt64
                      else forIn (m := Id) [:n.toNat] (seed + flag.toUInt64) fun i a =>
                        let next := if flag then a + UInt64.ofNat i else a * 3 + UInt64.ofNat i
                        if exits && next % 11 == 0 then .done next else .yield next
                    let actual := module_.evalFunc 0 [count, seed]
                    unless actual == result do throwError "Boolean prefix capture/state: {actual} != {result}"
                    comparisons := comparisons + 1
                  for empty in [false, true] do
                    let first := flagRange (if empty then literalExpr 0 else .bvar 1) (eqZero (.bvar 0)) firstStep binder
                    let tail := second (if empty then literalExpr 0 else bound) initial step
                    let invalid := [
                      Lean.Expr.letE `saved word first tail nondep,
                      .letE `saved (.const ``Nat []) first tail nondep,
                      .letE `saved (.app (.const ``Id [.succ .zero]) boolean) first tail nondep,
                      save unknown tail, save first unknown,
                      save (flagRange (literalExpr 0) (booleanLiteralExpr false) (BooleanStep.yieldDirect (literalExpr 0)) binder) tail,
                      save (flagRange (literalExpr 0) (literalExpr 0) firstStep binder) tail,
                      save (flagRange (booleanLiteralExpr false) (eqZero (.bvar 0)) firstStep binder) tail,
                      save first (second (booleanLiteralExpr false) initial step),
                      save first (second (literalExpr 0) unknown step),
                      rawBind boolType.expr resultType word first tail binder,
                      rawBind (.const ``Nat []) resultType (.const ``Nat []) first tail binder,
                      rawBind boolType.expr (if boolResult then word else boolean) boolType.expr first tail binder,
                      .app (.app (.const `unsupportedBooleanPrefixBind []) first) (.lam `saved boolType.expr tail binder),
                      .app (.app (.const ``Id.run [.succ .zero]) resultType) (save first tail),
                      save unknown (second (literalExpr 0) (if boolResult then booleanLiteralExpr false else literalExpr 0)
                        (if boolResult then BooleanStep.yieldDirect (.bvar 0) else Step.yieldDirect (.bvar 0)))]
                    for bad in invalid do
                      unless (extractScalarFunc `invalidBooleanPrefix none signature (wrap (wrapped bad))).isNone do
                        throwError "invalid Boolean prefix admitted: empty {empty}, Boolean result {boolResult}"
                      rejected := rejected + 1
  unless comparisons == 13824 && rejected == 18432 && controls == 576 do
    throwError "unexpected counts {comparisons}, {rejected}, {controls}"
  Lean.logInfo m!"{comparisons} native/Boolean-prefix sequential-loop IR comparisons, {rejected} invalid-input tests and {controls} admission controls passed"

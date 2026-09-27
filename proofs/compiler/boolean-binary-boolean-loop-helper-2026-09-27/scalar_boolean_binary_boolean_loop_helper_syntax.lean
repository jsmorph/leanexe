import LeanExe.Extract.ScalarFunc

open LeanExe.Extract.Core
open LeanExe.Source.Scalar

run_elab do
  let word : Lean.Expr := .const ``UInt64 []
  let boolean : Lean.Expr := .const ``Bool []
  let signature := Lean.Expr.forallE `count word (.forallE `seed word boolean .default) .default
  let wrap (body : Lean.Expr) := Lean.Expr.lam `count word (.lam `seed word body .default) .default
  let add (x y : Lean.Expr) := Lean.mkAppN (.const ``UInt64.add []) #[x, y]
  let mul (x y : Lean.Expr) := Lean.mkAppN (.const ``UInt64.mul []) #[x, y]
  let mod7 (x : Lean.Expr) := Lean.mkAppN (.const ``UInt64.mod []) #[x, literalExpr 7]
  let indexWord := Lean.Expr.app (.const ``UInt64.ofNat []) (.bvar 1)
  let call (i : Nat) (x y : Lean.Expr) := Lean.Expr.app (.app (.bvar i) x) y
  let toWord (value : Lean.Expr) := Lean.Expr.app (.const ``Bool.toUInt64 []) value
  let neg (value : Lean.Expr) := Lean.Expr.app (.const ``Bool.not []) value
  let stride : Range.Exit.Stride := ⟨1, by decide, by decide, .const ``Nat.zero_lt_one []⟩
  let range (bound initial step : Lean.Expr) := BooleanAccumulator.call ⟨.const ``Nat [], rfl⟩ stride
    (.literal 0 (by decide)) (.word bound) initial `i `a .default .default step
  let choice (result flag yes no : Lean.Expr) := Lean.mkAppN (.const ``ite [.succ .zero])
    #[result, booleanRelationCondition false flag (booleanLiteralExpr true),
      booleanRelationEvidence false flag (booleanLiteralExpr true), yes, no]
  let inputs : List (UInt64 × UInt64) :=
    ([0, 1, 2, 7, 16, 31] : List UInt64).flatMap fun n =>
      ([0, 1, 0x8000000000000000, 0xffffffffffffffff] : List UInt64).map fun seed => (n, seed)
  let mut comparisons : Nat := 0
  let mut rejected : Nat := 0
  let mut controls : Nat := 0
  for depth in [0, 1, 2] do
    let result := (List.range depth).foldl (fun type _ => BooleanType.identity type) .boolean
    for firstInfo in [Lean.BinderInfo.default, .implicit] do
      for secondInfo in [Lean.BinderInfo.default, .strictImplicit] do
        for nondep in [false, true] do
          for wrapped in [false, true] do
            let rawBody := (BooleanLocal.compare .eq
              (mod7 (add (.bvar 1) (mul (literalExpr 3) (.bvar 0)))) (mod7 (.bvar 2))).expr
            let body := if wrapped then BooleanIdentity.run (BooleanIdentity.pure rawBody result) (.identity result) else rawBody
            let helper (firstType secondType firstDomain secondDomain output value tail : Lean.Expr) :=
              Lean.Expr.letE `f (.forallE `a firstType (.forallE `b secondType output secondInfo) firstInfo)
                (.lam `a firstDomain (.lam `b secondDomain value secondInfo) firstInfo) tail nondep
            let typed := helper word word word word result.expr
            for disjoin in [false, true] do
              for mode in ([0, 1, 2, 3] : List Nat) do
                let flag := Lean.mkAppN (.const (if disjoin then ``Bool.or else ``Bool.and) [])
                  #[call 2 indexWord (toWord (.bvar 0)), call 2 (.bvar 3) indexWord]
                let next := booleanEqualityExpr true (.bvar 0)
                  (BooleanLocal.compare .eq (Lean.mkAppN (.const ``UInt64.mod []) #[indexWord, literalExpr 3]) (literalExpr 0)).expr
                let step := if mode == 1 then BooleanStep.yieldDirect next else
                  choice (BooleanStep.resultType .boolean) flag
                    (BooleanStep.doneDirect (neg (.bvar 0))) (BooleanStep.yieldDirect next)
                let bound := if mode == 2 then
                    choice word (call 0 (.bvar 2) (.bvar 1)) (.bvar 2) (mod7 (.bvar 2))
                  else .bvar 2
                let start := (BooleanLocal.compare .eq (.bvar 1) (literalExpr 0)).expr
                let initial := if mode == 2 then
                    choice boolean (call 0 (.bvar 1) (literalExpr 1)) (neg start) start
                  else start
                let loop := range bound initial step
                let tail := if mode == 3 then Lean.Expr.letE `saved boolean loop
                    (Lean.mkAppN (.const ``Bool.or [])
                      #[call 1 (toWord (.bvar 0)) (.bvar 2), call 1 (.bvar 2) (toWord (.bvar 0))]) nondep
                  else loop
                let source := typed body tail
                unless (booleanBinaryHelper? source).isSome do throwError "outer binary helper recognition failed"
                controls := controls + 1
                let some func := extractScalarFunc `binaryBooleanLoopHelper (some "entry") signature (wrap source) |
                  throwError "outer binary helper rejected: depth {depth}, mode {mode}"
                let module_ : LeanExe.IR.Module := { funcs := #[func] }
                for (count, seed) in inputs do
                  let f := fun x y : UInt64 => (x + 3 * y) % 7 == seed % 7
                  let n := if mode == 2 then (if f count seed then count else count % 7) else count
                  let initial := if mode == 2 then (if f seed 1 then !(seed == 0) else seed == 0) else seed == 0
                  let accumulated : Bool := forIn (m := Id) [:n.toNat] initial fun i a =>
                    let flag := if disjoin then f (UInt64.ofNat i) a.toUInt64 || f seed (UInt64.ofNat i)
                      else f (UInt64.ofNat i) a.toUInt64 && f seed (UInt64.ofNat i)
                    if mode != 1 && flag then .done (!a) else .yield (a != (UInt64.ofNat i % 3 == 0))
                  let expected := if mode == 3 then f accumulated.toUInt64 seed || f seed accumulated.toUInt64
                    else accumulated
                  let actual := module_.evalFunc 0 [count, seed]
                  unless actual == expected.toUInt64 do throwError "outer binary helper capture/order: {actual} != {expected}, mode {mode}"
                  comparisons := comparisons + 1
                let unknown := Lean.Expr.const `unsupportedBinaryWordLoopHelper []
                for empty in [false, true] do
                  let loop (step : Lean.Expr) := range (if empty then literalExpr 0 else .bvar 2)
                    (BooleanLocal.compare .eq (.bvar 1) (literalExpr 0)).expr step
                  let tail := loop step
                  let yieldFlag (flag : Lean.Expr) := loop (BooleanStep.yieldDirect flag)
                  let invalid := [
                    helper boolean word word word result.expr body tail,
                    helper word boolean word word result.expr body tail,
                    helper word word boolean word result.expr body tail,
                    helper word word word boolean result.expr body tail,
                    helper (.app (.const ``Id [.zero]) word) word word word result.expr body tail,
                    helper word (.const ``Nat []) word word result.expr body tail,
                    helper word word word (.const ``Nat []) result.expr body tail,
                    helper word word word word (.app (.const ``Id [.succ .zero]) boolean) body tail,
                    helper word word word word word body tail,
                    typed unknown tail, typed (literalExpr 0) tail, typed body unknown,
                    typed unknown (loop (BooleanStep.yieldDirect (.bvar 0))),
                    typed body (loop (BooleanStep.yieldDirect (literalExpr 0))),
                    typed body (yieldFlag (.bvar 2)), typed body (yieldFlag (.app (.bvar 2) (.bvar 3))),
                    typed body (yieldFlag (.app (call 2 (.bvar 3) indexWord) (.bvar 3))),
                    typed body (yieldFlag (call 99 (.bvar 3) indexWord)),
                    typed body (yieldFlag (call 2 (booleanLiteralExpr true) (.bvar 3))),
                    typed body (yieldFlag (call 2 (.bvar 3) (booleanLiteralExpr false))),
                    typed body (yieldFlag (call 2 unknown (.bvar 3))),
                    typed body (yieldFlag (call 2 (.bvar 3) unknown)),
                    typed body (loop (BooleanStep.yieldDirect (toWord (call 2 (.bvar 3) indexWord))))]
                  for bad in invalid do
                    unless (extractScalarFunc `invalidBinaryBooleanLoopHelper none signature (wrap bad)).isNone do
                      throwError "invalid outer binary helper admitted: mode {mode}, empty {empty}"
                    rejected := rejected + 1
  unless comparisons == 9216 && rejected == 17664 && controls == 384 do
    throwError "unexpected counts {comparisons}, {rejected}, {controls}"
  Lean.logInfo m!"{comparisons} native/outer binary Boolean-result loop IR comparisons, {rejected} invalid-input tests and {controls} admission controls passed"

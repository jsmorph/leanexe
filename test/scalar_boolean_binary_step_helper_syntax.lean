import LeanExe.Extract.ScalarFunc

open LeanExe.Extract.Core
open LeanExe.Source.Scalar

run_elab do
  let word : Lean.Expr := .const ``UInt64 []
  let boolean : Lean.Expr := .const ``Bool []
  let signature := Lean.Expr.forallE `count word (.forallE `seed word word .default) .default
  let wrap (empty : Bool) (body : Lean.Expr) := Lean.Expr.lam `count word (.lam `seed word
    (Range.call (if empty then literalExpr 0 else .bvar 1) (.bvar 0) `i `a .default .default body) .default) .default
  let add (x y : Lean.Expr) := Lean.mkAppN (.const ``UInt64.add []) #[x, y]
  let mul (x y : Lean.Expr) := Lean.mkAppN (.const ``UInt64.mul []) #[x, y]
  let mod7 (x : Lean.Expr) := Lean.mkAppN (.const ``UInt64.mod []) #[x, literalExpr 7]
  let index (i : Nat) := Lean.Expr.app (.const ``UInt64.ofNat []) (.bvar i)
  let call (i : Nat) (x y : Lean.Expr) := Lean.Expr.app (.app (.bvar i) x) y
  let junction (disjoin : Bool) (x y : Lean.Expr) := Lean.mkAppN
    (.const (if disjoin then ``Bool.or else ``Bool.and) []) #[x, y]
  let toWord (value : Lean.Expr) := Lean.Expr.app (.const ``Bool.toUInt64 []) value
  let branch (flag : Lean.Expr) (a i : Nat) := Lean.mkAppN (.const ``ite [.succ .zero])
    #[Step.resultType .word,
      Lean.mkAppN (.const ``Eq [.succ .zero]) #[boolean, flag, booleanLiteralExpr true],
      Lean.mkAppN (.const ``instDecidableEqBool []) #[flag, booleanLiteralExpr true],
      Step.doneDirect (add (.bvar a) (literalExpr 7)),
      Step.yieldDirect (add (add (.bvar a) (index i)) (literalExpr 1))]
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
                let calls := junction disjoin (call 0 (index 2) (.bvar 1)) (call 0 (.bvar 3) (index 2))
                let tail := if mode == 1 then Step.yieldDirect (add (add (.bvar 1) (index 2)) (literalExpr 1))
                  else if mode == 2 then typed
                    (.app (.const ``Bool.not []) (call 2 (.bvar 1) (.bvar 0)))
                    (branch (junction disjoin (call 0 (index 3) (.bvar 2)) (call 0 (.bvar 4) (index 3))) 2 3)
                  else if mode == 3 then Lean.Expr.letE `saved boolean (call 0 (index 2) (.bvar 1))
                    (branch (junction disjoin (.bvar 0) (call 1 (.bvar 4) (index 3))) 2 3) nondep
                  else branch calls 1 2
                let source := typed body tail
                unless (booleanBinaryHelper? source).isSome do throwError "binary step helper recognition failed"
                controls := controls + 1
                let some func := extractScalarFunc `binaryStepHelper (some "entry") signature (wrap false source) |
                  throwError "binary step helper rejected: depth {depth}, mode {mode}"
                let module_ : LeanExe.IR.Module := { funcs := #[func] }
                for (count, seed) in inputs do
                  let expected := forIn (m := Id) [:count.toNat] seed fun i a =>
                    let f := fun x y : UInt64 => (x + 3 * y) % 7 == a % 7
                    let g := fun x y => if mode == 2 then !(f x y) else f x y
                    let flag := if disjoin then g (UInt64.ofNat i) a || g seed (UInt64.ofNat i)
                      else g (UInt64.ofNat i) a && g seed (UInt64.ofNat i)
                    if mode != 1 && flag then .done (a + 7) else .yield (a + UInt64.ofNat i + 1)
                  let actual := module_.evalFunc 0 [count, seed]
                  unless actual == expected do throwError "binary step helper order/capture: {actual} != {expected}, mode {mode}"
                  comparisons := comparisons + 1
                let unknown := Lean.Expr.const `unsupportedBinaryStepHelper []
                let yieldFlag (flag : Lean.Expr) := Step.yieldDirect (toWord flag)
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
                  typed unknown (Step.yieldDirect (.bvar 1)),
                  typed body (Step.yieldDirect (.bvar 0)),
                  typed body (yieldFlag (.bvar 0)), typed body (yieldFlag (.app (.bvar 0) (.bvar 1))),
                  typed body (yieldFlag (.app (call 0 (.bvar 1) (.bvar 3)) (.bvar 1))),
                  typed body (yieldFlag (call 9 (.bvar 1) (.bvar 3))),
                  typed body (yieldFlag (call 0 (booleanLiteralExpr true) (.bvar 1))),
                  typed body (yieldFlag (call 0 (.bvar 1) (booleanLiteralExpr false))),
                  typed body (yieldFlag (call 0 unknown (.bvar 1))),
                  typed body (yieldFlag (call 0 (.bvar 1) unknown)),
                  typed body (Step.yieldDirect (call 0 (.bvar 1) (.bvar 3)))]
                for bad in invalid do
                  for empty in [false, true] do
                    unless (extractScalarFunc `invalidBinaryStepHelper none signature (wrap empty bad)).isNone do
                      throwError "invalid binary step helper admitted: mode {mode}, empty {empty}"
                    rejected := rejected + 1
  unless comparisons == 9216 && rejected == 17664 && controls == 384 do
    throwError "unexpected counts {comparisons}, {rejected}, {controls}"
  Lean.logInfo m!"{comparisons} native/binary Boolean step helper IR comparisons, {rejected} invalid-input tests and {controls} admission controls passed"

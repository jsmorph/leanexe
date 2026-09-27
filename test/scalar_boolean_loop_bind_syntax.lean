import LeanExe.Extract.ScalarFunc

open LeanExe.Extract.Core
open LeanExe.Source.Scalar

run_elab do
  let word : Lean.Expr := .const ``UInt64 []
  let boolean : Lean.Expr := .const ``Bool []
  let toWord (value : Lean.Expr) := Lean.Expr.app (.const ``Bool.toUInt64 []) value
  let add (a b : Lean.Expr) := Lean.Expr.app (.app (.const ``UInt64.add []) a) b
  let modWord (a b : Lean.Expr) := Lean.Expr.app (.app (.const ``UInt64.mod []) a) b
  let indexWord (i : Nat) := Lean.Expr.app (.const ``UInt64.ofNat []) (.bvar i)
  let inputs : List (UInt64 × UInt64) :=
    [(0, 0), (1, 0), (0, 1), (1, 1), (42, 3), (3, 17), (17, 3),
     (0xffffffffffffffff, 0), (0xffffffffffffffff, 1),
     (0x8000000000000000, 2), (0xffffffffffffffff, 63),
     (0x8000000000000001, 64), (0xffffffffffffffff, 65),
     (0x0123456789abcdef, 0xffffffffffffffff)]
  let mut comparisons : Nat := 0
  let mut rejected : Nat := 0
  let mut controls : Nat := 0
  for depth in ([0, 2] : List Nat) do
    for inputDepth in ([0, 2] : List Nat) do
      for flagFirst in [false, true] do
        let domains := (if flagFirst then [boolean, word] else [word, boolean]).map fun input =>
          (List.range depth).foldl (fun value _ => Lean.Expr.app (.const ``Id [.zero]) value) input
        let resultType := (List.range depth).foldl (fun value _ => BooleanType.identity value) .boolean
        let inputType := (List.range inputDepth).foldl (fun value _ => ResultType.identity value) .word
        let flagIndex := if flagFirst then 1 else 0
        let wordIndex := if flagFirst then 0 else 1
        for binder in [Lean.BinderInfo.default, .implicit, .strictImplicit, .instImplicit] do
          for nondep in [false, true] do
            for kind in ([0, 1, 2] : List Nat) do
              for wrapper in ([0, 1, 2, 3] : List Nat) do
                for form in ([0, 1, 2] : List Nat) do
                  let signature := domains.foldr
                    (fun input rest => Lean.Expr.forallE `parameter input rest binder) resultType.expr
                  let wrap (body : Lean.Expr) := domains.foldr
                    (fun input rest => Lean.Expr.lam `parameter input rest binder) body
                  let outer (body : Lean.Expr) := if wrapper == 0 then body
                    else if wrapper == 1 then BooleanIdentity.run body resultType
                    else if wrapper == 2 then BooleanIdentity.pure body resultType
                    else Lean.Expr.mdata {} body
                  let flag : BooleanLocal := .var 0 (flagIndex + 2)
                  let choose : BooleanLocalGuard := { value := flag, expanded := rfl }
                  let even : BooleanLocal := .junction 0 .conjunction flag
                    (.compare .eq (modWord (indexWord 1) (literalExpr 2)) (literalExpr 0))
                  let skip : BooleanLocalGuard := { value := even, expanded := rfl }
                  let advanced := add (add (.bvar 0) (indexWord 1)) (literalExpr 1)
                  let step := if kind == 0 then choose.branch (Step.resultType .word)
                      (Step.yieldDirect advanced) (Step.yieldDirect (add (.bvar 0) (literalExpr 3)))
                    else if kind == 1 then choose.branch (Step.resultType .word)
                      (Step.doneDirect (add (.bvar 0) (literalExpr 7))) (Step.yieldDirect advanced)
                    else skip.branch (Step.resultType .word) (Step.yieldDirect (.bvar 0)) (Step.yieldDirect advanced)
                  let loop (step : Lean.Expr) := Range.call (modWord (.bvar wordIndex) (literalExpr 17))
                    (add (.bvar wordIndex) (toWord (.bvar flagIndex))) `i `a binder binder step
                  let equal : BooleanLocal := .compare .eq (.bvar 0) (.bvar (wordIndex + 1))
                  let tail : BooleanLocal := if form == 0 then equal
                    else if form == 1 then .junction 0 .disjunction equal (.var 0 (flagIndex + 1))
                    else .binding 0 `saved (.letE nondep) equal (.var 1 0)
                  let source (value body : Lean.Expr) := wrap (outer (BooleanRange.bind `value binder inputType resultType value body))
                  let bindInstance := Lean.mkAppN (.const ``Monad.toBind [.zero, .zero])
                    #[.const ``Id [.zero], .const ``Id.instMonad [.zero]]
                  let rawBind (head input domain output evidence : Lean.Expr) := wrap (outer (
                    Lean.mkAppN head #[.const ``Id [.zero], evidence, input, output, loop step,
                      .lam `value domain tail.expr binder]))
                  let some func := extractScalarFunc `booleanLoopResult (some "entry") signature (source (loop step) tail.expr) |
                    throwError "Boolean loop result rejected: {depth}, {flagFirst}, {kind}, {wrapper}, {form}"
                  let some letFunc := extractScalarFunc `booleanLoopResult (some "entry") signature
                      (wrap (outer (.letE `value word (loop step) tail.expr nondep))) |
                    throwError "previous explicit-let control rejected"
                  unless letFunc == func do throwError "monadic binding changes compiled loop result"
                  controls := controls + 1
                  let module_ : LeanExe.IR.Module := { funcs := #[func] }
                  for (x, y) in inputs do
                    let rawFlag := if flagFirst then x else y
                    let rawWord := if flagFirst then y else x
                    let flag := rawFlag != 0
                    let value : UInt64 := Id.run <| forIn (m := Id) [:(rawWord % 17).toNat] (rawWord + flag.toUInt64) fun i a =>
                      if kind == 0 then .yield (if flag then a + i.toUInt64 + 1 else a + 3)
                      else if kind == 1 then
                        if flag then .done (a + 7) else .yield (a + i.toUInt64 + 1)
                      else .yield (if flag && i % 2 == 0 then a else a + i.toUInt64 + 1)
                    let same := value == rawWord
                    let expected := (if form == 0 then same else if form == 1 then same || flag else !same).toUInt64
                    let actual := module_.evalFunc 0 [x, y]
                    unless actual == expected && (actual == 0 || actual == 1) do
                      throwError "Boolean loop result: {actual}, expected {expected}"
                    comparisons := comparisons + 1
                  let dead : BooleanLocalGuard := { value := .var 0 (flagIndex + 1), expanded := rfl }
                  let badTail := Lean.Expr.const `unsupportedBooleanTail []
                  let bindHead := Lean.Expr.const ``Bind.bind [.zero, .zero]
                  let invalid := [
                    rawBind bindHead inputType.expr boolean resultType.expr bindInstance,
                    rawBind bindHead inputType.expr inputType.expr word bindInstance,
                    rawBind bindHead boolean boolean resultType.expr bindInstance,
                    rawBind bindHead (.app (.const `CustomId [.zero]) word) inputType.expr resultType.expr bindInstance,
                    rawBind bindHead inputType.expr inputType.expr resultType.expr (.const `customBindInstance []),
                    rawBind (.const ``Bind.bind [.zero]) inputType.expr inputType.expr resultType.expr bindInstance,
                    rawBind (.const `customBind [.zero, .zero]) inputType.expr inputType.expr resultType.expr bindInstance,
                    rawBind bindHead (.app (.const ``Id [.succ .zero]) word)
                      (.app (.const ``Id [.succ .zero]) word) resultType.expr bindInstance,
                    source (loop step) (.bvar 0),
                    source (loop step) badTail,
                    source (loop step) (.bvar 99),
                    source (loop step) (BooleanLocal.var 0 (wordIndex + 1)).expr,
                    source (loop step) (dead.branch boolean tail.expr badTail),
                    source (loop step) (.letE `unused word (.bvar (flagIndex + 1)) (tail.expr.liftLooseBVars 0 1) nondep),
                    source (loop (Step.yieldDirect (.bvar (flagIndex + 2)))) tail.expr,
                    source (loop (choose.branch (Step.resultType .word) (Step.yieldDirect (.bvar 0))
                      (Step.yieldDirect (.const `unsupportedLoopStep [])))) tail.expr,
                    wrap (outer (.letE `wrong boolean (loop step) tail.expr nondep)),
                    wrap (Lean.Expr.app (.app (.const ``Id.run [.succ .zero]) boolean)
                      (.letE `value word (loop step) tail.expr nondep)),
                    wrap (Lean.Expr.app (.app (.const `CustomRun [.zero]) boolean)
                      (.letE `value word (loop step) tail.expr nondep)),
                    wrap (Lean.Expr.app (.app (.const ``Id.run [.zero]) word)
                      (.letE `value word (loop step) tail.expr nondep))]
                  for value in invalid do
                    if (extractScalarFunc `invalidBooleanLoopResult (some "entry") signature value).isSome then
                      throwError "invalid Boolean loop result accepted: {depth}, {kind}, {form}"
                    rejected := rejected + 1
  unless comparisons == 32256 && rejected == 46080 && controls == 2304 do
    throwError "unexpected counts {comparisons}, {rejected}, {controls}"
  Lean.logInfo m!"{comparisons} native/Boolean loop-bind syntax comparisons, {rejected} invalid-input tests and {controls} explicit-let controls passed"

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
  for inputDepth in ([1, 3] : List Nat) do
    for flagFirst in [false, true] do
      let domains := (if flagFirst then [boolean, word] else [word, boolean]).map fun input =>
        (List.range inputDepth).foldl (fun value _ => Lean.Expr.app (.const ``Id [.zero]) value) input
      let flagIndex := if flagFirst then 1 else 0
      let wordIndex := if flagFirst then 0 else 1
      for alias in [false, true] do
        for negations in ([0, 1, 2] : List Nat) do
          for kind in ([0, 1, 2] : List Nat) do
            for binder in [Lean.BinderInfo.default, .implicit, .strictImplicit, .instImplicit] do
              for depth in ([0, 2] : List Nat) do
                for nondep in [false, true] do
                  let result := (List.range depth).foldl
                    (fun value _ => Lean.Expr.app (.const ``Id [.zero]) value) word
                  let signature := domains.foldr
                    (fun input rest => Lean.Expr.forallE `parameter input rest binder) result
                  let wrap (body : Lean.Expr) := domains.foldr
                    (fun input rest => Lean.Expr.lam `parameter input rest binder) body
                  let n := modWord (.bvar wordIndex) (literalExpr 17)
                  let seed := add (.bvar wordIndex) (toWord (.bvar flagIndex))
                  let flag : BooleanLocal := .var (if alias then 0 else negations)
                    (if alias then 2 else flagIndex + 2)
                  let choose : BooleanLocalGuard := { value := flag, expanded := rfl }
                  let pair : BooleanLocal := .junction 0 .conjunction flag
                    (.compare .eq (modWord (indexWord 1) (literalExpr 2)) (literalExpr 0))
                  let skip : BooleanLocalGuard := { value := pair, expanded := rfl }
                  let advanced := add (add (.bvar 0) (indexWord 1)) (literalExpr 1)
                  let step := if kind == 0 then choose.branch (Step.resultType .word)
                      (Step.yieldDirect advanced) (Step.yieldDirect (add (.bvar 0) (literalExpr 3)))
                    else if kind == 1 then choose.branch (Step.resultType .word)
                      (Step.doneDirect (add (.bvar 0) (literalExpr 7))) (Step.yieldDirect advanced)
                    else skip.branch (Step.resultType .word) (Step.yieldDirect (.bvar 0)) (Step.yieldDirect advanced)
                  let source (body : Lean.Expr) := wrap (
                    if alias then .letE `saved boolean (BooleanGuardNegation.expr negations (.bvar flagIndex))
                      (Range.call (n.liftLooseBVars 0 1) (seed.liftLooseBVars 0 1) `i `a binder binder body) nondep
                    else Range.call n seed `i `a binder binder body)
                  let some func := extractScalarFunc `publicLoopParameters (some "entry") signature (source step) |
                    throwError "public loop input rejected: {flagFirst}, {alias}, {negations}, {kind}"
                  let module_ : LeanExe.IR.Module := { funcs := #[func] }
                  for (x, y) in inputs do
                    let rawFlag := if flagFirst then x else y
                    let rawWord := if flagFirst then y else x
                    let flag := GuardNegation.denote negations (rawFlag != 0)
                    let initial := rawWord + (rawFlag != 0).toUInt64
                    let expected := forIn (m := Id) [:(rawWord % 17).toNat] initial fun i a =>
                      if kind == 0 then .yield (if flag then a + i.toUInt64 + 1 else a + 3)
                      else if kind == 1 then
                        if flag then .done (a + 7) else .yield (a + i.toUInt64 + 1)
                      else .yield (if flag && i % 2 == 0 then a else a + i.toUInt64 + 1)
                    let actual := module_.evalFunc 0 [x, y]
                    unless actual == expected do throwError "public loop input: {actual}, expected {expected}"
                    comparisons := comparisons + 1
                  let flagSlot := if alias then 2 else flagIndex + 2
                  let wordSlot := wordIndex + 2 + if alias then 1 else 0
                  let wrong : BooleanLocalGuard := { value := .var 0 wordSlot, expanded := rfl }
                  let bad := Step.yieldDirect (.bvar flagSlot)
                  let invalid := [
                    source bad,
                    source (Step.yieldDirect (toWord (.bvar wordSlot))),
                    source (wrong.branch (Step.resultType .word) (Step.yieldDirect (.bvar 0)) (Step.yieldDirect (.bvar 0))),
                    source (Step.yieldDirect (.const `unsupportedLoopInput [])),
                    source (choose.branch (Step.resultType .word) (Step.yieldDirect (.bvar 0)) bad),
                    source (.letE `unused word (.bvar flagSlot) (Step.yieldDirect (.bvar 1)) nondep),
                    Lean.Expr.lam `wrong word (.lam `wrong word (Range.call n seed `i `a binder binder step) binder) binder]
                  for value in invalid do
                    if (extractScalarFunc `invalidPublicLoopInput (some "entry") signature value).isSome then
                      throwError "invalid loop input use admitted: {flagFirst}, {alias}, {kind}"
                    rejected := rejected + 1
  unless comparisons == 16128 && rejected == 8064 do
    throwError "unexpected counts {comparisons}, {rejected}"
  Lean.logInfo m!"{comparisons} native/public loop parameter-Id syntax comparisons and {rejected} invalid-input tests passed"

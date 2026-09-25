import LeanExe.Extract.ScalarFunc

namespace BooleanDependentTest

def booleanDependentLet (x y : UInt64) : UInt64 :=
  let equal := x == y
  if _h : equal then x + y * 3 else x - y * 5

def booleanDependentAlias (x y : UInt64) : UInt64 :=
  let equal := x == y
  let alias := equal
  let inverted := !!!alias
  if _h : inverted then ~~~x else ~~~y

def booleanDependentShadow (x y : UInt64) : UInt64 :=
  let flag := x != y
  let f := fun a b : UInt64 => if _h : flag then a + b else a - b
  let flag := y == 0
  if _h : flag then f x y else f y x

def booleanDependentCompound (x y : UInt64) : UInt64 :=
  let equal := x == y
  let zero := x == 0 || y == 0
  let flag := !equal && !(zero || y == 1)
  if _h : flag || (!zero && equal) then x + 13 else y - 17

def booleanDependentNestedOperand (x y : UInt64) : UInt64 :=
  let flag := x == 0
  let a := if _h : flag then x + y else x - y
  let next := (if _h : flag then a else y) == (if _h : x < y then x else a)
  if _h : next && !flag then a + 7 else a - 3

def booleanDependentUnused (x y : UInt64) : UInt64 :=
  let _flag := (x / 0 == y) && (y % 0 != x)
  let kept := true
  let alias := kept
  if _h : alias then x + y else ~~~x

def booleanDependentMany (x y : UInt64) : UInt64 :=
  let five : UInt64 := 5
  let outer := x != y
  let f := fun a b c : UInt64 =>
    let inner := a == b || b == c
    if _h : outer && !inner then a + b * 3 - c else a - b * five + c
  f x y (x + 7)

def booleanDependentDo (x y : UInt64) : UInt64 := Id.run do
  let flag := x == y
  let mut a := x
  if _h : flag then a := a + y else a := a - y
  let next := a % 3 == 0
  let z ← if _h : next && !flag then pure (a * 7) else pure (a + 5)
  return z ^^^ y

def rangeBooleanDependentYield (count seed : UInt64) : UInt64 := Id.run do
  let mut a := seed
  for i in [:count.toNat] do
    let even := UInt64.ofNat i % 2 == 0
    if _h : even then a := a + 3 else a := a + 7
  return a

def rangeBooleanDependentBreak (count seed : UInt64) : UInt64 := Id.run do
  let mut a := seed
  for i in [:count.toNat] do
    a := a + UInt64.ofNat i + 1
    let stop := a % 7 == 0 || UInt64.ofNat i == 12
    if _h : stop then break
  return a

def rangeBooleanDependentContinue (count seed : UInt64) : UInt64 := Id.run do
  let mut a := seed
  for i in [:count.toNat] do
    let skip := UInt64.ofNat i % 3 == 1
    if _h : skip then continue
    a := a + UInt64.ofNat i
    let stop := a % 11 == 0
    if _h : stop && !skip then break
  return a

def rangeBooleanDependentCapture (count seed : UInt64) : UInt64 := Id.run do
  let mut a := seed
  for i in [:count.toNat] do
    let captured := a % 5 == 0
    let f := fun x y : UInt64 => if _h : captured then x + y else x - y
    a := a + UInt64.ofNat i + 1
    let captured := a % 7 == 0
    a := f a seed
    if _h : captured then break
  return a

def rangeBooleanDependentJoined (count seed : UInt64) : UInt64 := Id.run do
  let mut a := seed
  for i in [:count.toNat] do
    let even := a % 2 == 0
    if _h : even then a := a + 2 else a := a + 5
    let z ← if _h : !even then pure (a - 1) else pure (a + 3)
    a := z + UInt64.ofNat i
    let stop := a % 13 == 0
    if _h : stop then break
  let changed := a != seed
  return if _h : changed then a + count else a - count

def rangeBooleanDependentOuter (count seed : UInt64) : UInt64 :=
  let flag := seed % 3 == 0
  let f := fun x y z : UInt64 => if _h : flag then x + y - z else x - y + z
  let result := Id.run do
    let mut a := seed
    for i in [:count.toNat] do
      a := f a (UInt64.ofNat i) count
      let stop := a == 0
      if _h : stop && flag then break
    return a
  if _h : flag then result + seed else result - count

def rangeBooleanDependentBounds (count seed : UInt64) : UInt64 := Id.run do
  let flag := seed % 3 == 0
  let first : UInt64 := if _h : flag then 0 else 2
  let stop := if _h : !flag && count != 0 then count - 1 else count
  let mut a := seed
  for i in [first.toNat:stop.toNat:2] do
    let finish := a % 7 == 0
    if _h : finish && flag then break
    a := a + UInt64.ofNat i
  return a

def rangeBooleanDependentStep (count seed : UInt64) : UInt64 :=
  forIn (m := Id) [:count.toNat] seed fun i a =>
    let captured := a % 5 == 0
    let f : UInt64 → UInt64 → UInt64 → ForInStep UInt64 := fun x y z =>
      let localFlag := x == y || y == z
      if _h : captured && localFlag then .done (x + y - z)
      else .yield (x - y + z)
    f a (UInt64.ofNat i) count

def booleanDependentInactiveUnsupported (x y : UInt64) : UInt64 :=
  let flag := true
  if _h : flag then x else UInt64.ofNat (toString y).length

def booleanDependentCustomDecision (x y : UInt64) : UInt64 :=
  let flag := x == y
  @dite UInt64 (flag = true) (if h : flag then .isTrue h else .isFalse h)
    (fun _ => x) (fun _ => y)

def booleanDependentUnusedUnsupported (x y : UInt64) : UInt64 :=
  let flag := false
  let _f := fun a b : UInt64 => if _h : flag then UInt64.ofNat (toString a).length else b
  x + y

def rangeBooleanDependentInactiveUnsupported (count seed : UInt64) : UInt64 :=
  forIn (m := Id) [:count.toNat] seed fun _ a =>
    let flag := false
    if _h : flag then .done (UInt64.ofNat (toString a).length) else .yield (a + 1)

def inputs : List (UInt64 × UInt64) :=
  [(0, 0), (1, 0), (0xffffffffffffffff, 0), (0, 1), (1, 1),
   (0xffffffffffffffff, 1), (0x8000000000000000, 2), (42, 3),
   (0xffffffffffffffff, 63), (0x8000000000000001, 64), (0xffffffffffffffff, 65),
   (0x0123456789abcdef, 0xffffffffffffffff), (3, 17), (17, 3)]

end BooleanDependentTest

run_elab do
  let env ← Lean.getEnv
  let cases : List (Lean.Name × (UInt64 → UInt64 → UInt64) × Bool) := [
    (`BooleanDependentTest.booleanDependentLet, BooleanDependentTest.booleanDependentLet, false),
    (`BooleanDependentTest.booleanDependentAlias, BooleanDependentTest.booleanDependentAlias, false),
    (`BooleanDependentTest.booleanDependentShadow, BooleanDependentTest.booleanDependentShadow, false),
    (`BooleanDependentTest.booleanDependentCompound, BooleanDependentTest.booleanDependentCompound, false),
    (`BooleanDependentTest.booleanDependentNestedOperand, BooleanDependentTest.booleanDependentNestedOperand, false),
    (`BooleanDependentTest.booleanDependentUnused, BooleanDependentTest.booleanDependentUnused, false),
    (`BooleanDependentTest.booleanDependentMany, BooleanDependentTest.booleanDependentMany, false),
    (`BooleanDependentTest.booleanDependentDo, BooleanDependentTest.booleanDependentDo, false),
    (`BooleanDependentTest.rangeBooleanDependentYield, BooleanDependentTest.rangeBooleanDependentYield, true),
    (`BooleanDependentTest.rangeBooleanDependentBreak, BooleanDependentTest.rangeBooleanDependentBreak, true),
    (`BooleanDependentTest.rangeBooleanDependentContinue, BooleanDependentTest.rangeBooleanDependentContinue, true),
    (`BooleanDependentTest.rangeBooleanDependentCapture, BooleanDependentTest.rangeBooleanDependentCapture, true),
    (`BooleanDependentTest.rangeBooleanDependentJoined, BooleanDependentTest.rangeBooleanDependentJoined, true),
    (`BooleanDependentTest.rangeBooleanDependentOuter, BooleanDependentTest.rangeBooleanDependentOuter, true),
    (`BooleanDependentTest.rangeBooleanDependentBounds, BooleanDependentTest.rangeBooleanDependentBounds, true),
    (`BooleanDependentTest.rangeBooleanDependentStep, BooleanDependentTest.rangeBooleanDependentStep, true)]
  for (name, native, isRange) in cases do
    let some info := env.find? name | throwError "missing declaration"
    let some value := info.value? | throwError "missing body"
    let some func := LeanExe.Extract.Core.extractScalarFunc name (some "entry") info.type value |
      throwError "{name}: dependent conditional extraction failed"
    let module_ : LeanExe.IR.Module := { funcs := #[func] }
    let inputs := if isRange then
      ([0, 1, 2, 7, 16, 31] : List UInt64).flatMap fun n =>
        ([0, 1, 0x8000000000000000, 0xffffffffffffffff] : List UInt64).map fun seed => (n, seed)
      else BooleanDependentTest.inputs
    for (x, y) in inputs do
      let expected := native x y
      let actual := module_.evalFunc 0 [x, y]
      unless actual == expected do
        throwError "{name}({x}, {y}): native={expected}, IR={actual}"
  for name in [`BooleanDependentTest.booleanDependentInactiveUnsupported, `BooleanDependentTest.booleanDependentCustomDecision, `BooleanDependentTest.booleanDependentUnusedUnsupported, `BooleanDependentTest.rangeBooleanDependentInactiveUnsupported] do
    let some info := env.find? name | throwError "missing declaration"
    let some value := info.value? | throwError "missing body"
    unless (LeanExe.Extract.Core.extractScalarFunc name (some "entry") info.type value).isNone do
      throwError "{name}: unsupported dependent conditional accepted"
  let guard : LeanExe.Source.Scalar.BooleanLocalGuard := ⟨.var 0 0, by decide⟩
  let word := LeanExe.Source.Scalar.literalExpr 1
  let step := LeanExe.Source.Scalar.Step.yieldDirect word
  let make (type body td fd : Lean.Expr) :=
    Lean.mkAppN (.const ``dite [.succ .zero]) #[type, guard.condition, guard.evidence,
      .lam `h td body .default, .lam `h fd body .default]
  let neg := Lean.Expr.app (.const ``Not []) guard.condition
  for (td, fd) in [(Lean.Expr.const ``UInt64 [], neg), (guard.condition, guard.condition)] do
    unless (LeanExe.Extract.Core.extractScalarExprWith [.boolean (.u64 1)]
        (make (.const ``UInt64 []) word td fd)).isNone do
      throwError "wrong scalar proof-lambda domain accepted"
    unless (LeanExe.Extract.Core.extractScalarStepWith [.scalar (.boolean (.u64 1))]
        (make (LeanExe.Source.Scalar.Step.resultType .word) step td fd)).isNone do
      throwError "wrong step proof-lambda domain accepted"
  unless (LeanExe.Extract.Core.extractScalarExprWith [.boolean (.u64 1)]
      (make (.const ``UInt64 []) (.bvar 0) guard.condition neg)).isNone do
    throwError "erased scalar proof binder read as a word"
  unless (LeanExe.Extract.Core.extractScalarStepWith [.scalar (.boolean (.u64 1))]
      (make (LeanExe.Source.Scalar.Step.resultType .word)
        (LeanExe.Source.Scalar.Step.yieldDirect (.bvar 0)) guard.condition neg)).isNone do
    throwError "erased step proof binder read as a word"
  Lean.logInfo "304 native/Boolean-dependent IR comparisons, four declaration rejection tests and six proof-binder rejection tests passed"

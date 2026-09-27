import LeanExe.Extract.ScalarFunc

namespace BooleanLocalTest

def booleanLet (x y : UInt64) : UInt64 :=
  let equal := x == y
  if equal then x + y * 3 else x - y * 5

def booleanAlias (x y : UInt64) : UInt64 :=
  let equal := x == y
  let alias := equal
  let inverted := !!!alias
  if inverted then ~~~x else ~~~y

def booleanShadow (x y : UInt64) : UInt64 :=
  let flag := x != y
  let f := fun a b : UInt64 => if flag then a + b else a - b
  let flag := y == 0
  if flag then f x y else f y x

def booleanCompound (x y : UInt64) : UInt64 :=
  let equal := x == y
  let zero := x == 0 || y == 0
  let flag := !equal && !(zero || y == 1)
  if flag || (!zero && equal) then x + 13 else y - 17

def booleanNestedOperand (x y : UInt64) : UInt64 :=
  let flag := x == 0
  let a := if flag then x + y else x - y
  let next := (if flag then a else y) == (if _h : x < y then x else a)
  if next && !flag then a + 7 else a - 3

def booleanUnused (x y : UInt64) : UInt64 :=
  let _flag := (x / 0 == y) && (y % 0 != x)
  let kept := true
  let alias := kept
  if alias then x + y else ~~~x

def booleanMany (x y : UInt64) : UInt64 :=
  let outer := x != y
  let f := fun a b c : UInt64 =>
    let inner := a == b || b == c
    if outer && !inner then a + b * 3 - c else a - b * 5 + c
  f x y (x + 7)

def booleanDo (x y : UInt64) : UInt64 := Id.run do
  let flag := x == y
  let mut a := x
  if flag then a := a + y else a := a - y
  let next := a % 3 == 0
  let z ← if next && !flag then pure (a * 7) else pure (a + 5)
  return z ^^^ y

def rangeBooleanYield (count seed : UInt64) : UInt64 := Id.run do
  let mut a := seed
  for i in [:count.toNat] do
    let even := UInt64.ofNat i % 2 == 0
    if even then a := a + 3 else a := a + 7
  return a

def rangeBooleanBreak (count seed : UInt64) : UInt64 := Id.run do
  let mut a := seed
  for i in [:count.toNat] do
    a := a + UInt64.ofNat i + 1
    let stop := a % 7 == 0 || UInt64.ofNat i == 12
    if stop then break
  return a

def rangeBooleanContinue (count seed : UInt64) : UInt64 := Id.run do
  let mut a := seed
  for i in [:count.toNat] do
    let skip := UInt64.ofNat i % 3 == 1
    if skip then continue
    a := a + UInt64.ofNat i
    let stop := a % 11 == 0
    if stop && !skip then break
  return a

def rangeBooleanCapture (count seed : UInt64) : UInt64 := Id.run do
  let mut a := seed
  for i in [:count.toNat] do
    let captured := a % 5 == 0
    let f := fun x y : UInt64 => if captured then x + y else x - y
    a := a + UInt64.ofNat i + 1
    let captured := a % 7 == 0
    a := f a seed
    if captured then break
  return a

def rangeBooleanJoined (count seed : UInt64) : UInt64 := Id.run do
  let mut a := seed
  for i in [:count.toNat] do
    let even := a % 2 == 0
    if even then a := a + 2 else a := a + 5
    let z ← if !even then pure (a - 1) else pure (a + 3)
    a := z + UInt64.ofNat i
    let stop := a % 13 == 0
    if stop then break
  let changed := a != seed
  return if changed then a + count else a - count

def rangeBooleanOuter (count seed : UInt64) : UInt64 :=
  let flag := seed % 3 == 0
  let f := fun x y z : UInt64 => if flag then x + y - z else x - y + z
  let result := Id.run do
    let mut a := seed
    for i in [:count.toNat] do
      a := f a (UInt64.ofNat i) count
      let stop := a == 0
      if stop && flag then break
    return a
  if flag then result + seed else result - count

def rangeBooleanBounds (count seed : UInt64) : UInt64 := Id.run do
  let flag := seed % 3 == 0
  let first : UInt64 := if flag then 0 else 2
  let stop := if !flag && count != 0 then count - 1 else count
  let mut a := seed
  for i in [first.toNat:stop.toNat:2] do
    let finish := a % 7 == 0
    if finish && flag then break
    a := a + UInt64.ofNat i
  return a

def rangeBooleanStep (count seed : UInt64) : UInt64 :=
  forIn (m := Id) [:count.toNat] seed fun i a =>
    let captured := a % 5 == 0
    let f : UInt64 → UInt64 → UInt64 → ForInStep UInt64 := fun x y z =>
      let localFlag := x == y || y == z
      if captured && localFlag then .done (x + y - z)
      else .yield (x - y + z)
    f a (UInt64.ofNat i) count

def booleanUnusedUnsupported (x y : UInt64) : UInt64 :=
  let _flag := toString x == toString y
  x + y

def booleanCustomEquality (x y : UInt64) : UInt64 :=
  let flag := @BEq.beq UInt64 ⟨fun _ _ => true⟩ x y
  if flag then x else y

def booleanIgnoredOperand (x y : UInt64) : UInt64 :=
  let flag := true || UInt64.ofNat (toString x).length == y
  if flag then x else y

def rangeBooleanUnusedUnsupported (count seed : UInt64) : UInt64 :=
  forIn (m := Id) [:count.toNat] seed fun _ a =>
    let _flag := toString a == toString seed
    .yield (a + 1)

def inputs : List (UInt64 × UInt64) :=
  [(0, 0), (1, 0), (0xffffffffffffffff, 0), (0, 1), (1, 1),
   (0xffffffffffffffff, 1), (0x8000000000000000, 2), (42, 3),
   (0xffffffffffffffff, 63), (0x8000000000000001, 64), (0xffffffffffffffff, 65),
   (0x0123456789abcdef, 0xffffffffffffffff), (3, 17), (17, 3)]

end BooleanLocalTest

run_elab do
  let env ← Lean.getEnv
  let cases : List (Lean.Name × (UInt64 → UInt64 → UInt64) × Bool) := [
    (`BooleanLocalTest.booleanLet, BooleanLocalTest.booleanLet, false),
    (`BooleanLocalTest.booleanAlias, BooleanLocalTest.booleanAlias, false),
    (`BooleanLocalTest.booleanShadow, BooleanLocalTest.booleanShadow, false),
    (`BooleanLocalTest.booleanCompound, BooleanLocalTest.booleanCompound, false),
    (`BooleanLocalTest.booleanNestedOperand, BooleanLocalTest.booleanNestedOperand, false),
    (`BooleanLocalTest.booleanUnused, BooleanLocalTest.booleanUnused, false),
    (`BooleanLocalTest.booleanMany, BooleanLocalTest.booleanMany, false),
    (`BooleanLocalTest.booleanDo, BooleanLocalTest.booleanDo, false),
    (`BooleanLocalTest.rangeBooleanYield, BooleanLocalTest.rangeBooleanYield, true),
    (`BooleanLocalTest.rangeBooleanBreak, BooleanLocalTest.rangeBooleanBreak, true),
    (`BooleanLocalTest.rangeBooleanContinue, BooleanLocalTest.rangeBooleanContinue, true),
    (`BooleanLocalTest.rangeBooleanCapture, BooleanLocalTest.rangeBooleanCapture, true),
    (`BooleanLocalTest.rangeBooleanJoined, BooleanLocalTest.rangeBooleanJoined, true),
    (`BooleanLocalTest.rangeBooleanOuter, BooleanLocalTest.rangeBooleanOuter, true),
    (`BooleanLocalTest.rangeBooleanBounds, BooleanLocalTest.rangeBooleanBounds, true),
    (`BooleanLocalTest.rangeBooleanStep, BooleanLocalTest.rangeBooleanStep, true)]
  for (name, native, isRange) in cases do
    let some info := env.find? name | throwError "missing declaration"
    let some value := info.value? | throwError "missing body"
    let some func := LeanExe.Extract.Core.extractScalarFunc name (some "entry") info.type value |
      throwError "{name}: Boolean local extraction failed"
    let module_ : LeanExe.IR.Module := { funcs := #[func] }
    let inputs := if isRange then
      ([0, 1, 2, 7, 16, 31] : List UInt64).flatMap fun n =>
        ([0, 1, 0x8000000000000000, 0xffffffffffffffff] : List UInt64).map fun seed => (n, seed)
      else BooleanLocalTest.inputs
    for (x, y) in inputs do
      let expected := native x y
      let actual := module_.evalFunc 0 [x, y]
      unless actual == expected do
        throwError "{name}({x}, {y}): native={expected}, IR={actual}"
  for name in [`BooleanLocalTest.booleanUnusedUnsupported, `BooleanLocalTest.booleanCustomEquality, `BooleanLocalTest.booleanIgnoredOperand, `BooleanLocalTest.rangeBooleanUnusedUnsupported] do
    let some info := env.find? name | throwError "missing declaration"
    let some value := info.value? | throwError "missing body"
    unless (LeanExe.Extract.Core.extractScalarFunc name (some "entry") info.type value).isNone do
      throwError "{name}: unsupported Boolean local accepted"
  unless (LeanExe.Extract.Core.extractScalarExprWith [.boolean (.u64 1)] (.bvar 0)).isNone do
    throwError "Boolean binding accepted as a UInt64 word"
  let condition := LeanExe.Source.Scalar.BooleanLocal.var 0 0
  unless (LeanExe.Extract.Core.extractBooleanLocalWith [.word (.u64 1)] condition
      (fun _ _ => none)).isNone do
    throwError "UInt64 binding accepted as a Boolean"
  let one := LeanExe.Source.Scalar.literalExpr 1
  let branch := LeanExe.Source.Scalar.BooleanLocalGuard.branch { value := condition, expanded := by decide } (.const ``UInt64 []) one one
  unless (LeanExe.Extract.Core.extractScalarExprWith [.word (.u64 1)] branch).isNone do
    throwError "word binding accepted by a Boolean condition"
  unless (LeanExe.Extract.Core.extractScalarExprWith [.unit] branch).isNone do
    throwError "erased binder accepted by a Boolean condition"
  Lean.logInfo "304 native/boolean-local IR comparisons, four declaration rejection tests and four binding-kind rejection tests passed"

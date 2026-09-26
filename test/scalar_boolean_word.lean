import LeanExe.Extract.ScalarFunc

namespace BooleanWordTest

def boolWordDirect (x y : UInt64) : UInt64 := (x == y).toUInt64 + Bool.toUInt64 (decide (x < y))

def boolWordCaptured (x y : UInt64) : UInt64 :=
  let flag := x != 0
  let f := fun flag : Bool => flag.toUInt64 + x
  f (!flag) + flag.toUInt64 * y

def boolWordAction (x y : UInt64) : UInt64 := Id.run do
  let flag ← if x = y then pure true else pure (decide (x > 0))
  return flag.toUInt64 + x

def boolWordLiterals (x y : UInt64) : UInt64 :=
  true.toUInt64 * x + false.toUInt64 * y + (!false).toUInt64

def boolWordChoice (x y : UInt64) : UInt64 :=
  let flag := x == y
  let value := (if flag then decide (x ≥ y) else x == 0).toUInt64
  value * 7 + (!!!(flag && decide (x < y))).toUInt64

def boolWordNested (x y : UInt64) : UInt64 :=
  let a := ((x == y).toUInt64 == (decide (x < y)).toUInt64).toUInt64
  let b := (decide (a < (x != 0).toUInt64 + y)).toUInt64
  a * 7 + b * 13

def boolWordDependent (x y : UInt64) : UInt64 :=
  let flag := x != 0
  if _h : flag then
    let f := fun other : Bool => (flag && other).toUInt64 + x
    f (decide (x ≤ y))
  else
    (if y < x then !flag else y != 0).toUInt64 + y

def boolWordUnused (x y : UInt64) : UInt64 :=
  let _unused := (false && (x / 0 == y)).toUInt64
  let f := fun a b c : UInt64 => (decide (a < b ∨ b ≥ c)).toUInt64
  f x y (x + 1) + (x == 0).toUInt64

def rangeBoolWordYield (count seed : UInt64) : UInt64 := Id.run do
  let mut a := seed
  for i in [:count.toNat] do
    a := a + (decide (UInt64.ofNat i % 2 = 0)).toUInt64
    if a % 7 == 0 then break
  return a

def rangeBoolWordBreak (count seed : UInt64) : UInt64 := Id.run do
  let mut a := seed
  for i in [:count.toNat] do
    let flag := decide (a < seed ∨ UInt64.ofNat i ≥ 12)
    a := a + flag.toUInt64 + 1
    if flag.toUInt64 == 1 then break
  return a

def rangeBoolWordContinue (count seed : UInt64) : UInt64 := Id.run do
  let mut a := seed
  for i in [:count.toNat] do
    let skip := UInt64.ofNat i % 3 == 1
    if skip.toUInt64 != 0 then continue
    a := a + skip.toUInt64 + UInt64.ofNat i
    if a % 11 == 0 then break
  return a

def rangeBoolWordJoined (count seed : UInt64) : UInt64 := Id.run do
  let mut a := seed
  for i in [:count.toNat] do
    let even ← if a % 2 = 0 then pure true else pure false
    if even then a := a + even.toUInt64 else a := a + (!even).toUInt64
    let next ← if even then pure (a % 3 == 0) else pure (!even)
    a := a + next.toUInt64 + UInt64.ofNat i
    if next && a % 13 == 0 then break
  return a

def rangeBoolWordCapture (count seed : UInt64) : UInt64 := Id.run do
  let outer := seed != 0
  let f := fun flag : Bool => (flag || outer).toUInt64 + count
  let mut a := seed
  for i in [:count.toNat] do
    let g := fun flag : Bool => f flag + a + outer.toUInt64
    a := g (UInt64.ofNat i % 2 == 0)
    if a % 11 == 0 then break
  return a + f (a == 0)

def rangeBoolWordBounds (count seed : UInt64) : UInt64 := Id.run do
  let flag := decide (seed % 3 ≤ 1)
  let first := flag.toUInt64
  let stop := count + (!flag).toUInt64
  let mut a := seed + flag.toUInt64
  for i in [first.toNat:stop.toNat:2] do
    a := a + Bool.toUInt64 (UInt64.ofNat i < count)
    if a % 7 == 0 then break
  return a

def rangeBoolWordStep (count seed : UInt64) : UInt64 :=
  forIn (m := Id) [:count.toNat] seed fun i a => do
    let f : Bool → Id (ForInStep UInt64) := fun flag => do
      let value := flag.toUInt64 + a
      if flag then return .done value else return .yield (value + count)
    f (decide (UInt64.ofNat i ≥ 7))

def rangeBoolWordOuter (count seed : UInt64) : UInt64 := Id.run do
  let flag ← pure (count != 0)
  let mut a := seed + flag.toUInt64
  for i in [:count.toNat] do
    a := a + UInt64.ofNat i + 1
    if a % 7 == 0 then break
  let changed ← if a = seed then pure (count != 0) else pure (a != 0)
  return a + (changed && flag).toUInt64

def boolWordUnsupported (x y : UInt64) : UInt64 := (toString x == toString y).toUInt64

def boolWordUnusedUnsupported (x y : UInt64) : UInt64 :=
  let _unused := (false && (toString x == toString y)).toUInt64
  x + y

def boolWordBooleanHelper (x y : UInt64) : UInt64 :=
  let f := fun flag : Bool => !flag
  (f (x == y)).toUInt64

def rangeBoolWordUnsupported (count seed : UInt64) : UInt64 :=
  forIn (m := Id) [:count.toNat] seed fun _ a => do
    let _unused := (toString a == toString seed).toUInt64
    return .yield (a + 1)

def inputs : List (UInt64 × UInt64) :=
  [(0, 0), (1, 0), (0xffffffffffffffff, 0), (0, 1), (1, 1),
   (0xffffffffffffffff, 1), (0x8000000000000000, 2), (42, 3),
   (0xffffffffffffffff, 63), (0x8000000000000001, 64), (0xffffffffffffffff, 65),
   (0x0123456789abcdef, 0xffffffffffffffff), (3, 17), (17, 3)]

end BooleanWordTest

run_elab do
  let env ← Lean.getEnv
  let cases : List (Lean.Name × (UInt64 → UInt64 → UInt64) × Bool) := [
    (`BooleanWordTest.boolWordBooleanHelper, BooleanWordTest.boolWordBooleanHelper, false),
    (`BooleanWordTest.boolWordDirect, BooleanWordTest.boolWordDirect, false),
    (`BooleanWordTest.boolWordCaptured, BooleanWordTest.boolWordCaptured, false),
    (`BooleanWordTest.boolWordAction, BooleanWordTest.boolWordAction, false),
    (`BooleanWordTest.boolWordLiterals, BooleanWordTest.boolWordLiterals, false),
    (`BooleanWordTest.boolWordChoice, BooleanWordTest.boolWordChoice, false),
    (`BooleanWordTest.boolWordNested, BooleanWordTest.boolWordNested, false),
    (`BooleanWordTest.boolWordDependent, BooleanWordTest.boolWordDependent, false),
    (`BooleanWordTest.boolWordUnused, BooleanWordTest.boolWordUnused, false),
    (`BooleanWordTest.rangeBoolWordYield, BooleanWordTest.rangeBoolWordYield, true),
    (`BooleanWordTest.rangeBoolWordBreak, BooleanWordTest.rangeBoolWordBreak, true),
    (`BooleanWordTest.rangeBoolWordContinue, BooleanWordTest.rangeBoolWordContinue, true),
    (`BooleanWordTest.rangeBoolWordJoined, BooleanWordTest.rangeBoolWordJoined, true),
    (`BooleanWordTest.rangeBoolWordCapture, BooleanWordTest.rangeBoolWordCapture, true),
    (`BooleanWordTest.rangeBoolWordBounds, BooleanWordTest.rangeBoolWordBounds, true),
    (`BooleanWordTest.rangeBoolWordStep, BooleanWordTest.rangeBoolWordStep, true),
    (`BooleanWordTest.rangeBoolWordOuter, BooleanWordTest.rangeBoolWordOuter, true)]
  for (name, native, isRange) in cases do
    let some info := env.find? name | throwError "missing declaration"
    let some value := info.value? | throwError "missing body"
    let some func := LeanExe.Extract.Core.extractScalarFunc name (some "entry") info.type value |
      throwError "{name}: Boolean conversion extraction failed"
    let module_ : LeanExe.IR.Module := { funcs := #[func] }
    let inputs := if isRange then
      ([0, 1, 2, 7, 16, 31] : List UInt64).flatMap fun n =>
        ([0, 1, 0x8000000000000000, 0xffffffffffffffff] : List UInt64).map fun seed => (n, seed)
      else BooleanWordTest.inputs
    for (x, y) in inputs do
      let expected := native x y
      let actual := module_.evalFunc 0 [x, y]
      unless actual == expected do
        throwError "{name}({x}, {y}): native={expected}, IR={actual}"
  for name in [`BooleanWordTest.boolWordUnsupported, `BooleanWordTest.boolWordUnusedUnsupported, `BooleanWordTest.rangeBoolWordUnsupported] do
    let some info := env.find? name | throwError "missing declaration"
    let some value := info.value? | throwError "missing body"
    unless (LeanExe.Extract.Core.extractScalarFunc name (some "entry") info.type value).isNone do
      throwError "{name}: unsupported Boolean conversion accepted"
  let one := LeanExe.Source.Scalar.literalExpr 1
  let yes := Lean.Expr.const ``Bool.true []
  for argument in [one, Lean.Expr.const ``True [], Lean.Expr.bvar 0] do
    let source := Lean.Expr.app (.const ``Bool.toUInt64 []) argument
    for locals in [[], [LeanExe.Extract.Core.ScalarBinding.word (.u64 1)]] do
      unless (LeanExe.Extract.Core.extractScalarExprWith locals source).isNone do
        throwError "invalid Boolean conversion accepted in scalar code"
      let step := LeanExe.Source.Scalar.Step.yieldDirect source
      unless (LeanExe.Extract.Core.extractScalarStepWith (locals.map LeanExe.Extract.Core.ScalarStepBinding.scalar) step).isNone do
        throwError "invalid Boolean conversion accepted in step code"
  let wrongLevel := Lean.Expr.app (.const ``Bool.toUInt64 [.zero]) yes
  unless (LeanExe.Extract.Core.extractScalarExprWith [] wrongLevel).isNone do
    throwError "invalid conversion universe accepted"
  Lean.logInfo "304 native/Boolean-word IR comparisons, four declaration rejection tests and thirteen raw conversion rejection tests passed"

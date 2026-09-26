import LeanExe.Extract.ScalarFunc

namespace BooleanChoiceTest

def boolChoiceLet (x y : UInt64) : UInt64 :=
  let flag := if x == y then x == 0 else y != 0
  if flag then x + y * 3 else x - y * 5

def boolChoiceNested (x y : UInt64) : UInt64 :=
  let flag := x == y
  let result := !!!(if (if flag then x == 0 else y == 0) then
    (if !flag then x != 0 else false) else (if flag then true else y != 0))
  if result then ~~~x else ~~~y

def boolChoiceClosed (x y : UInt64) : UInt64 :=
  if (if x == y then x != 0 else y == 0) then x + 7 else y - 11

def boolChoiceShadow (x y : UInt64) : UInt64 :=
  let flag := if x == y then true else x == 0
  let f := fun a b : UInt64 => if (if flag then a != b else b == 0) then a + b else a - b
  let flag := if y == 0 then false else !flag
  if flag then f x y else f y x

def boolChoiceCapture (x y : UInt64) : UInt64 :=
  let outer := x == 0
  let f := fun a b c : UInt64 =>
    let inner := if outer then a == b || b == c else a != c
    if inner then a + b * 3 - c else a - b + c
  f x y (x + 7)

def boolChoiceDependent (x y : UInt64) : UInt64 :=
  let flag := x == y
  if _h : (if flag then x != 0 else y == 0) then
    let next := if flag then y == 0 else x != 0
    if next then y + 3 else x - 5
  else
    let next := if !flag then x != 0 && y != 0 else true
    if _k : next then x / y else y % x

def boolChoiceDo (x y : UInt64) : UInt64 := Id.run do
  let flag ← pure (if x == y then x == 0 else y != 0)
  let mut a := x
  if flag then a := a + y else a := a - y
  let next := if a % 3 == 0 then !flag else a != 0
  let z ← if next && !flag then pure (a * 7) else pure (a + 5)
  return z ^^^ y

def boolChoiceUnused (x y : UInt64) : UInt64 :=
  let _unused := if true then false else x / 0 == y
  let kept := if false then false else true
  if kept then x + y else x - y

def rangeBoolChoiceYield (count seed : UInt64) : UInt64 := Id.run do
  let mut a := seed
  for i in [:count.toNat] do
    let even := if UInt64.ofNat i % 2 == 0 then a != 0 else a == 0
    if even then a := a + 3 else a := a + 7
  return a

def rangeBoolChoiceBreak (count seed : UInt64) : UInt64 := Id.run do
  let mut a := seed
  for i in [:count.toNat] do
    a := a + UInt64.ofNat i + 1
    if _h : (if a % 7 == 0 then true else UInt64.ofNat i == 12) then break
  return a

def rangeBoolChoiceContinue (count seed : UInt64) : UInt64 := Id.run do
  let mut a := seed
  for i in [:count.toNat] do
    let skip := if UInt64.ofNat i % 3 == 1 then a != seed else false
    if skip then continue
    a := a + UInt64.ofNat i
    let stop := if !skip then a % 11 == 0 else false
    if stop then break
  return a

def rangeBoolChoiceJoined (count seed : UInt64) : UInt64 := Id.run do
  let mut a := seed
  for i in [:count.toNat] do
    let even ← pure (if a % 2 == 0 then true else false)
    if even then a := a + 2 else a := a + 5
    let next ← pure (if even then a % 3 == 0 else !even)
    let z ← if next then pure (a - 1) else pure (a + 3)
    a := z + UInt64.ofNat i
    if (if next then a % 13 == 0 else false) then break
  return a

def rangeBoolChoiceCapture (count seed : UInt64) : UInt64 := Id.run do
  let flag := if seed % 3 == 0 then count != 0 else false
  let f := fun x y z : UInt64 =>
    let inner := if flag then x != y else y == z
    if inner then x + y - z else x - y + z
  let mut a := seed
  for i in [:count.toNat] do
    let inner := if flag then a % 5 == 0 else a == seed
    a := f a (UInt64.ofNat i) count
    if inner && flag then break
  return a

def rangeBoolChoiceBounds (count seed : UInt64) : UInt64 := Id.run do
  let flag := if seed % 3 == 0 then true else count == 0
  let first : UInt64 := if flag then 0 else 2
  let stop := if (if flag then false else count != 0) then count - 1 else count
  let mut a := seed
  for i in [first.toNat:stop.toNat:2] do
    let finish := if flag then a % 7 == 0 else false
    if finish then break
    a := a + UInt64.ofNat i
  return a

def rangeBoolChoiceStep (count seed : UInt64) : UInt64 :=
  forIn (m := Id) [:count.toNat] seed fun i a => do
    let captured := if a % 5 == 0 then count != 0 else false
    let f : UInt64 → UInt64 → UInt64 → Id (ForInStep UInt64) := fun x y z => do
      let inner := if captured then x == y || y == z else y != z
      if _h : inner then return .done (x + y - z)
      else return .yield (x - y + z)
    f a (UInt64.ofNat i) count

def rangeBoolChoiceOuter (count seed : UInt64) : UInt64 := Id.run do
  let flag := if seed == 0 then count != 0 else false
  let mut a := seed
  for i in [:count.toNat] do
    a := a + UInt64.ofNat i + 1
    let stop := if flag then a % 7 == 0 else false
    if stop then break
  let changed ← pure (if flag then a != seed else count == 0)
  return if changed then a + count else a - count

def boolChoiceUnsupportedArm (x y : UInt64) : UInt64 :=
  let flag := if true then false else toString x == toString y
  if flag then x else y

def boolChoiceUnusedUnsupported (x y : UInt64) : UInt64 :=
  let _unused := if false then toString x == toString y else true
  x + y

def boolChoiceCustomDecision (x y : UInt64) : UInt64 :=
  let flag := @ite Bool ((x == y) = true)
    (if h : (x == y) = true then .isTrue h else .isFalse h) true false
  if flag then x else y

def rangeBoolChoiceUnsupportedArm (count seed : UInt64) : UInt64 :=
  forIn (m := Id) [:count.toNat] seed fun _ a => do
    let flag := if false then toString a == toString seed else true
    return if flag then .yield (a + 1) else .done a

def inputs : List (UInt64 × UInt64) :=
  [(0, 0), (1, 0), (0xffffffffffffffff, 0), (0, 1), (1, 1),
   (0xffffffffffffffff, 1), (0x8000000000000000, 2), (42, 3),
   (0xffffffffffffffff, 63), (0x8000000000000001, 64), (0xffffffffffffffff, 65),
   (0x0123456789abcdef, 0xffffffffffffffff), (3, 17), (17, 3)]

end BooleanChoiceTest

run_elab do
  let env ← Lean.getEnv
  let cases : List (Lean.Name × (UInt64 → UInt64 → UInt64) × Bool) := [
    (`BooleanChoiceTest.boolChoiceLet, BooleanChoiceTest.boolChoiceLet, false),
    (`BooleanChoiceTest.boolChoiceNested, BooleanChoiceTest.boolChoiceNested, false),
    (`BooleanChoiceTest.boolChoiceClosed, BooleanChoiceTest.boolChoiceClosed, false),
    (`BooleanChoiceTest.boolChoiceShadow, BooleanChoiceTest.boolChoiceShadow, false),
    (`BooleanChoiceTest.boolChoiceCapture, BooleanChoiceTest.boolChoiceCapture, false),
    (`BooleanChoiceTest.boolChoiceDependent, BooleanChoiceTest.boolChoiceDependent, false),
    (`BooleanChoiceTest.boolChoiceDo, BooleanChoiceTest.boolChoiceDo, false),
    (`BooleanChoiceTest.boolChoiceUnused, BooleanChoiceTest.boolChoiceUnused, false),
    (`BooleanChoiceTest.rangeBoolChoiceYield, BooleanChoiceTest.rangeBoolChoiceYield, true),
    (`BooleanChoiceTest.rangeBoolChoiceBreak, BooleanChoiceTest.rangeBoolChoiceBreak, true),
    (`BooleanChoiceTest.rangeBoolChoiceContinue, BooleanChoiceTest.rangeBoolChoiceContinue, true),
    (`BooleanChoiceTest.rangeBoolChoiceJoined, BooleanChoiceTest.rangeBoolChoiceJoined, true),
    (`BooleanChoiceTest.rangeBoolChoiceCapture, BooleanChoiceTest.rangeBoolChoiceCapture, true),
    (`BooleanChoiceTest.rangeBoolChoiceBounds, BooleanChoiceTest.rangeBoolChoiceBounds, true),
    (`BooleanChoiceTest.rangeBoolChoiceStep, BooleanChoiceTest.rangeBoolChoiceStep, true),
    (`BooleanChoiceTest.rangeBoolChoiceOuter, BooleanChoiceTest.rangeBoolChoiceOuter, true)]
  for (name, native, isRange) in cases do
    let some info := env.find? name | throwError "missing declaration"
    let some value := info.value? | throwError "missing body"
    let some func := LeanExe.Extract.Core.extractScalarFunc name (some "entry") info.type value |
      throwError "{name}: Boolean choice extraction failed"
    let module_ : LeanExe.IR.Module := { funcs := #[func] }
    let inputs := if isRange then
      ([0, 1, 2, 7, 16, 31] : List UInt64).flatMap fun n =>
        ([0, 1, 0x8000000000000000, 0xffffffffffffffff] : List UInt64).map fun seed => (n, seed)
      else BooleanChoiceTest.inputs
    for (x, y) in inputs do
      let expected := native x y
      let actual := module_.evalFunc 0 [x, y]
      unless actual == expected do
        throwError "{name}({x}, {y}): native={expected}, IR={actual}"
  for name in [`BooleanChoiceTest.boolChoiceUnsupportedArm, `BooleanChoiceTest.boolChoiceUnusedUnsupported, `BooleanChoiceTest.boolChoiceCustomDecision, `BooleanChoiceTest.rangeBoolChoiceUnsupportedArm] do
    let some info := env.find? name | throwError "missing declaration"
    let some value := info.value? | throwError "missing body"
    unless (LeanExe.Extract.Core.extractScalarFunc name (some "entry") info.type value).isNone do
      throwError "{name}: unsupported Boolean choice accepted"
  let boolType := Lean.Expr.const ``Bool []
  let one := LeanExe.Source.Scalar.literalExpr 1
  let test := Lean.Expr.const ``Bool.true []
  let yes := Lean.Expr.const ``Bool.false []
  let no := Lean.Expr.const ``Bool.true []
  let condition := Lean.mkAppN (.const ``Eq [.succ .zero]) #[boolType, test, test]
  let evidence := Lean.mkAppN (.const ``instDecidableEqBool []) #[test, test]
  let make (result decision first : Lean.Expr) :=
    Lean.mkAppN (.const ``ite [.succ .zero]) #[result, condition, decision, first, no]
  let mismatched := Lean.mkAppN (.const ``instDecidableEqBool []) #[yes, test]
  for argument in [make (.const ``UInt64 []) evidence yes,
      make boolType (.bvar 0) yes, make boolType mismatched yes,
      make boolType evidence one] do
    let scalar := Lean.Expr.letE `flag boolType argument one false
    let step := Lean.Expr.letE `flag boolType argument (LeanExe.Source.Scalar.Step.yieldDirect one) false
    unless (LeanExe.Extract.Core.extractScalarExprWith [] scalar).isNone do
      throwError "invalid Boolean choice accepted in scalar code"
    unless (LeanExe.Extract.Core.extractScalarStepWith [] step).isNone do
      throwError "invalid Boolean choice accepted in step code"
  Lean.logInfo "304 native/Boolean-choice IR comparisons, four declaration rejection tests and eight raw choice rejection tests passed"

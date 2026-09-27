import LeanExe.Extract.ScalarFunc

namespace BooleanEqualityTest

def boolEqDirect (x y : UInt64) : UInt64 :=
  let a := x == 0
  let b := y == 0
  (a == b).toUInt64 + (a != b).toUInt64 * 3

def boolEqCalls (x y : UInt64) : UInt64 :=
  let a := x == y
  let b := decide (x < y)
  (BEq.beq a b).toUInt64 + (bne a b).toUInt64

def boolEqConditional (x y : UInt64) : UInt64 :=
  let a := x != 0
  let b := y != 0
  if a == b then x + y else x - y

def boolEqCapture (x y : UInt64) : UInt64 :=
  let outer := x == 0
  let f := fun flag : Bool => if flag != outer then x + y else x - y
  f (y == 0)

def boolEqLiterals (x y : UInt64) : UInt64 :=
  (true == true).toUInt64 + (false == false).toUInt64 * 3 +
    (true == false).toUInt64 * x + (false != true).toUInt64 * y

def boolEqChoices (x y : UInt64) : UInt64 :=
  let a := x == 0
  let b := y == 0
  let flag := (if x < y then a else !b) == (if a then decide (x ≤ y) else b)
  if _h : !!!(flag != a) then x / y else y % x

def boolEqNested (x y : UInt64) : UInt64 :=
  let a := x == 0
  let b := y == 0
  let left := (a == b) != (!a == !b)
  let right := (a != !b) == (a == b)
  (left == right).toUInt64 + ((a && b) != (a || b)).toUInt64 * 7

def boolEqDo (x y : UInt64) : UInt64 := Id.run do
  let a ← if x = y then pure true else pure (decide (x > 0))
  let b ← pure (y != 0)
  let same ← if a then pure (a == b) else pure (a != b)
  let mut z := x
  if same then z := z + y else z := z - y
  return z + (same == a).toUInt64

def rangeBoolEqYield (count seed : UInt64) : UInt64 := Id.run do
  let mut a := seed
  for i in [:count.toNat] do
    let first := a % 2 == 0
    let second := UInt64.ofNat i % 3 == 0
    a := a + (first == second).toUInt64
    if first != second then break
  return a

def rangeBoolEqBreak (count seed : UInt64) : UInt64 := Id.run do
  let mut a := seed
  for i in [:count.toNat] do
    a := a + UInt64.ofNat i + 1
    let flag := (a % 7 == 0) == (UInt64.ofNat i < 12 : Bool)
    if flag then break
  return a

def rangeBoolEqContinue (count seed : UInt64) : UInt64 := Id.run do
  let mut a := seed
  for i in [:count.toNat] do
    let skip := (UInt64.ofNat i % 3 == 1) != (a == seed)
    if skip then continue
    a := a + UInt64.ofNat i
    if (a % 11 == 0) == true then break
  return a

def rangeBoolEqJoined (count seed : UInt64) : UInt64 := Id.run do
  let mut a := seed
  for i in [:count.toNat] do
    let even ← if a % 2 = 0 then pure true else pure false
    if even == (UInt64.ofNat i % 2 == 0) then a := a + 2 else a := a + 5
    let next ← if even then pure (even == (a % 3 == 0)) else pure (!even)
    a := a + next.toUInt64 + UInt64.ofNat i
    if next != (a % 13 != 0) then break
  return a

def rangeBoolEqCapture (count seed : UInt64) : UInt64 := Id.run do
  let outer := seed != 0
  let f := fun flag : Bool => (flag == outer).toUInt64 + count
  let mut a := seed
  for i in [:count.toNat] do
    let g := fun flag : Bool => f (flag != outer) + a
    a := g (UInt64.ofNat i % 2 == 0)
    if (a % 11 == 0) != outer then break
  return a + f (a == 0)

def rangeBoolEqBounds (count seed : UInt64) : UInt64 := Id.run do
  let flag := decide (seed % 3 ≤ 1)
  let first := (flag == (count != 0)).toUInt64
  let stop := count + (flag != true).toUInt64
  let mut a := seed
  for i in [first.toNat:stop.toNat:2] do
    let even := UInt64.ofNat i % 2 == 0
    a := a + (even == flag).toUInt64
    if (a % 7 == 0) == flag then break
  return a

def rangeBoolEqStep (count seed : UInt64) : UInt64 :=
  forIn (m := Id) [:count.toNat] seed fun i a => do
    let outer := a == seed
    let f : Bool → Id (ForInStep UInt64) := fun flag => do
      let equal := flag == outer
      if _h : equal != false then return .done (a + UInt64.ofNat i)
      else return .yield (a - count)
    f (decide (UInt64.ofNat i ≥ 7))

def rangeBoolEqOuter (count seed : UInt64) : UInt64 := Id.run do
  let flag ← pure (count != 0)
  let mut a := seed + flag.toUInt64
  for i in [:count.toNat] do
    a := a + UInt64.ofNat i + 1
    if (a % 7 == 0) != flag then break
  let changed ← if a = seed then pure (flag == (count != 0)) else pure (flag != (a == 0))
  return a + (changed == flag).toUInt64

def boolEqUnsupported (x y : UInt64) : UInt64 :=
  ((x == 0) == (toString x == toString y)).toUInt64

def boolEqUnusedUnsupported (x y : UInt64) : UInt64 :=
  let _unused := false == (toString x == toString y)
  x + y

def boolEqCustomInstance (x y : UInt64) : UInt64 :=
  let flag := @BEq.beq Bool ⟨fun _ _ => true⟩ (x == 0) (y == 0)
  if flag then x else y

def rangeBoolEqUnsupported (count seed : UInt64) : UInt64 :=
  forIn (m := Id) [:count.toNat] seed fun _ a => do
    let _unused := true != (toString a == toString seed)
    return .yield (a + 1)

def inputs : List (UInt64 × UInt64) :=
  [(0, 0), (1, 0), (0xffffffffffffffff, 0), (0, 1), (1, 1),
   (0xffffffffffffffff, 1), (0x8000000000000000, 2), (42, 3),
   (0xffffffffffffffff, 63), (0x8000000000000001, 64), (0xffffffffffffffff, 65),
   (0x0123456789abcdef, 0xffffffffffffffff), (3, 17), (17, 3)]

end BooleanEqualityTest

run_elab do
  let env ← Lean.getEnv
  let cases : List (Lean.Name × (UInt64 → UInt64 → UInt64) × Bool) := [
    (`BooleanEqualityTest.boolEqDirect, BooleanEqualityTest.boolEqDirect, false),
    (`BooleanEqualityTest.boolEqCalls, BooleanEqualityTest.boolEqCalls, false),
    (`BooleanEqualityTest.boolEqConditional, BooleanEqualityTest.boolEqConditional, false),
    (`BooleanEqualityTest.boolEqCapture, BooleanEqualityTest.boolEqCapture, false),
    (`BooleanEqualityTest.boolEqLiterals, BooleanEqualityTest.boolEqLiterals, false),
    (`BooleanEqualityTest.boolEqChoices, BooleanEqualityTest.boolEqChoices, false),
    (`BooleanEqualityTest.boolEqNested, BooleanEqualityTest.boolEqNested, false),
    (`BooleanEqualityTest.boolEqDo, BooleanEqualityTest.boolEqDo, false),
    (`BooleanEqualityTest.rangeBoolEqYield, BooleanEqualityTest.rangeBoolEqYield, true),
    (`BooleanEqualityTest.rangeBoolEqBreak, BooleanEqualityTest.rangeBoolEqBreak, true),
    (`BooleanEqualityTest.rangeBoolEqContinue, BooleanEqualityTest.rangeBoolEqContinue, true),
    (`BooleanEqualityTest.rangeBoolEqJoined, BooleanEqualityTest.rangeBoolEqJoined, true),
    (`BooleanEqualityTest.rangeBoolEqCapture, BooleanEqualityTest.rangeBoolEqCapture, true),
    (`BooleanEqualityTest.rangeBoolEqBounds, BooleanEqualityTest.rangeBoolEqBounds, true),
    (`BooleanEqualityTest.rangeBoolEqStep, BooleanEqualityTest.rangeBoolEqStep, true),
    (`BooleanEqualityTest.rangeBoolEqOuter, BooleanEqualityTest.rangeBoolEqOuter, true)]
  for (name, native, isRange) in cases do
    let some info := env.find? name | throwError "missing declaration"
    let some value := info.value? | throwError "missing body"
    let some func := LeanExe.Extract.Core.extractScalarFunc name (some "entry") info.type value |
      throwError "{name}: Boolean equality extraction failed"
    let module_ : LeanExe.IR.Module := { funcs := #[func] }
    let inputs := if isRange then
      ([0, 1, 2, 7, 16, 31] : List UInt64).flatMap fun n =>
        ([0, 1, 0x8000000000000000, 0xffffffffffffffff] : List UInt64).map fun seed => (n, seed)
      else BooleanEqualityTest.inputs
    for (x, y) in inputs do
      let expected := native x y
      let actual := module_.evalFunc 0 [x, y]
      unless actual == expected do
        throwError "{name}({x}, {y}): native={expected}, IR={actual}"
  for name in [`BooleanEqualityTest.boolEqUnsupported, `BooleanEqualityTest.boolEqUnusedUnsupported, `BooleanEqualityTest.boolEqCustomInstance, `BooleanEqualityTest.rangeBoolEqUnsupported] do
    let some info := env.find? name | throwError "missing declaration"
    let some value := info.value? | throwError "missing body"
    unless (LeanExe.Extract.Core.extractScalarFunc name (some "entry") info.type value).isNone do
      throwError "{name}: unsupported Boolean equality accepted"
  let boolType := Lean.Expr.const ``Bool []
  let one := LeanExe.Source.Scalar.literalExpr 1
  let yes := Lean.Expr.const ``Bool.true []
  let standard := Lean.mkAppN (.const ``instBEqOfDecidableEq [.zero]) #[boolType, .const ``instDecidableEqBool []]
  let wrongInstance := Lean.mkAppN (.const ``instBEqOfDecidableEq [.zero]) #[.const ``UInt64 [], .const ``instDecidableEqUInt64 []]
  for head in [``BEq.beq, ``_root_.bne] do
    let make (levels : List Lean.Level) (evidence left : Lean.Expr) :=
      Lean.mkAppN (.const head levels) #[boolType, evidence, left, yes]
    for argument in [make [.zero] (.bvar 0) yes, make [.zero] wrongInstance yes,
        make [.zero] standard one, make [.succ .zero] standard yes] do
      let scalar := Lean.Expr.letE `flag boolType argument one false
      let step := Lean.Expr.letE `flag boolType argument (LeanExe.Source.Scalar.Step.yieldDirect one) false
      unless (LeanExe.Extract.Core.extractScalarExprWith [] scalar).isNone do
        throwError "invalid Boolean equality accepted in scalar code"
      unless (LeanExe.Extract.Core.extractScalarStepWith [] step).isNone do
        throwError "invalid Boolean equality accepted in step code"
  Lean.logInfo "304 native/Boolean-equality IR comparisons, four declaration rejection tests and sixteen raw equality rejection tests passed"

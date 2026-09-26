import LeanExe.Extract.ScalarFunc

namespace BooleanCompoundTest

def boolAndTruth (x y : UInt64) : UInt64 :=
  if (x % 2 == 1 && y % 2 == 1) then 11 else 29

def boolOrTruth (x y : UInt64) : UInt64 :=
  if (x % 2 == 1 || y % 2 == 1) then 31 else 47

def boolCompoundNot (x y : UInt64) : UInt64 :=
  if !((x + y == 0) && (x != y)) then ~~~x else ~~~y

def boolCompoundTwice (x y : UInt64) : UInt64 :=
  if !!((x == 0) || !(y == x * 3)) then x + 13 else y - 17

def boolCompoundNested (x y : UInt64) : UInt64 :=
  if !((!(x == 0 || y == 0)) && (x / y == 3 || !(y % x == 0 && x != y)))
  then x / y + 1 else y % x + 7

def boolCompoundFunction (x y : UInt64) : UInt64 :=
  let captured := x + 7
  let f := fun a b : UInt64 =>
    if (!(a == b || a == captured)) || (!(b != 0 && a == 0)) then a + b else a - b
  f x y + f y x

def boolCompoundDo (x y : UInt64) : UInt64 := Id.run do
  let mut a := x
  let z ← if !(x == 0 || y == 0) then pure (x + y) else pure (x * y)
  if !!(z == a && y != 1) then a := a + z else a := a - z
  return a ^^^ y

def boolCompoundOperand (x y : UInt64) : UInt64 :=
  if ((if !(x == y && x != 0) then ~~~x else y) == (x + y)) && !(x == y || x == 0)
  then (if !(x == 0 && y == 0) then 19 else x + y) else ~~~(x + y)

def rangeBoolCompoundBreak (count seed : UInt64) : UInt64 := Id.run do
  let mut a := seed
  for i in [:count.toNat] do
    a := a + UInt64.ofNat i + 1
    if !(UInt64.ofNat i % 5 != seed % 5 || a % 3 != 0) then break
  return a

def rangeBoolCompoundContinue (count seed : UInt64) : UInt64 := Id.run do
  let mut a := seed
  for i in [:count.toNat] do
    if !!(UInt64.ofNat i % 3 == 0 || !(UInt64.ofNat i != seed % 7 && a != 0)) then continue
    a := a + UInt64.ofNat i
  return a

def rangeBoolCompoundJoined (count seed : UInt64) : UInt64 := Id.run do
  let mut a := seed
  for i in [:count.toNat] do
    let z ← if !(a == seed && UInt64.ofNat i % 3 == 0) then pure (a + 5) else pure (a - 2)
    if (!(z == a && a != 0)) || (!(UInt64.ofNat i % 3 == 0 || seed == 0)) then
      a := z
    else
      a := z + UInt64.ofNat i
    if !(a != 7 && !(a % 5 == 0 && UInt64.ofNat i != 2)) then break
  return a

def rangeBoolCompoundStep (count seed : UInt64) : UInt64 :=
  forIn (m := Id) [:count.toNat] seed fun i a => Id.run do
    let finish : UInt64 → UInt64 → ForInStep UInt64 := fun x y =>
      if !!!((UInt64.ofNat i % 5 == seed % 5 && x % 3 == 0) || y == 7)
      then .done (x + 11) else .yield (y + UInt64.ofNat i + 1)
    let r : ForInStep UInt64 ← pure (finish (a + seed) a)
    let keep : ForInStep UInt64 → ForInStep UInt64 := fun result => result
    return keep r

def boolCompoundCustom (x y : UInt64) : UInt64 :=
  if x == 0 && @BEq.beq UInt64 ⟨fun _ _ => true⟩ x y then x else y

def boolCompoundDecision (x y : UInt64) : UInt64 :=
  @ite UInt64 ((x == 0 && y == 0) = true)
    (if h : (x == 0 && y == 0) = true then isTrue h else isFalse h) x y

def boolCompoundUnusedCustom (x y : UInt64) : UInt64 :=
  let _f := fun z : UInt64 =>
    if z == 0 || @BEq.beq UInt64 ⟨fun _ _ => true⟩ z y then z else y
  x + y

def inputs : List (UInt64 × UInt64) :=
  [(0, 0), (1, 0), (0xffffffffffffffff, 0), (0, 1), (1, 1),
   (0xffffffffffffffff, 1), (0x8000000000000000, 2), (42, 3),
   (0xffffffffffffffff, 63), (0x8000000000000001, 64), (0xffffffffffffffff, 65),
   (0x0123456789abcdef, 0xffffffffffffffff), (3, 17), (17, 3)]

end BooleanCompoundTest

run_elab do
  let env ← Lean.getEnv
  let cases : List (Lean.Name × (UInt64 → UInt64 → UInt64) × Bool) := [
    (`BooleanCompoundTest.boolAndTruth, BooleanCompoundTest.boolAndTruth, false),
    (`BooleanCompoundTest.boolOrTruth, BooleanCompoundTest.boolOrTruth, false),
    (`BooleanCompoundTest.boolCompoundNot, BooleanCompoundTest.boolCompoundNot, false),
    (`BooleanCompoundTest.boolCompoundTwice, BooleanCompoundTest.boolCompoundTwice, false),
    (`BooleanCompoundTest.boolCompoundNested, BooleanCompoundTest.boolCompoundNested, false),
    (`BooleanCompoundTest.boolCompoundFunction, BooleanCompoundTest.boolCompoundFunction, false),
    (`BooleanCompoundTest.boolCompoundDo, BooleanCompoundTest.boolCompoundDo, false),
    (`BooleanCompoundTest.boolCompoundOperand, BooleanCompoundTest.boolCompoundOperand, false),
    (`BooleanCompoundTest.rangeBoolCompoundBreak, BooleanCompoundTest.rangeBoolCompoundBreak, true),
    (`BooleanCompoundTest.rangeBoolCompoundContinue, BooleanCompoundTest.rangeBoolCompoundContinue, true),
    (`BooleanCompoundTest.rangeBoolCompoundJoined, BooleanCompoundTest.rangeBoolCompoundJoined, true),
    (`BooleanCompoundTest.rangeBoolCompoundStep, BooleanCompoundTest.rangeBoolCompoundStep, true)]
  for (name, native, isRange) in cases do
    let some info := env.find? name | throwError "missing declaration"
    let some value := info.value? | throwError "missing body"
    let some func := LeanExe.Extract.Core.extractScalarFunc name (some "entry") info.type value |
      throwError "{name}: Boolean compound extraction failed"
    let module_ : LeanExe.IR.Module := { funcs := #[func] }
    let inputs := if isRange then
      ([0, 1, 2, 7, 16, 31] : List UInt64).flatMap fun n =>
        ([0, 1, 0x8000000000000000, 0xffffffffffffffff] : List UInt64).map fun seed => (n, seed)
      else BooleanCompoundTest.inputs
    for (x, y) in inputs do
      let expected := native x y
      let actual := module_.evalFunc 0 [x, y]
      unless actual == expected do
        throwError "{name}({x}, {y}): native={expected}, IR={actual}"
  for name in [`BooleanCompoundTest.boolCompoundCustom, `BooleanCompoundTest.boolCompoundDecision, `BooleanCompoundTest.boolCompoundUnusedCustom] do
    let some info := env.find? name | throwError "missing declaration"
    let some value := info.value? | throwError "missing body"
    unless (LeanExe.Extract.Core.extractScalarFunc name (some "entry") info.type value).isNone do
      throwError "{name}: unsupported Boolean compound accepted"
  Lean.logInfo "208 native/Boolean-compound IR comparisons and three rejection tests passed"

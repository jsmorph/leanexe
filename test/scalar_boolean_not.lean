import LeanExe.Extract.ScalarFunc

namespace BooleanNotTest

def boolNotEqual (x y : UInt64) : UInt64 :=
  if !(x == y) then x - y else x * 3 + 1

def boolNotUnequal (x y : UInt64) : UInt64 :=
  if !(x != y) then x + 7 else y / x

def boolNotTwice (x y : UInt64) : UInt64 :=
  if !(!(x == y)) then x / y else y % x

def boolNotThrice (x y : UInt64) : UInt64 :=
  if !(!(!(x != y))) then x <<< y else y >>> x

def boolNotNested (x y : UInt64) : UInt64 :=
  if !((if !(x == 0) then x + y else y) == (if !(y != 1) then x else y))
  then x ^^^ y else x + 11

def boolNotFunction (x y : UInt64) : UInt64 :=
  let f := fun a b : UInt64 => if !(a == b) then a * 3 + x else b - y
  if !(f x y != f y x) then f (x + y) x else f y (x - y)

def boolNotDo (x y : UInt64) : UInt64 := Id.run do
  let z ← if !(x == y) then pure (x + 7) else pure (y / x)
  let mut a := z
  if !(z != x) then a := a + y else a := a * 3
  return a + 1

def boolNotProposition (x y : UInt64) : UInt64 :=
  if ¬ (!(x == y)) then (if ¬ (!(!(x != y))) then x + 3 else y + 7) else x - y

def rangeBoolNotBreak (count seed : UInt64) : UInt64 := Id.run do
  let mut a := seed
  for i in [:count.toNat] do
    a := a + UInt64.ofNat i
    if !(a % 5 != seed % 5) then break
    a := a * 3 + 1
  return a

def rangeBoolNotContinue (count seed : UInt64) : UInt64 := Id.run do
  let mut a := seed
  for i in [1:count.toNat:2] do
    if !(UInt64.ofNat i % 3 == seed % 3) then continue
    a := a + UInt64.ofNat i
    if !(!(a % 7 == 0)) then break
  return a

def rangeBoolNotJoin (count seed : UInt64) : UInt64 :=
  forIn (m := Id) [:count.toNat] seed fun i a => do
    let result ← if !(UInt64.ofNat i != seed % 7) then pure (.done (a + 9)) else pure (.yield (a + 1))
    return result

def rangeBoolNotFunction (count seed : UInt64) : UInt64 :=
  forIn (m := Id) [(seed % 3).toNat:count.toNat] seed fun i a =>
    let finish : UInt64 → UInt64 → Id (ForInStep UInt64) := fun x y => do
      let z ← pure (x + y + UInt64.ofNat i)
      if !(!(!(z != seed))) then return .done (z + 17)
      return .yield (z * 3 + 1)
    finish a seed

def boolNotCustomBEq (x y : UInt64) : UInt64 :=
  if !(@BEq.beq UInt64 ⟨fun _ _ => true⟩ x y) then x else y

def boolNotDecision (b : Bool) : Decidable (b = true) := inferInstance

def boolNotCustomDecision (x y : UInt64) : UInt64 :=
  @ite UInt64 (@Eq Bool (Bool.not (x == y)) true) (boolNotDecision (Bool.not (x == y))) (x + 3) (y - 1)

def boolNotExternal (x y : UInt64) : Bool := x == y

def boolNotHelper (x y : UInt64) : UInt64 :=
  if !(boolNotExternal x y) then x + 3 else y - 1

def inputs : List (UInt64 × UInt64) :=
  [(0, 0), (1, 0), (0xffffffffffffffff, 0), (0, 1), (1, 1),
   (0xffffffffffffffff, 1), (0x8000000000000000, 2), (42, 3),
   (0xffffffffffffffff, 63), (0x8000000000000001, 64), (0xffffffffffffffff, 65),
   (0x0123456789abcdef, 0xffffffffffffffff), (3, 17), (17, 3)]

end BooleanNotTest

run_elab do
  let env ← Lean.getEnv
  let cases : List (Lean.Name × (UInt64 → UInt64 → UInt64) × Bool) := [
    (`BooleanNotTest.boolNotEqual, BooleanNotTest.boolNotEqual, false),
    (`BooleanNotTest.boolNotUnequal, BooleanNotTest.boolNotUnequal, false),
    (`BooleanNotTest.boolNotTwice, BooleanNotTest.boolNotTwice, false),
    (`BooleanNotTest.boolNotThrice, BooleanNotTest.boolNotThrice, false),
    (`BooleanNotTest.boolNotNested, BooleanNotTest.boolNotNested, false),
    (`BooleanNotTest.boolNotFunction, BooleanNotTest.boolNotFunction, false),
    (`BooleanNotTest.boolNotDo, BooleanNotTest.boolNotDo, false),
    (`BooleanNotTest.boolNotProposition, BooleanNotTest.boolNotProposition, false),
    (`BooleanNotTest.rangeBoolNotBreak, BooleanNotTest.rangeBoolNotBreak, true),
    (`BooleanNotTest.rangeBoolNotContinue, BooleanNotTest.rangeBoolNotContinue, true),
    (`BooleanNotTest.rangeBoolNotJoin, BooleanNotTest.rangeBoolNotJoin, true),
    (`BooleanNotTest.rangeBoolNotFunction, BooleanNotTest.rangeBoolNotFunction, true)]
  for (name, native, isRange) in cases do
    let some info := env.find? name | throwError "missing declaration"
    let some value := info.value? | throwError "missing body"
    let some func := LeanExe.Extract.Core.extractScalarFunc name (some "entry") info.type value |
      throwError "{name}: Boolean-not extraction failed"
    let module_ : LeanExe.IR.Module := { funcs := #[func] }
    let inputs := if isRange then
      ([0, 1, 2, 7, 16, 31] : List UInt64).flatMap fun n =>
        ([0, 1, 0x8000000000000000, 0xffffffffffffffff] : List UInt64).map fun seed => (n, seed)
      else BooleanNotTest.inputs
    for (x, y) in inputs do
      let expected := native x y
      let actual := module_.evalFunc 0 [x, y]
      unless actual == expected do
        throwError "{name}({x}, {y}): native={expected}, IR={actual}"
  for name in [`BooleanNotTest.boolNotCustomBEq, `BooleanNotTest.boolNotCustomDecision, `BooleanNotTest.boolNotHelper] do
    let some info := env.find? name | throwError "missing declaration"
    let some value := info.value? | throwError "missing body"
    unless (LeanExe.Extract.Core.extractScalarFunc name (some "entry") info.type value).isNone do
      throwError "{name}: unsupported Boolean guard accepted"
  Lean.logInfo "208 native/Boolean-not IR comparisons and three rejection tests passed"

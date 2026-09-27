import LeanExe.Extract.ScalarFunc

namespace BooleanInnerWrapperTest

def booleanInnerWrapperWord (x y : UInt64) : UInt64 :=
  (Id.run do
    let f := fun n : UInt64 => n == y
    return f x || f 0).toUInt64 + x

def booleanInnerWrapperBoolean (x y : UInt64) : UInt64 :=
  if (Id.run do
    let f := fun b : Bool => !b || y == 0
    return f (x == y) && f (x == 0)) then x + 7 else y + 11

def booleanInnerWrapperDependent (x y : UInt64) : UInt64 :=
  if _h : (Id.run do
    let f := fun n : UInt64 => n == y
    return f x || f 0) then x - 3 else y * 7

def booleanInnerWrapperNested (x y : UInt64) : UInt64 :=
  (Id.run (pure (let f := fun n : UInt64 => n == y; f x || f 0) : Id (Id Bool))).toUInt64 + x

def booleanInnerWrapperUnused (x y : UInt64) : UInt64 :=
  (pure (let _unused := fun b : Bool => b && x != 0; x == y) : Id Bool).toUInt64 + y

def booleanInnerWrapperIdResult (x y : UInt64) : UInt64 :=
  (pure (let f := fun n : UInt64 => (pure (n == y) : Id Bool); f x || f 0) : Id (Id Bool)).toUInt64 + x

def rangeInnerWrapperStep (count seed : UInt64) : Id UInt64 := do
  let mut a := seed
  for i in [:count.toNat] do
    if (Id.run do
      let f := fun n : UInt64 => n % 2 == 0
      return f a && f i.toUInt64) then
      a := a + i.toUInt64 + 7
    else a := a * 3 + 1
  return a

def rangeInnerWrapperExit (count seed : UInt64) : Id UInt64 := do
  let mut a := seed
  for i in [:count.toNat] do
    a := a + i.toUInt64 + 1
    if (Id.run do
      let f := fun n : UInt64 => n % 7 == 0
      return f a || f (i.toUInt64 + 1)) then break
  return a

def rangeInnerWrapperContinue (count seed : UInt64) : Id UInt64 := do
  let mut a := seed
  for i in [:count.toNat] do
    if (Id.run do
      let f := fun b : Bool => !b || a % 2 == 0
      return f (i.toUInt64 % 3 == 0) && f (a == seed)) then continue
    a := a * 3 + i.toUInt64 + 1
  return a

def rangeInnerWrapperTail (count seed : UInt64) : Id UInt64 := do
  let mut a := seed
  for i in [:count.toNat] do
    a := a + i.toUInt64 + 1
  return (Id.run do
    let f := fun n : UInt64 => n == seed
    return f a || f 0).toUInt64 + a

def inputs : List (UInt64 × UInt64) :=
  [(0, 0), (1, 0), (0xffffffffffffffff, 0), (0, 1), (1, 1),
   (0xffffffffffffffff, 1), (0x8000000000000000, 2), (42, 3),
   (0xffffffffffffffff, 63), (0x8000000000000001, 64), (0xffffffffffffffff, 65),
   (0x0123456789abcdef, 0xffffffffffffffff), (3, 17), (17, 3)]

end BooleanInnerWrapperTest

run_elab do
  let env ← Lean.getEnv
  let cases : List (Lean.Name × (UInt64 → UInt64 → UInt64) × Bool) := [
    (`BooleanInnerWrapperTest.booleanInnerWrapperWord, (fun (x y : UInt64) => BooleanInnerWrapperTest.booleanInnerWrapperWord x y), false),
    (`BooleanInnerWrapperTest.booleanInnerWrapperBoolean, (fun (x y : UInt64) => BooleanInnerWrapperTest.booleanInnerWrapperBoolean x y), false),
    (`BooleanInnerWrapperTest.booleanInnerWrapperDependent, (fun (x y : UInt64) => BooleanInnerWrapperTest.booleanInnerWrapperDependent x y), false),
    (`BooleanInnerWrapperTest.booleanInnerWrapperNested, (fun (x y : UInt64) => BooleanInnerWrapperTest.booleanInnerWrapperNested x y), false),
    (`BooleanInnerWrapperTest.booleanInnerWrapperUnused, (fun (x y : UInt64) => BooleanInnerWrapperTest.booleanInnerWrapperUnused x y), false),
    (`BooleanInnerWrapperTest.booleanInnerWrapperIdResult, (fun (x y : UInt64) => BooleanInnerWrapperTest.booleanInnerWrapperIdResult x y), false),
    (`BooleanInnerWrapperTest.rangeInnerWrapperStep, (fun (x y : UInt64) => BooleanInnerWrapperTest.rangeInnerWrapperStep x y), true),
    (`BooleanInnerWrapperTest.rangeInnerWrapperExit, (fun (x y : UInt64) => BooleanInnerWrapperTest.rangeInnerWrapperExit x y), true),
    (`BooleanInnerWrapperTest.rangeInnerWrapperContinue, (fun (x y : UInt64) => BooleanInnerWrapperTest.rangeInnerWrapperContinue x y), true),
    (`BooleanInnerWrapperTest.rangeInnerWrapperTail, (fun (x y : UInt64) => BooleanInnerWrapperTest.rangeInnerWrapperTail x y), true)]
  let mut comparisons : Nat := 0
  for (name, native, isRange) in cases do
    let some info := env.find? name | throwError "missing declaration"
    let some value := info.value? | throwError "missing body"
    let some func := LeanExe.Extract.Core.extractScalarFunc name (some "entry") info.type value |
      throwError "{name}: wrapped Boolean helper extraction failed"
    let module_ : LeanExe.IR.Module := { funcs := #[func] }
    let inputs := if isRange then
      ([0, 1, 2, 7, 16, 31] : List UInt64).flatMap fun n =>
        ([0, 1, 0x8000000000000000, 0xffffffffffffffff] : List UInt64).map fun seed => (n, seed)
      else BooleanInnerWrapperTest.inputs
    for (x, y) in inputs do
      let expected := native x y
      let actual := module_.evalFunc 0 [x, y]
      unless actual == expected do
        throwError "{name}({x}, {y}): native={expected}, IR={actual}"
      comparisons := comparisons + 1
  unless comparisons == 180 do throwError "unexpected comparison count {comparisons}"
  Lean.logInfo m!"{comparisons} native/wrapped Boolean helper IR comparisons passed"

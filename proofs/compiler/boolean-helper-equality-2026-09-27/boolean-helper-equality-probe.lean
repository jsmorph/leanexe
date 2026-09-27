import LeanExe.Extract.ScalarFunc
namespace BooleanHelperEqualityProbe
def booleanHelperEqualityLeft (x y : UInt64) : UInt64 :=
  ((let f := fun n : UInt64 => n == y; f x || f 0) == (x == 0)).toUInt64 + x

def booleanHelperEqualityRight (x y : UInt64) : UInt64 :=
  ((x == 0) != (Id.run do
    let f := fun b : Bool => !b || y == 0
    return f (x == y) && f (x == 0))).toUInt64 + x

def booleanHelperEqualityBoth (x y : UInt64) : UInt64 :=
  (decide ((let f := fun n : UInt64 => n == y; f x || f 0) =
    !(let g := fun b : Bool => !b || y == 0; g (x == y) && g (x == 0)))).toUInt64 + x

def booleanHelperEqualityDependent (x y : UInt64) : UInt64 :=
  if _h : decide ((let f := fun n : UInt64 => n == y; f x || f 0) ≠
    (let g := fun b : Bool => !b || y == 0; g (x == y) && g (x == 0))) then x + 7 else y + 11

def booleanHelperEqualityNested (x y : UInt64) : UInt64 :=
  ((!((let f := fun n : UInt64 => n == y; f x || f 0) ==
    (Id.run do
      let g := fun b : Bool => b || y != 0
      return g (x == y) && g (x == 0)))) ||
    (let h := fun n : UInt64 => n % 3 == 0; h x && h y)).toUInt64 + y

def booleanHelperEqualityUnused (x y : UInt64) : UInt64 :=
  ((let _unused := fun b : Bool => b && x != 0; x == y) !=
    !(let f := fun n : UInt64 => n == x; f y && f 0)).toUInt64 + y

def rangeHelperEqualityStep (count seed : UInt64) : Id UInt64 := do
  let mut a := seed
  for i in [:count.toNat] do
    if ((let f := fun n : UInt64 => n % 2 == 0; f a && f i.toUInt64) == (a == seed)) then
      a := a + i.toUInt64 + 7
    else a := a * 3 + 1
  return a

def rangeHelperEqualityExit (count seed : UInt64) : Id UInt64 := do
  let mut a := seed
  for i in [:count.toNat] do
    a := a + i.toUInt64 + 1
    if _h : decide ((let f := fun n : UInt64 => n % 7 == 0; f a || f (i.toUInt64 + 1)) ≠
        !(Id.run do
          let g := fun b : Bool => b || seed == 0
          return g (a == seed) && g (i.toUInt64 == 0))) then break
  return a

def rangeHelperEqualityContinue (count seed : UInt64) : Id UInt64 := do
  let mut a := seed
  for i in [:count.toNat] do
    if ((a == seed) != (let f := fun b : Bool => !b || a % 2 == 0; f (i.toUInt64 % 3 == 0) && f (a == seed))) then continue
    a := a * 3 + i.toUInt64 + 1
  return a

def rangeHelperEqualityTail (count seed : UInt64) : Id UInt64 := do
  let mut a := seed
  for i in [:count.toNat] do
    a := a + i.toUInt64 + 1
  return (decide ((let f := fun n : UInt64 => n == seed; f a || f 0) =
    !(Id.run do
      let g := fun b : Bool => b || seed == 0
      return g (a == seed) && g (a == 0)))).toUInt64 + a

end BooleanHelperEqualityProbe
run_elab do
  let env ← Lean.getEnv
  for name in [`BooleanHelperEqualityProbe.booleanHelperEqualityLeft, `BooleanHelperEqualityProbe.booleanHelperEqualityRight, `BooleanHelperEqualityProbe.booleanHelperEqualityBoth, `BooleanHelperEqualityProbe.booleanHelperEqualityDependent, `BooleanHelperEqualityProbe.booleanHelperEqualityNested, `BooleanHelperEqualityProbe.booleanHelperEqualityUnused, `BooleanHelperEqualityProbe.rangeHelperEqualityStep, `BooleanHelperEqualityProbe.rangeHelperEqualityExit, `BooleanHelperEqualityProbe.rangeHelperEqualityContinue, `BooleanHelperEqualityProbe.rangeHelperEqualityTail] do
    let some info := env.find? name | throwError "missing declaration"
    let some value := info.value? | throwError "missing body"
    Lean.logInfo m!"{name}: {(LeanExe.Extract.Core.extractScalarFunc name none info.type value).isSome}"

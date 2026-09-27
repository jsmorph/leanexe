import LeanExe.Extract.ScalarFunc

namespace BooleanHelperJunctionTest

def booleanHelperJunctionLeft (x y : UInt64) : UInt64 :=
  ((let f := fun n : UInt64 => n == y; f x || f 0) && (x == 0)).toUInt64 + x

def booleanHelperJunctionRight (x y : UInt64) : UInt64 :=
  ((x == 0) || (Id.run do
    let f := fun b : Bool => !b || y == 0
    return f (x == y) && f (x == 0))).toUInt64 + x

def booleanHelperJunctionBoth (x y : UInt64) : UInt64 :=
  ((let f := fun n : UInt64 => n == y; f x || f 0) &&
    !(let g := fun b : Bool => !b || y == 0; g (x == y) && g (x == 0))).toUInt64 + x

def booleanHelperJunctionDependent (x y : UInt64) : UInt64 :=
  if _h : ((let f := fun n : UInt64 => n == y; f x || f 0) ||
    (let g := fun b : Bool => !b || y == 0; g (x == y) && g (x == 0))) then x + 7 else y + 11

def booleanHelperJunctionNested (x y : UInt64) : UInt64 :=
  (((!(let f := fun n : UInt64 => n == y; f x || f 0)) &&
    (Id.run do
      let g := fun b : Bool => b || y != 0
      return g (x == y) && g (x == 0))) ||
    (let h := fun n : UInt64 => n % 3 == 0; h x && h y)).toUInt64 + y

def booleanHelperJunctionUnused (x y : UInt64) : UInt64 :=
  ((let _unused := fun b : Bool => b && x != 0; x == y) ||
    !(let f := fun n : UInt64 => n == x; f y && f 0)).toUInt64 + y

def rangeHelperJunctionStep (count seed : UInt64) : Id UInt64 := do
  let mut a := seed
  for i in [:count.toNat] do
    if ((let f := fun n : UInt64 => n % 2 == 0; f a && f i.toUInt64) || a == seed) then
      a := a + i.toUInt64 + 7
    else a := a * 3 + 1
  return a

def rangeHelperJunctionExit (count seed : UInt64) : Id UInt64 := do
  let mut a := seed
  for i in [:count.toNat] do
    a := a + i.toUInt64 + 1
    if _h : ((let f := fun n : UInt64 => n % 7 == 0; f a || f (i.toUInt64 + 1)) &&
        !(Id.run do
          let g := fun b : Bool => b || seed == 0
          return g (a == seed) && g (i.toUInt64 == 0))) then break
  return a

def rangeHelperJunctionContinue (count seed : UInt64) : Id UInt64 := do
  let mut a := seed
  for i in [:count.toNat] do
    if (a == seed || (let f := fun b : Bool => !b || a % 2 == 0; f (i.toUInt64 % 3 == 0) && f (a == seed))) then continue
    a := a * 3 + i.toUInt64 + 1
  return a

def rangeHelperJunctionTail (count seed : UInt64) : Id UInt64 := do
  let mut a := seed
  for i in [:count.toNat] do
    a := a + i.toUInt64 + 1
  return ((let f := fun n : UInt64 => n == seed; f a || f 0) &&
    !(Id.run do
      let g := fun b : Bool => b || seed == 0
      return g (a == seed) && g (a == 0))).toUInt64 + a

def inputs : List (UInt64 × UInt64) :=
  [(0, 0), (1, 0), (0xffffffffffffffff, 0), (0, 1), (1, 1),
   (0xffffffffffffffff, 1), (0x8000000000000000, 2), (42, 3),
   (0xffffffffffffffff, 63), (0x8000000000000001, 64), (0xffffffffffffffff, 65),
   (0x0123456789abcdef, 0xffffffffffffffff), (3, 17), (17, 3)]

end BooleanHelperJunctionTest

run_elab do
  let env ← Lean.getEnv
  let cases : List (Lean.Name × (UInt64 → UInt64 → UInt64) × Bool) := [
    (`BooleanHelperJunctionTest.booleanHelperJunctionLeft, (fun (x y : UInt64) => BooleanHelperJunctionTest.booleanHelperJunctionLeft x y), false),
    (`BooleanHelperJunctionTest.booleanHelperJunctionRight, (fun (x y : UInt64) => BooleanHelperJunctionTest.booleanHelperJunctionRight x y), false),
    (`BooleanHelperJunctionTest.booleanHelperJunctionBoth, (fun (x y : UInt64) => BooleanHelperJunctionTest.booleanHelperJunctionBoth x y), false),
    (`BooleanHelperJunctionTest.booleanHelperJunctionDependent, (fun (x y : UInt64) => BooleanHelperJunctionTest.booleanHelperJunctionDependent x y), false),
    (`BooleanHelperJunctionTest.booleanHelperJunctionNested, (fun (x y : UInt64) => BooleanHelperJunctionTest.booleanHelperJunctionNested x y), false),
    (`BooleanHelperJunctionTest.booleanHelperJunctionUnused, (fun (x y : UInt64) => BooleanHelperJunctionTest.booleanHelperJunctionUnused x y), false),
    (`BooleanHelperJunctionTest.rangeHelperJunctionStep, (fun (x y : UInt64) => BooleanHelperJunctionTest.rangeHelperJunctionStep x y), true),
    (`BooleanHelperJunctionTest.rangeHelperJunctionExit, (fun (x y : UInt64) => BooleanHelperJunctionTest.rangeHelperJunctionExit x y), true),
    (`BooleanHelperJunctionTest.rangeHelperJunctionContinue, (fun (x y : UInt64) => BooleanHelperJunctionTest.rangeHelperJunctionContinue x y), true),
    (`BooleanHelperJunctionTest.rangeHelperJunctionTail, (fun (x y : UInt64) => BooleanHelperJunctionTest.rangeHelperJunctionTail x y), true)]
  let mut comparisons : Nat := 0
  for (name, native, isRange) in cases do
    let some info := env.find? name | throwError "missing declaration"
    let some value := info.value? | throwError "missing body"
    let some func := LeanExe.Extract.Core.extractScalarFunc name (some "entry") info.type value |
      throwError "{name}: joined Boolean helper extraction failed"
    let module_ : LeanExe.IR.Module := { funcs := #[func] }
    let inputs := if isRange then
      ([0, 1, 2, 7, 16, 31] : List UInt64).flatMap fun n =>
        ([0, 1, 0x8000000000000000, 0xffffffffffffffff] : List UInt64).map fun seed => (n, seed)
      else BooleanHelperJunctionTest.inputs
    for (x, y) in inputs do
      let expected := native x y
      let actual := module_.evalFunc 0 [x, y]
      unless actual == expected do
        throwError "{name}({x}, {y}): native={expected}, IR={actual}"
      comparisons := comparisons + 1
  unless comparisons == 180 do throwError "unexpected comparison count {comparisons}"
  Lean.logInfo m!"{comparisons} native/joined Boolean helper IR comparisons passed"

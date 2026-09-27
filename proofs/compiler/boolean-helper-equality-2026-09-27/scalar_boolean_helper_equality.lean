import LeanExe.Extract.ScalarFunc

namespace BooleanHelperEqualityTest

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

def inputs : List (UInt64 × UInt64) :=
  [(0, 0), (1, 0), (0xffffffffffffffff, 0), (0, 1), (1, 1),
   (0xffffffffffffffff, 1), (0x8000000000000000, 2), (42, 3),
   (0xffffffffffffffff, 63), (0x8000000000000001, 64), (0xffffffffffffffff, 65),
   (0x0123456789abcdef, 0xffffffffffffffff), (3, 17), (17, 3)]

end BooleanHelperEqualityTest

run_elab do
  let env ← Lean.getEnv
  let cases : List (Lean.Name × (UInt64 → UInt64 → UInt64) × Bool) := [
    (`BooleanHelperEqualityTest.booleanHelperEqualityLeft, (fun (x y : UInt64) => BooleanHelperEqualityTest.booleanHelperEqualityLeft x y), false),
    (`BooleanHelperEqualityTest.booleanHelperEqualityRight, (fun (x y : UInt64) => BooleanHelperEqualityTest.booleanHelperEqualityRight x y), false),
    (`BooleanHelperEqualityTest.booleanHelperEqualityBoth, (fun (x y : UInt64) => BooleanHelperEqualityTest.booleanHelperEqualityBoth x y), false),
    (`BooleanHelperEqualityTest.booleanHelperEqualityDependent, (fun (x y : UInt64) => BooleanHelperEqualityTest.booleanHelperEqualityDependent x y), false),
    (`BooleanHelperEqualityTest.booleanHelperEqualityNested, (fun (x y : UInt64) => BooleanHelperEqualityTest.booleanHelperEqualityNested x y), false),
    (`BooleanHelperEqualityTest.booleanHelperEqualityUnused, (fun (x y : UInt64) => BooleanHelperEqualityTest.booleanHelperEqualityUnused x y), false),
    (`BooleanHelperEqualityTest.rangeHelperEqualityStep, (fun (x y : UInt64) => BooleanHelperEqualityTest.rangeHelperEqualityStep x y), true),
    (`BooleanHelperEqualityTest.rangeHelperEqualityExit, (fun (x y : UInt64) => BooleanHelperEqualityTest.rangeHelperEqualityExit x y), true),
    (`BooleanHelperEqualityTest.rangeHelperEqualityContinue, (fun (x y : UInt64) => BooleanHelperEqualityTest.rangeHelperEqualityContinue x y), true),
    (`BooleanHelperEqualityTest.rangeHelperEqualityTail, (fun (x y : UInt64) => BooleanHelperEqualityTest.rangeHelperEqualityTail x y), true)]
  let mut comparisons : Nat := 0
  for (name, native, isRange) in cases do
    let some info := env.find? name | throwError "missing declaration"
    let some value := info.value? | throwError "missing body"
    let some func := LeanExe.Extract.Core.extractScalarFunc name (some "entry") info.type value |
      throwError "{name}: related Boolean helper extraction failed"
    let module_ : LeanExe.IR.Module := { funcs := #[func] }
    let inputs := if isRange then
      ([0, 1, 2, 7, 16, 31] : List UInt64).flatMap fun n =>
        ([0, 1, 0x8000000000000000, 0xffffffffffffffff] : List UInt64).map fun seed => (n, seed)
      else BooleanHelperEqualityTest.inputs
    for (x, y) in inputs do
      let expected := native x y
      let actual := module_.evalFunc 0 [x, y]
      unless actual == expected do
        throwError "{name}({x}, {y}): native={expected}, IR={actual}"
      comparisons := comparisons + 1
  unless comparisons == 180 do throwError "unexpected comparison count {comparisons}"
  Lean.logInfo m!"{comparisons} native/related Boolean helper IR comparisons passed"

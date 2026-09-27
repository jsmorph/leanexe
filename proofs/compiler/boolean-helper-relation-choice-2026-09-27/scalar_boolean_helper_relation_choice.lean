import LeanExe.Extract.ScalarFunc

namespace BooleanHelperRelationChoiceTest

def booleanHelperRelationChoiceLeft (x y : UInt64) : UInt64 :=
  (if (let f := fun n : UInt64 => n == y; f x || f 0) = (x == 0) then
    (let g := fun b : Bool => b || y == 0; g (x == 0) && g (x == y)) else y == 0).toUInt64 + x

def booleanHelperRelationChoiceRight (x y : UInt64) : UInt64 :=
  (if (x == y) ≠ (Id.run do
      let f := fun b : Bool => !b || y == 0
      return f (x == y) && f (x == 0)) then
    (let g := fun n : UInt64 => n % 3 == 0; g x || g y) else x == 0).toUInt64 + x

def booleanHelperRelationChoiceFalse (x y : UInt64) : UInt64 :=
  (if (let f := fun n : UInt64 => n == y; f x || f 0) = false then
    (let g := fun b : Bool => b || y == 0; g (x == 0) && g (x == y)) else x == y).toUInt64 + x

def booleanHelperRelationChoiceDependent (x y : UInt64) : UInt64 :=
  (if _h : (let f := fun n : UInt64 => n == y; f x || f 0) =
      (let h := fun n : UInt64 => n % 3 == 0; h x || h y) then
    (let g := fun b : Bool => !b || y == 0; g (x == y) && g (x == 0))
   else (let h := fun n : UInt64 => n % 5 == 0; h x && h y)).toUInt64 + y

def booleanHelperRelationChoiceTrue (x y : UInt64) : UInt64 :=
  (if _h : (let g := fun b : Bool => b || y == 0; g (x == 0) && g (x == y)) ≠ true then
    (let f := fun n : UInt64 => n == y; f x || f 0) else x == y).toUInt64 + x

def booleanHelperRelationChoiceNested (x y : UInt64) : UInt64 :=
  (Id.run do
    if _h : (let f := fun n : UInt64 => n == y; f x || f 0) ≠ false then
      return if (x == 0) = false then
        (let g := fun b : Bool => b || y != 0; g (x == y) && g (x == 0))
        else false
    else return !(let h := fun n : UInt64 => n % 3 == 0; h x && h y)).toUInt64 + x

def rangeHelperRelationChoiceStep (count seed : UInt64) : Id UInt64 := do
  let mut a := seed
  for i in [:count.toNat] do
    if (if (let f := fun n : UInt64 => n % 2 == 0; f a && f i.toUInt64) = (a == seed) then
        (let g := fun b : Bool => !b || seed == 0; g (a == seed) && g (i.toUInt64 == 0)) else a == seed) then
      a := a + i.toUInt64 + 7
    else a := a * 3 + 1
  return a

def rangeHelperRelationChoiceExit (count seed : UInt64) : Id UInt64 := do
  let mut a := seed
  for i in [:count.toNat] do
    a := a + i.toUInt64 + 1
    if _h : (if _h : (let f := fun n : UInt64 => n % 7 == 0; f a || f (i.toUInt64 + 1)) ≠ false then
        !(Id.run do
          let g := fun b : Bool => b || seed == 0
          return g (a == seed) && g (i.toUInt64 == 0))
      else a % 11 == 0) then break
  return a

def rangeHelperRelationChoiceContinue (count seed : UInt64) : Id UInt64 := do
  let mut a := seed
  for i in [:count.toNat] do
    if (if (a == seed) ≠ (let f := fun n : UInt64 => n % 3 == 0; f a || f i.toUInt64) then
        (let f := fun b : Bool => !b || a % 2 == 0; f (i.toUInt64 % 3 == 0) && f (a == seed))
      else false) then continue
    a := a * 3 + i.toUInt64 + 1
  return a

def rangeHelperRelationChoiceTail (count seed : UInt64) : Id UInt64 := do
  let mut a := seed
  for i in [:count.toNat] do
    a := a + i.toUInt64 + 1
  return (if (let f := fun n : UInt64 => n == seed; f a || f 0) = false then
      (let f := fun n : UInt64 => n % 3 == 0; f a && f seed)
    else !(Id.run do
      let g := fun b : Bool => b || seed == 0
      return g (a == seed) && g (a == 0))).toUInt64 + a

def inputs : List (UInt64 × UInt64) :=
  [(0, 0), (1, 0), (0xffffffffffffffff, 0), (0, 1), (1, 1),
   (0xffffffffffffffff, 1), (0x8000000000000000, 2), (42, 3),
   (0xffffffffffffffff, 63), (0x8000000000000001, 64), (0xffffffffffffffff, 65),
   (0x0123456789abcdef, 0xffffffffffffffff), (3, 17), (17, 3)]

end BooleanHelperRelationChoiceTest

run_elab do
  let env ← Lean.getEnv
  let cases : List (Lean.Name × (UInt64 → UInt64 → UInt64) × Bool) := [
    (`BooleanHelperRelationChoiceTest.booleanHelperRelationChoiceLeft, (fun (x y : UInt64) => BooleanHelperRelationChoiceTest.booleanHelperRelationChoiceLeft x y), false),
    (`BooleanHelperRelationChoiceTest.booleanHelperRelationChoiceRight, (fun (x y : UInt64) => BooleanHelperRelationChoiceTest.booleanHelperRelationChoiceRight x y), false),
    (`BooleanHelperRelationChoiceTest.booleanHelperRelationChoiceFalse, (fun (x y : UInt64) => BooleanHelperRelationChoiceTest.booleanHelperRelationChoiceFalse x y), false),
    (`BooleanHelperRelationChoiceTest.booleanHelperRelationChoiceDependent, (fun (x y : UInt64) => BooleanHelperRelationChoiceTest.booleanHelperRelationChoiceDependent x y), false),
    (`BooleanHelperRelationChoiceTest.booleanHelperRelationChoiceTrue, (fun (x y : UInt64) => BooleanHelperRelationChoiceTest.booleanHelperRelationChoiceTrue x y), false),
    (`BooleanHelperRelationChoiceTest.booleanHelperRelationChoiceNested, (fun (x y : UInt64) => BooleanHelperRelationChoiceTest.booleanHelperRelationChoiceNested x y), false),
    (`BooleanHelperRelationChoiceTest.rangeHelperRelationChoiceStep, (fun (x y : UInt64) => BooleanHelperRelationChoiceTest.rangeHelperRelationChoiceStep x y), true),
    (`BooleanHelperRelationChoiceTest.rangeHelperRelationChoiceExit, (fun (x y : UInt64) => BooleanHelperRelationChoiceTest.rangeHelperRelationChoiceExit x y), true),
    (`BooleanHelperRelationChoiceTest.rangeHelperRelationChoiceContinue, (fun (x y : UInt64) => BooleanHelperRelationChoiceTest.rangeHelperRelationChoiceContinue x y), true),
    (`BooleanHelperRelationChoiceTest.rangeHelperRelationChoiceTail, (fun (x y : UInt64) => BooleanHelperRelationChoiceTest.rangeHelperRelationChoiceTail x y), true)]
  let mut comparisons : Nat := 0
  for (name, native, isRange) in cases do
    let some info := env.find? name | throwError "missing declaration"
    let some value := info.value? | throwError "missing body"
    let some func := LeanExe.Extract.Core.extractScalarFunc name (some "entry") info.type value |
      throwError "{name}: relation-choice Boolean helper extraction failed"
    let module_ : LeanExe.IR.Module := { funcs := #[func] }
    let inputs := if isRange then
      ([0, 1, 2, 7, 16, 31] : List UInt64).flatMap fun n =>
        ([0, 1, 0x8000000000000000, 0xffffffffffffffff] : List UInt64).map fun seed => (n, seed)
      else BooleanHelperRelationChoiceTest.inputs
    for (x, y) in inputs do
      let expected := native x y
      let actual := module_.evalFunc 0 [x, y]
      unless actual == expected do
        throwError "{name}({x}, {y}): native={expected}, IR={actual}"
      comparisons := comparisons + 1
  unless comparisons == 180 do throwError "unexpected comparison count {comparisons}"
  Lean.logInfo m!"{comparisons} native/relation-choice Boolean helper IR comparisons passed"

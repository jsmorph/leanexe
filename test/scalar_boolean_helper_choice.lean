import LeanExe.Extract.ScalarFunc

namespace BooleanHelperChoiceTest

def booleanHelperChoiceCondition (x y : UInt64) : UInt64 :=
  (if (let f := fun n : UInt64 => n == y; f x || f 0) then x == 0 else y == 0).toUInt64 + x

def booleanHelperChoiceYes (x y : UInt64) : UInt64 :=
  (if x == y then (Id.run do
    let f := fun b : Bool => !b || y == 0
    return f (x == y) && f (x == 0)) else y != 0).toUInt64 + x

def booleanHelperChoiceNo (x y : UInt64) : UInt64 :=
  (if x == 0 then x == y else
    !(let g := fun b : Bool => !b || y == 0; g (x == y) && g (x == 0))).toUInt64 + y

def booleanHelperChoiceDependent (x y : UInt64) : UInt64 :=
  (if _h : (let f := fun n : UInt64 => n == y; f x || f 0) then
    (let g := fun b : Bool => !b || y == 0; g (x == y) && g (x == 0))
   else (let h := fun n : UInt64 => n % 3 == 0; h x || h y)).toUInt64 + y

def booleanHelperChoiceNested (x y : UInt64) : UInt64 :=
  (Id.run do
    if _h : (let f := fun n : UInt64 => n == y; f x || f 0) then
      return if x == 0 then
        (let g := fun b : Bool => b || y != 0; g (x == y) && g (x == 0))
        else false
    else return !(let h := fun n : UInt64 => n % 3 == 0; h x && h y)).toUInt64 + x

def booleanHelperChoiceUnused (x y : UInt64) : UInt64 :=
  (if false then (let _unused := fun b : Bool => b && x != 0; x == y)
   else (let f := fun n : UInt64 => n == x; f y && f 0)).toUInt64 + y

def rangeHelperChoiceStep (count seed : UInt64) : Id UInt64 := do
  let mut a := seed
  for i in [:count.toNat] do
    if (if (let f := fun n : UInt64 => n % 2 == 0; f a && f i.toUInt64) then a == seed else i.toUInt64 == 0) then
      a := a + i.toUInt64 + 7
    else a := a * 3 + 1
  return a

def rangeHelperChoiceExit (count seed : UInt64) : Id UInt64 := do
  let mut a := seed
  for i in [:count.toNat] do
    a := a + i.toUInt64 + 1
    if _h : (if _h : (let f := fun n : UInt64 => n % 7 == 0; f a || f (i.toUInt64 + 1)) then
        !(Id.run do
          let g := fun b : Bool => b || seed == 0
          return g (a == seed) && g (i.toUInt64 == 0))
      else a % 11 == 0) then break
  return a

def rangeHelperChoiceContinue (count seed : UInt64) : Id UInt64 := do
  let mut a := seed
  for i in [:count.toNat] do
    if (if a == seed then
        (let f := fun b : Bool => !b || a % 2 == 0; f (i.toUInt64 % 3 == 0) && f (a == seed))
      else false) then continue
    a := a * 3 + i.toUInt64 + 1
  return a

def rangeHelperChoiceTail (count seed : UInt64) : Id UInt64 := do
  let mut a := seed
  for i in [:count.toNat] do
    a := a + i.toUInt64 + 1
  return (if a == 0 then (let f := fun n : UInt64 => n == seed; f a || f 0)
    else !(Id.run do
      let g := fun b : Bool => b || seed == 0
      return g (a == seed) && g (a == 0))).toUInt64 + a

def inputs : List (UInt64 × UInt64) :=
  [(0, 0), (1, 0), (0xffffffffffffffff, 0), (0, 1), (1, 1),
   (0xffffffffffffffff, 1), (0x8000000000000000, 2), (42, 3),
   (0xffffffffffffffff, 63), (0x8000000000000001, 64), (0xffffffffffffffff, 65),
   (0x0123456789abcdef, 0xffffffffffffffff), (3, 17), (17, 3)]

end BooleanHelperChoiceTest

run_elab do
  let env ← Lean.getEnv
  let cases : List (Lean.Name × (UInt64 → UInt64 → UInt64) × Bool) := [
    (`BooleanHelperChoiceTest.booleanHelperChoiceCondition, (fun (x y : UInt64) => BooleanHelperChoiceTest.booleanHelperChoiceCondition x y), false),
    (`BooleanHelperChoiceTest.booleanHelperChoiceYes, (fun (x y : UInt64) => BooleanHelperChoiceTest.booleanHelperChoiceYes x y), false),
    (`BooleanHelperChoiceTest.booleanHelperChoiceNo, (fun (x y : UInt64) => BooleanHelperChoiceTest.booleanHelperChoiceNo x y), false),
    (`BooleanHelperChoiceTest.booleanHelperChoiceDependent, (fun (x y : UInt64) => BooleanHelperChoiceTest.booleanHelperChoiceDependent x y), false),
    (`BooleanHelperChoiceTest.booleanHelperChoiceNested, (fun (x y : UInt64) => BooleanHelperChoiceTest.booleanHelperChoiceNested x y), false),
    (`BooleanHelperChoiceTest.booleanHelperChoiceUnused, (fun (x y : UInt64) => BooleanHelperChoiceTest.booleanHelperChoiceUnused x y), false),
    (`BooleanHelperChoiceTest.rangeHelperChoiceStep, (fun (x y : UInt64) => BooleanHelperChoiceTest.rangeHelperChoiceStep x y), true),
    (`BooleanHelperChoiceTest.rangeHelperChoiceExit, (fun (x y : UInt64) => BooleanHelperChoiceTest.rangeHelperChoiceExit x y), true),
    (`BooleanHelperChoiceTest.rangeHelperChoiceContinue, (fun (x y : UInt64) => BooleanHelperChoiceTest.rangeHelperChoiceContinue x y), true),
    (`BooleanHelperChoiceTest.rangeHelperChoiceTail, (fun (x y : UInt64) => BooleanHelperChoiceTest.rangeHelperChoiceTail x y), true)]
  let mut comparisons : Nat := 0
  for (name, native, isRange) in cases do
    let some info := env.find? name | throwError "missing declaration"
    let some value := info.value? | throwError "missing body"
    let some func := LeanExe.Extract.Core.extractScalarFunc name (some "entry") info.type value |
      throwError "{name}: conditional Boolean helper extraction failed"
    let module_ : LeanExe.IR.Module := { funcs := #[func] }
    let inputs := if isRange then
      ([0, 1, 2, 7, 16, 31] : List UInt64).flatMap fun n =>
        ([0, 1, 0x8000000000000000, 0xffffffffffffffff] : List UInt64).map fun seed => (n, seed)
      else BooleanHelperChoiceTest.inputs
    for (x, y) in inputs do
      let expected := native x y
      let actual := module_.evalFunc 0 [x, y]
      unless actual == expected do
        throwError "{name}({x}, {y}): native={expected}, IR={actual}"
      comparisons := comparisons + 1
  unless comparisons == 180 do throwError "unexpected comparison count {comparisons}"
  Lean.logInfo m!"{comparisons} native/conditional Boolean helper IR comparisons passed"

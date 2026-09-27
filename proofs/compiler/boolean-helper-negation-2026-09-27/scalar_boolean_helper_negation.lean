import LeanExe.Extract.ScalarFunc

namespace BooleanHelperNegationTest

def booleanHelperNegationWord (x y : UInt64) : UInt64 :=
  (!(let f := fun n : UInt64 => n == y; f x || f 0)).toUInt64 + x

def booleanHelperNegationBoolean (x y : UInt64) : UInt64 :=
  if !(Id.run do
    let f := fun b : Bool => !b || y == 0
    return f (x == y) && f (x == 0)) then x + 7 else y + 11

def booleanHelperNegationDependent (x y : UInt64) : UInt64 :=
  if _h : !(let f := fun n : UInt64 => n == y; f x || f 0) then x - 3 else y * 7

def booleanHelperNegationNested (x y : UInt64) : UInt64 :=
  (!(!(!(Id.run (pure (let f := fun n : UInt64 => n == y; f x || f 0) : Id (Id Bool)))))).toUInt64 + x

def booleanHelperNegationUnused (x y : UInt64) : UInt64 :=
  (!(let _unused := fun b : Bool => b && x != 0; x == y)).toUInt64 + y

def booleanHelperNegationIdResult (x y : UInt64) : UInt64 :=
  (!(!(pure (let f := fun n : UInt64 => (pure (n == y) : Id Bool); f x || f 0) : Id (Id Bool)))).toUInt64 + x

def rangeHelperNegationStep (count seed : UInt64) : Id UInt64 := do
  let mut a := seed
  for i in [:count.toNat] do
    if !(let f := fun n : UInt64 => n % 2 == 0; f a && f i.toUInt64) then
      a := a + i.toUInt64 + 7
    else a := a * 3 + 1
  return a

def rangeHelperNegationExit (count seed : UInt64) : Id UInt64 := do
  let mut a := seed
  for i in [:count.toNat] do
    a := a + i.toUInt64 + 1
    if !(Id.run do
      let f := fun n : UInt64 => n % 7 == 0
      return f a || f (i.toUInt64 + 1)) then break
  return a

def rangeHelperNegationContinue (count seed : UInt64) : Id UInt64 := do
  let mut a := seed
  for i in [:count.toNat] do
    if !(!(let f := fun b : Bool => !b || a % 2 == 0; f (i.toUInt64 % 3 == 0) && f (a == seed))) then continue
    a := a * 3 + i.toUInt64 + 1
  return a

def rangeHelperNegationTail (count seed : UInt64) : Id UInt64 := do
  let mut a := seed
  for i in [:count.toNat] do
    a := a + i.toUInt64 + 1
  return (!(Id.run do
    let f := fun n : UInt64 => n == seed
    return f a || f 0)).toUInt64 + a

def inputs : List (UInt64 × UInt64) :=
  [(0, 0), (1, 0), (0xffffffffffffffff, 0), (0, 1), (1, 1),
   (0xffffffffffffffff, 1), (0x8000000000000000, 2), (42, 3),
   (0xffffffffffffffff, 63), (0x8000000000000001, 64), (0xffffffffffffffff, 65),
   (0x0123456789abcdef, 0xffffffffffffffff), (3, 17), (17, 3)]

end BooleanHelperNegationTest

run_elab do
  let env ← Lean.getEnv
  let cases : List (Lean.Name × (UInt64 → UInt64 → UInt64) × Bool) := [
    (`BooleanHelperNegationTest.booleanHelperNegationWord, (fun (x y : UInt64) => BooleanHelperNegationTest.booleanHelperNegationWord x y), false),
    (`BooleanHelperNegationTest.booleanHelperNegationBoolean, (fun (x y : UInt64) => BooleanHelperNegationTest.booleanHelperNegationBoolean x y), false),
    (`BooleanHelperNegationTest.booleanHelperNegationDependent, (fun (x y : UInt64) => BooleanHelperNegationTest.booleanHelperNegationDependent x y), false),
    (`BooleanHelperNegationTest.booleanHelperNegationNested, (fun (x y : UInt64) => BooleanHelperNegationTest.booleanHelperNegationNested x y), false),
    (`BooleanHelperNegationTest.booleanHelperNegationUnused, (fun (x y : UInt64) => BooleanHelperNegationTest.booleanHelperNegationUnused x y), false),
    (`BooleanHelperNegationTest.booleanHelperNegationIdResult, (fun (x y : UInt64) => BooleanHelperNegationTest.booleanHelperNegationIdResult x y), false),
    (`BooleanHelperNegationTest.rangeHelperNegationStep, (fun (x y : UInt64) => BooleanHelperNegationTest.rangeHelperNegationStep x y), true),
    (`BooleanHelperNegationTest.rangeHelperNegationExit, (fun (x y : UInt64) => BooleanHelperNegationTest.rangeHelperNegationExit x y), true),
    (`BooleanHelperNegationTest.rangeHelperNegationContinue, (fun (x y : UInt64) => BooleanHelperNegationTest.rangeHelperNegationContinue x y), true),
    (`BooleanHelperNegationTest.rangeHelperNegationTail, (fun (x y : UInt64) => BooleanHelperNegationTest.rangeHelperNegationTail x y), true)]
  let mut comparisons : Nat := 0
  for (name, native, isRange) in cases do
    let some info := env.find? name | throwError "missing declaration"
    let some value := info.value? | throwError "missing body"
    let some func := LeanExe.Extract.Core.extractScalarFunc name (some "entry") info.type value |
      throwError "{name}: negated Boolean helper extraction failed"
    let module_ : LeanExe.IR.Module := { funcs := #[func] }
    let inputs := if isRange then
      ([0, 1, 2, 7, 16, 31] : List UInt64).flatMap fun n =>
        ([0, 1, 0x8000000000000000, 0xffffffffffffffff] : List UInt64).map fun seed => (n, seed)
      else BooleanHelperNegationTest.inputs
    for (x, y) in inputs do
      let expected := native x y
      let actual := module_.evalFunc 0 [x, y]
      unless actual == expected do
        throwError "{name}({x}, {y}): native={expected}, IR={actual}"
      comparisons := comparisons + 1
  unless comparisons == 180 do throwError "unexpected comparison count {comparisons}"
  Lean.logInfo m!"{comparisons} native/negated Boolean helper IR comparisons passed"

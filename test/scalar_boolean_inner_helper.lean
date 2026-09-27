import LeanExe.Extract.ScalarFunc

namespace BooleanInnerHelperTest

def booleanInnerHelperWord (x y : UInt64) : UInt64 :=
  (let f := fun n : UInt64 => n == y; f x || f 0).toUInt64 + x

def booleanInnerHelperBoolean (x y : UInt64) : UInt64 :=
  if (let f := fun b : Bool => !b || y == 0; f (x == y) && f (x == 0)) then x + 7 else y + 11

def booleanInnerHelperDependent (x y : UInt64) : UInt64 :=
  if _h : (let f := fun n : UInt64 => n == y; f x || f 0) then x - 3 else y * 7

def booleanInnerHelperNested (x y : UInt64) : UInt64 :=
  (let f := fun n : UInt64 => n == y
   let g := fun b : Bool => !b || x == 0
   g (f x) && g (f 0)).toUInt64 + x

def booleanInnerHelperUnused (x y : UInt64) : UInt64 :=
  (let _unused := fun b : Bool => b && x != 0; x == y).toUInt64 + y

def booleanInnerHelperIdResult (x y : UInt64) : UInt64 :=
  (let f := fun n : UInt64 => (pure (n == y) : Id Bool); f x || f 0).toUInt64 + x

def rangeInnerHelperStep (count seed : UInt64) : Id UInt64 := do
  let mut a := seed
  for i in [:count.toNat] do
    if (let f := fun n : UInt64 => n % 2 == 0; f a && f i.toUInt64) then
      a := a + i.toUInt64 + 7
    else a := a * 3 + 1
  return a

def rangeInnerHelperExit (count seed : UInt64) : Id UInt64 := do
  let mut a := seed
  for i in [:count.toNat] do
    a := a + i.toUInt64 + 1
    if (let f := fun n : UInt64 => n % 7 == 0; f a || f (i.toUInt64 + 1)) then break
  return a

def rangeInnerHelperContinue (count seed : UInt64) : Id UInt64 := do
  let mut a := seed
  for i in [:count.toNat] do
    if (let f := fun b : Bool => !b || a % 2 == 0; f (i.toUInt64 % 3 == 0) && f (a == seed)) then continue
    a := a * 3 + i.toUInt64 + 1
  return a

def rangeInnerHelperTail (count seed : UInt64) : Id UInt64 := do
  let mut a := seed
  for i in [:count.toNat] do
    a := a + i.toUInt64 + 1
  return (let f := fun n : UInt64 => n == seed; f a || f 0).toUInt64 + a

def inputs : List (UInt64 × UInt64) :=
  [(0, 0), (1, 0), (0xffffffffffffffff, 0), (0, 1), (1, 1),
   (0xffffffffffffffff, 1), (0x8000000000000000, 2), (42, 3),
   (0xffffffffffffffff, 63), (0x8000000000000001, 64), (0xffffffffffffffff, 65),
   (0x0123456789abcdef, 0xffffffffffffffff), (3, 17), (17, 3)]

end BooleanInnerHelperTest

run_elab do
  let env ← Lean.getEnv
  let cases : List (Lean.Name × (UInt64 → UInt64 → UInt64) × Bool) := [
    (`BooleanInnerHelperTest.booleanInnerHelperWord, (fun (x y : UInt64) => BooleanInnerHelperTest.booleanInnerHelperWord x y), false),
    (`BooleanInnerHelperTest.booleanInnerHelperBoolean, (fun (x y : UInt64) => BooleanInnerHelperTest.booleanInnerHelperBoolean x y), false),
    (`BooleanInnerHelperTest.booleanInnerHelperDependent, (fun (x y : UInt64) => BooleanInnerHelperTest.booleanInnerHelperDependent x y), false),
    (`BooleanInnerHelperTest.booleanInnerHelperNested, (fun (x y : UInt64) => BooleanInnerHelperTest.booleanInnerHelperNested x y), false),
    (`BooleanInnerHelperTest.booleanInnerHelperUnused, (fun (x y : UInt64) => BooleanInnerHelperTest.booleanInnerHelperUnused x y), false),
    (`BooleanInnerHelperTest.booleanInnerHelperIdResult, (fun (x y : UInt64) => BooleanInnerHelperTest.booleanInnerHelperIdResult x y), false),
    (`BooleanInnerHelperTest.rangeInnerHelperStep, (fun (x y : UInt64) => BooleanInnerHelperTest.rangeInnerHelperStep x y), true),
    (`BooleanInnerHelperTest.rangeInnerHelperExit, (fun (x y : UInt64) => BooleanInnerHelperTest.rangeInnerHelperExit x y), true),
    (`BooleanInnerHelperTest.rangeInnerHelperContinue, (fun (x y : UInt64) => BooleanInnerHelperTest.rangeInnerHelperContinue x y), true),
    (`BooleanInnerHelperTest.rangeInnerHelperTail, (fun (x y : UInt64) => BooleanInnerHelperTest.rangeInnerHelperTail x y), true)]
  let mut comparisons : Nat := 0
  for (name, native, isRange) in cases do
    let some info := env.find? name | throwError "missing declaration"
    let some value := info.value? | throwError "missing body"
    let some func := LeanExe.Extract.Core.extractScalarFunc name (some "entry") info.type value |
      throwError "{name}: inner Boolean helper extraction failed"
    let module_ : LeanExe.IR.Module := { funcs := #[func] }
    let inputs := if isRange then
      ([0, 1, 2, 7, 16, 31] : List UInt64).flatMap fun n =>
        ([0, 1, 0x8000000000000000, 0xffffffffffffffff] : List UInt64).map fun seed => (n, seed)
      else BooleanInnerHelperTest.inputs
    for (x, y) in inputs do
      let expected := native x y
      let actual := module_.evalFunc 0 [x, y]
      unless actual == expected do
        throwError "{name}({x}, {y}): native={expected}, IR={actual}"
      comparisons := comparisons + 1
  unless comparisons == 180 do throwError "unexpected comparison count {comparisons}"
  Lean.logInfo m!"{comparisons} native/inner Boolean helper IR comparisons passed"

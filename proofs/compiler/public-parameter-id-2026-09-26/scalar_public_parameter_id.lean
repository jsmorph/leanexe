import LeanExe.Extract.ScalarFunc

namespace PublicParameterIdTest

def publicInputIdWord (x : Id UInt64) (y : UInt64) : UInt64 := Id.run x + y

def publicInputIdFlag (flag : Id Bool) (x : UInt64) : UInt64 :=
  if Id.run flag then x + 7 else x - 3

def publicInputIdBoth (flag : Id (Id Bool)) (x : Id (Id UInt64)) : Id UInt64 :=
  pure (Id.run (Id.run x) + (Id.run (Id.run flag)).toUInt64)

def publicInputIdResult (x : Id UInt64) (flag : Id Bool) : Bool :=
  Id.run flag && Id.run x != 0

def publicInputIdCapture (flag : Id Bool) (x : Id UInt64) : Bool :=
  let f := fun b : Bool => b && Id.run flag && Id.run x != 0
  f (Id.run flag)

def publicInputIdBind (flag : Id Bool) (x : Id UInt64) : Id Bool := do
  let saved ← flag
  let n ← x
  return saved && n != 0

def rangeInputIdYield (count : Id UInt64) (flag : Id Bool) : UInt64 := Id.run do
  let mut a := (Id.run flag).toUInt64
  for i in [:(Id.run count).toNat] do
    a := a + i.toUInt64 + (Id.run flag).toUInt64
  return a

def rangeInputIdExit (count : Id (Id UInt64)) (flag : Id (Id Bool)) : Id UInt64 := do
  let mut a : UInt64 := 1
  for i in [:(Id.run (Id.run count)).toNat] do
    a := a + i.toUInt64 + 1
    if Id.run (Id.run flag) && a % 7 == 0 then break
  return a

def rangeInputIdContinue (count : Id UInt64) (flag : Id Bool) : UInt64 := Id.run do
  let saved ← flag
  let mut a := Id.run count
  for i in [:(Id.run count).toNat] do
    if saved && i.toUInt64 % 3 == 0 then continue
    a := a + i.toUInt64 + saved.toUInt64
  return a

def rangeInputIdCapture (count : Id UInt64) (flag : Id Bool) : UInt64 := Id.run do
  let f := fun b : Bool => if b then Id.run count + (Id.run flag).toUInt64 else Id.run count
  let mut a := f false
  for i in [:(Id.run count).toNat] do
    a := a + f (i.toUInt64 % 2 == 0)
    if a % 11 == 0 then break
  return a

def inputs : List (UInt64 × UInt64) :=
  [(0, 0), (1, 0), (0xffffffffffffffff, 0), (0, 1), (1, 1),
   (0xffffffffffffffff, 1), (0x8000000000000000, 2), (42, 3),
   (0xffffffffffffffff, 63), (0x8000000000000001, 64), (0xffffffffffffffff, 65),
   (0x0123456789abcdef, 0xffffffffffffffff), (3, 17), (17, 3)]

end PublicParameterIdTest

run_elab do
  let env ← Lean.getEnv
  let cases : List (Lean.Name × (UInt64 → UInt64 → UInt64) × Bool) := [
    (`PublicParameterIdTest.publicInputIdWord, (fun x y => Id.run (PublicParameterIdTest.publicInputIdWord x y)), false),
    (`PublicParameterIdTest.publicInputIdFlag, (fun x y => Id.run (PublicParameterIdTest.publicInputIdFlag (x != 0) y)), false),
    (`PublicParameterIdTest.publicInputIdBoth, (fun x y => Id.run (PublicParameterIdTest.publicInputIdBoth (x != 0) y)), false),
    (`PublicParameterIdTest.publicInputIdResult, (fun x y => (PublicParameterIdTest.publicInputIdResult x (y != 0)).toUInt64), false),
    (`PublicParameterIdTest.publicInputIdCapture, (fun x y => (PublicParameterIdTest.publicInputIdCapture (x != 0) y).toUInt64), false),
    (`PublicParameterIdTest.publicInputIdBind, (fun x y => (PublicParameterIdTest.publicInputIdBind (x != 0) y).toUInt64), false),
    (`PublicParameterIdTest.rangeInputIdYield, (fun x y => Id.run (PublicParameterIdTest.rangeInputIdYield x (y != 0))), true),
    (`PublicParameterIdTest.rangeInputIdExit, (fun x y => Id.run (PublicParameterIdTest.rangeInputIdExit x (y != 0))), true),
    (`PublicParameterIdTest.rangeInputIdContinue, (fun x y => Id.run (PublicParameterIdTest.rangeInputIdContinue x (y != 0))), true),
    (`PublicParameterIdTest.rangeInputIdCapture, (fun x y => Id.run (PublicParameterIdTest.rangeInputIdCapture x (y != 0))), true)]
  let mut comparisons : Nat := 0
  for (name, native, isRange) in cases do
    let some info := env.find? name | throwError "missing declaration"
    let some value := info.value? | throwError "missing body"
    let some func := LeanExe.Extract.Core.extractScalarFunc name (some "entry") info.type value |
      throwError "{name}: reusable Boolean helper extraction failed"
    let module_ : LeanExe.IR.Module := { funcs := #[func] }
    let inputs := if isRange then
      ([0, 1, 2, 7, 16, 31] : List UInt64).flatMap fun n =>
        ([0, 1, 0x8000000000000000, 0xffffffffffffffff] : List UInt64).map fun seed => (n, seed)
      else PublicParameterIdTest.inputs
    for (x, y) in inputs do
      let expected := native x y
      let actual := module_.evalFunc 0 [x, y]
      unless actual == expected do
        throwError "{name}({x}, {y}): native={expected}, IR={actual}"
      comparisons := comparisons + 1
  unless comparisons == 180 do throwError "unexpected comparison count {comparisons}"
  Lean.logInfo m!"{comparisons} native/public parameter-Id IR comparisons passed"

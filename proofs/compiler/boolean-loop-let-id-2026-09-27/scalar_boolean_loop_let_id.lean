import LeanExe.Extract.ScalarFunc

namespace BooleanLoopLetIdTest

def rangeBoolLetIdWord (count seed : UInt64) : Bool :=
  let start : Id UInt64 := seed + 7
  let value := Id.run do
    let mut a := Id.run start
    for i in [:count.toNat] do
      a := a + i.toUInt64 + 1
    return a
  value == Id.run start

def rangeBoolLetIdWordLayers (count seed : UInt64) : Bool :=
  let start : Id (Id UInt64) := pure (pure (seed + 1))
  let stop : Id UInt64 := count % 17
  let value := Id.run do
    let mut a := Id.run (Id.run start)
    for i in [:(Id.run stop).toNat] do
      a := a + i.toUInt64 + 1
    return a
  value != Id.run (Id.run start)

def rangeBoolLetIdFlag (count seed : UInt64) : Bool :=
  let flag : Id Bool := seed % 3 == 0
  let value := Id.run do
    let mut a := seed
    for i in [:count.toNat] do
      a := a + i.toUInt64 + (Id.run flag).toUInt64
    return a
  Id.run flag && value == seed

def rangeBoolLetIdFlagLayers (count seed : UInt64) : Bool :=
  let flag : Id (Id Bool) := pure (pure (seed % 2 == 0))
  let start : Id UInt64 := seed + (Id.run (Id.run flag)).toUInt64
  let value := Id.run do
    let mut a := Id.run start
    for i in [:count.toNat] do
      if Id.run (Id.run flag) && i.toUInt64 % 3 == 0 then continue
      a := a + i.toUInt64 + 1
    return a
  Id.run (Id.run flag) || value == Id.run start

def rangeBoolLetIdResult (count seed : UInt64) : Bool :=
  let value : Id UInt64 := Id.run do
    let mut a := seed
    for i in [:count.toNat] do
      a := a + i.toUInt64 + 1
    return a
  Id.run value == seed

def rangeBoolLetIdResultLayers (count seed : UInt64) : Id Bool :=
  let value : Id (Id UInt64) := pure (pure (Id.run do
    let mut a := seed
    for i in [1:count.toNat:3] do
      a := a + i.toUInt64
      if a % 7 == 0 then break
    return a))
  pure (Id.run (Id.run value) % 7 == 0)

def rangeBoolLetIdMixed (count seed : UInt64) : Bool :=
  let start : Id UInt64 := seed + 3
  let flag : Id Bool := Id.run start % 2 == 0
  let value : Id UInt64 := Id.run do
    let mut a := Id.run start
    for i in [:count.toNat] do
      a := a + i.toUInt64 + (Id.run flag).toUInt64
    return a
  Id.run flag && Id.run value != Id.run start

def rangeBoolLetIdExit (count seed : UInt64) : Bool :=
  let flag : Id Bool := seed != 0
  let value : Id (Id UInt64) := Id.run do
    let mut a := seed
    for i in [:count.toNat] do
      a := a + i.toUInt64 + 1
      if Id.run flag && a % 7 == 0 then break
    return a
  Id.run flag || Id.run (Id.run value) == seed

def rangeBoolLetIdContinue (count seed : UInt64) : Bool := Id.run (
  let flag : Id Bool := seed % 3 == 0
  let value : Id UInt64 := Id.run do
    let mut a := seed
    for i in [:count.toNat] do
      if Id.run flag && i.toUInt64 % 2 == 0 then continue
      a := a + i.toUInt64 + 1
    return a
  pure (Id.run flag && Id.run value == seed))

def rangeBoolLetIdInput (count : Id UInt64) (input : Id Bool) : Id (Id Bool) :=
  let flag : Id (Id Bool) := pure (pure (!Id.run input))
  let start : Id UInt64 := (Id.run input).toUInt64
  let value : Id (Id UInt64) := Id.run do
    let mut a := Id.run start
    for i in [:(Id.run count).toNat] do
      a := a + i.toUInt64 + 1
      if Id.run (Id.run flag) && a % 7 == 0 then break
    return a
  pure (pure (Id.run (Id.run flag) && Id.run (Id.run value) == Id.run start))

def inputs : List (UInt64 × UInt64) :=
  [(0, 0), (1, 0), (0xffffffffffffffff, 0), (0, 1), (1, 1),
   (0xffffffffffffffff, 1), (0x8000000000000000, 2), (42, 3),
   (0xffffffffffffffff, 63), (0x8000000000000001, 64), (0xffffffffffffffff, 65),
   (0x0123456789abcdef, 0xffffffffffffffff), (3, 17), (17, 3)]

end BooleanLoopLetIdTest

run_elab do
  let env ← Lean.getEnv
  let cases : List (Lean.Name × (UInt64 → UInt64 → UInt64) × Bool) := [
    (`BooleanLoopLetIdTest.rangeBoolLetIdWord, (fun (x y : UInt64) => (BooleanLoopLetIdTest.rangeBoolLetIdWord x y).toUInt64), true),
    (`BooleanLoopLetIdTest.rangeBoolLetIdWordLayers, (fun (x y : UInt64) => (BooleanLoopLetIdTest.rangeBoolLetIdWordLayers x y).toUInt64), true),
    (`BooleanLoopLetIdTest.rangeBoolLetIdFlag, (fun (x y : UInt64) => (BooleanLoopLetIdTest.rangeBoolLetIdFlag x y).toUInt64), true),
    (`BooleanLoopLetIdTest.rangeBoolLetIdFlagLayers, (fun (x y : UInt64) => (BooleanLoopLetIdTest.rangeBoolLetIdFlagLayers x y).toUInt64), true),
    (`BooleanLoopLetIdTest.rangeBoolLetIdResult, (fun (x y : UInt64) => (BooleanLoopLetIdTest.rangeBoolLetIdResult x y).toUInt64), true),
    (`BooleanLoopLetIdTest.rangeBoolLetIdResultLayers, (fun (x y : UInt64) => (BooleanLoopLetIdTest.rangeBoolLetIdResultLayers x y).toUInt64), true),
    (`BooleanLoopLetIdTest.rangeBoolLetIdMixed, (fun (x y : UInt64) => (BooleanLoopLetIdTest.rangeBoolLetIdMixed x y).toUInt64), true),
    (`BooleanLoopLetIdTest.rangeBoolLetIdExit, (fun (x y : UInt64) => (BooleanLoopLetIdTest.rangeBoolLetIdExit x y).toUInt64), true),
    (`BooleanLoopLetIdTest.rangeBoolLetIdContinue, (fun (x y : UInt64) => (BooleanLoopLetIdTest.rangeBoolLetIdContinue x y).toUInt64), true),
    (`BooleanLoopLetIdTest.rangeBoolLetIdInput, (fun (x y : UInt64) => (BooleanLoopLetIdTest.rangeBoolLetIdInput x (y != 0)).toUInt64), true)]
  let mut comparisons : Nat := 0
  for (name, native, isRange) in cases do
    let some info := env.find? name | throwError "missing declaration"
    let some value := info.value? | throwError "missing body"
    let some func := LeanExe.Extract.Core.extractScalarFunc name (some "entry") info.type value |
      throwError "{name}: Boolean loop let-Id extraction failed"
    let module_ : LeanExe.IR.Module := { funcs := #[func] }
    let inputs := if isRange then
      ([0, 1, 2, 7, 16, 31] : List UInt64).flatMap fun n =>
        ([0, 1, 0x8000000000000000, 0xffffffffffffffff] : List UInt64).map fun seed => (n, seed)
      else BooleanLoopLetIdTest.inputs
    for (x, y) in inputs do
      let expected := native x y
      let actual := module_.evalFunc 0 [x, y]
      unless actual == expected do
        throwError "{name}({x}, {y}): native={expected}, IR={actual}"
      comparisons := comparisons + 1
  unless comparisons == 240 do throwError "unexpected comparison count {comparisons}"
  Lean.logInfo m!"{comparisons} native/Boolean loop let-Id IR comparisons passed"

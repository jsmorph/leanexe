import LeanExe.Extract.ScalarFunc

namespace BooleanLoopWordResultTest

def rangeWordFromBoolLet (count seed : UInt64) : UInt64 :=
  let flag :=
    let value := Id.run do
      let mut a := seed
      for i in [:count.toNat] do
        a := a + i.toUInt64 + 1
      return a
    value % 7 == seed % 7
  (if flag then seed + 7 else seed * 3) + count

def rangeWordFromBoolDo (count seed : UInt64) : Id UInt64 := do
  let flag ← (do
    let value ← (do
      let mut a := seed
      for i in [:count.toNat] do
        a := a + i.toUInt64 + 1
      return a)
    pure (value % 7 == seed % 7))
  pure ((if flag then seed + 7 else seed * 3) + count)

def rangeWordFromBoolFlag (count : UInt64) (flag : Bool) : UInt64 :=
  let selected :=
    let value := Id.run do
      let mut a := count
      for i in [:count.toNat] do
        a := a + i.toUInt64 + (if flag then 1 else 3)
      return a
    value != count
  if selected != flag then count + 11 else count * 5

def rangeWordFromBoolHelper (count seed : UInt64) : UInt64 :=
  let flag :=
    let value := Id.run do
      let mut a := seed
      for i in [:count.toNat] do
        a := a + i.toUInt64 + 1
      return a
    value != seed
  let f := fun b : Bool => if b then seed + 7 else count * 3
  f flag + f (!flag)

def rangeWordFromBoolConverted (count seed : UInt64) : UInt64 :=
  (let value := Id.run do
    let mut a := seed
    for i in [:count.toNat] do
      a := a + i.toUInt64 + 1
    return a
   value % 7 == seed % 7).toUInt64

def rangeWordFromBoolMixed (count seed : UInt64) : UInt64 :=
  let flag := if seed == 0 then count == 0 else
    let value := Id.run do
      let mut a := seed
      for i in [:count.toNat] do
        a := a + i.toUInt64 + 1
      return a
    value % 7 == 0
  if !flag && count != 0 then seed + 7 else seed * 3

def rangeWordFromBoolExit (count seed : UInt64) : UInt64 :=
  let flag :=
    let value := Id.run do
      let mut a := seed
      for i in [:count.toNat] do
        a := a + i.toUInt64 + 1
        if a % 7 == 0 then break
      return a
    value % 7 == 0
  if flag || count == 0 then seed + 5 else seed * 7

def rangeWordFromBoolContinue (count seed : UInt64) : Id UInt64 := do
  let flag ← (do
    let value ← (do
      let mut a := seed
      for i in [:count.toNat] do
        if i.toUInt64 % 2 == 0 then continue
        a := a + i.toUInt64 + 1
      return a)
    pure (value % 7 == seed % 7))
  pure ((if !flag || seed == 0 then seed + 11 else seed * 3) + count)

def rangeWordFromBoolStride (count seed : UInt64) : UInt64 :=
  let flag :=
    let value := Id.run do
      let mut a := seed
      for i in [(seed % 3).toNat:count.toNat:3] do
        a := a + i.toUInt64 + 1
        if a % 5 == 0 then break
      return a
    value % 5 == 0
  flag.toUInt64 * 23 + seed

def rangeWordFromBoolId (count seed : UInt64) : Id (Id UInt64) := do
  let flag : Id (Id Bool) ← (do
    let value ← (do
      let mut a := seed
      for i in [:count.toNat] do
        a := a + i.toUInt64 + 1
      return a)
    pure (pure (pure (value % 7 == seed % 7))))
  pure (pure ((if !(Id.run (Id.run flag)) && seed != 0 then seed + 7 else seed * 3) + count))

def inputs : List (UInt64 × UInt64) :=
  [(0, 0), (1, 0), (0xffffffffffffffff, 0), (0, 1), (1, 1),
   (0xffffffffffffffff, 1), (0x8000000000000000, 2), (42, 3),
   (0xffffffffffffffff, 63), (0x8000000000000001, 64), (0xffffffffffffffff, 65),
   (0x0123456789abcdef, 0xffffffffffffffff), (3, 17), (17, 3)]

end BooleanLoopWordResultTest

run_elab do
  let env ← Lean.getEnv
  let cases : List (Lean.Name × (UInt64 → UInt64 → UInt64) × Bool) := [
    (`BooleanLoopWordResultTest.rangeWordFromBoolLet, (fun (x y : UInt64) => BooleanLoopWordResultTest.rangeWordFromBoolLet x y), true),
    (`BooleanLoopWordResultTest.rangeWordFromBoolDo, (fun (x y : UInt64) => BooleanLoopWordResultTest.rangeWordFromBoolDo x y), true),
    (`BooleanLoopWordResultTest.rangeWordFromBoolFlag, (fun (x y : UInt64) => BooleanLoopWordResultTest.rangeWordFromBoolFlag x (y != 0)), true),
    (`BooleanLoopWordResultTest.rangeWordFromBoolHelper, (fun (x y : UInt64) => BooleanLoopWordResultTest.rangeWordFromBoolHelper x y), true),
    (`BooleanLoopWordResultTest.rangeWordFromBoolConverted, (fun (x y : UInt64) => BooleanLoopWordResultTest.rangeWordFromBoolConverted x y), true),
    (`BooleanLoopWordResultTest.rangeWordFromBoolMixed, (fun (x y : UInt64) => BooleanLoopWordResultTest.rangeWordFromBoolMixed x y), true),
    (`BooleanLoopWordResultTest.rangeWordFromBoolExit, (fun (x y : UInt64) => BooleanLoopWordResultTest.rangeWordFromBoolExit x y), true),
    (`BooleanLoopWordResultTest.rangeWordFromBoolContinue, (fun (x y : UInt64) => BooleanLoopWordResultTest.rangeWordFromBoolContinue x y), true),
    (`BooleanLoopWordResultTest.rangeWordFromBoolStride, (fun (x y : UInt64) => BooleanLoopWordResultTest.rangeWordFromBoolStride x y), true),
    (`BooleanLoopWordResultTest.rangeWordFromBoolId, (fun (x y : UInt64) => BooleanLoopWordResultTest.rangeWordFromBoolId x y), true)]
  let mut comparisons : Nat := 0
  for (name, native, isRange) in cases do
    let some info := env.find? name | throwError "missing declaration"
    let some value := info.value? | throwError "missing body"
    let some func := LeanExe.Extract.Core.extractScalarFunc name (some "entry") info.type value |
      throwError "{name}: Boolean loop word-result extraction failed"
    let module_ : LeanExe.IR.Module := { funcs := #[func] }
    let inputs := if isRange then
      ([0, 1, 2, 7, 16, 31] : List UInt64).flatMap fun n =>
        ([0, 1, 0x8000000000000000, 0xffffffffffffffff] : List UInt64).map fun seed => (n, seed)
      else BooleanLoopWordResultTest.inputs
    for (x, y) in inputs do
      let expected := native x y
      let actual := module_.evalFunc 0 [x, y]
      unless actual == expected do
        throwError "{name}({x}, {y}): native={expected}, IR={actual}"
      comparisons := comparisons + 1
  unless comparisons == 240 do throwError "unexpected comparison count {comparisons}"
  Lean.logInfo m!"{comparisons} native/Boolean loop word-result IR comparisons passed"

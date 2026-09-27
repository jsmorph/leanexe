import LeanExe.Extract.ScalarFunc

namespace PublicBooleanLoopResultsTest

def rangeBoolYield (count seed : UInt64) : Bool :=
  let value := Id.run do
    let mut a := seed
    for i in [:count.toNat] do
      a := a + i.toUInt64 + 1
    return a
  value == seed

def rangeBoolExit (count seed : UInt64) : Bool :=
  let value := Id.run do
    let mut a := seed
    for i in [:count.toNat] do
      a := a + i.toUInt64 + 1
      if a % 7 == 0 then break
    return a
  value % 7 == 0

def rangeBoolContinue (count seed : UInt64) : Bool :=
  let value := Id.run do
    let mut a := seed
    for i in [:count.toNat] do
      if i.toUInt64 % 3 == 0 then continue
      a := a + i.toUInt64
    return a
  value != seed && value != 0

def rangeBoolStride (count seed : UInt64) : Bool :=
  let value := Id.run do
    let mut a := seed
    for i in [1:count.toNat:3] do
      a := a + i.toUInt64
      if a % 5 == 0 then break
    return a
  decide (value ≤ seed)

def rangeBoolStepHelper (count seed : UInt64) : Bool :=
  let value := Id.run do
    let mut a := seed
    for i in [:count.toNat] do
      let f := fun x : UInt64 => x + i.toUInt64 + seed
      a := f a
      if a % 11 == 0 then break
    return a
  value == 0 || value == seed

def rangeBoolCapture (count seed : UInt64) : Bool :=
  let value := Id.run do
    let f := fun b : Bool => if b then seed + 7 else seed + 3
    let mut a := f false
    for i in [:count.toNat] do
      a := a + f (i.toUInt64 % 2 == 0)
    return a
  let f := fun x : UInt64 => x == seed
  f value

def rangeBoolFlag (count : UInt64) (flag : Bool) : Bool :=
  let value := Id.run do
    let mut a := flag.toUInt64
    for i in [:count.toNat] do
      if flag && i.toUInt64 % 3 == 0 then continue
      a := a + i.toUInt64 + 1
    return a
  flag && value != 0

def rangeBoolIdInputs (count : Id UInt64) (flag : Id Bool) : Bool :=
  let value := Id.run do
    let mut a := (Id.run flag).toUInt64
    for i in [:(Id.run count).toNat] do
      a := a + i.toUInt64 + 1
      if Id.run flag && a % 7 == 0 then break
    return a
  Id.run flag || value == 0

def rangeBoolPure (count seed : UInt64) : Id Bool :=
  pure (
    let value := Id.run do
      let mut a := seed
      for i in [:count.toNat] do
        a := a + i.toUInt64 + 1
      return a
    value != seed)

def rangeBoolRun (count seed : UInt64) : Bool := Id.run (
  let value := Id.run do
    let mut a := seed
    for i in [:count.toNat] do
      a := a + i.toUInt64 + 1
      if a % 5 == 0 then break
    return a
  pure (value == seed))

def inputs : List (UInt64 × UInt64) :=
  [(0, 0), (1, 0), (0xffffffffffffffff, 0), (0, 1), (1, 1),
   (0xffffffffffffffff, 1), (0x8000000000000000, 2), (42, 3),
   (0xffffffffffffffff, 63), (0x8000000000000001, 64), (0xffffffffffffffff, 65),
   (0x0123456789abcdef, 0xffffffffffffffff), (3, 17), (17, 3)]

end PublicBooleanLoopResultsTest

run_elab do
  let env ← Lean.getEnv
  let cases : List (Lean.Name × (UInt64 → UInt64 → UInt64) × Bool) := [
    (`PublicBooleanLoopResultsTest.rangeBoolYield, (fun (x y : UInt64) => (PublicBooleanLoopResultsTest.rangeBoolYield x y).toUInt64), true),
    (`PublicBooleanLoopResultsTest.rangeBoolExit, (fun (x y : UInt64) => (PublicBooleanLoopResultsTest.rangeBoolExit x y).toUInt64), true),
    (`PublicBooleanLoopResultsTest.rangeBoolContinue, (fun (x y : UInt64) => (PublicBooleanLoopResultsTest.rangeBoolContinue x y).toUInt64), true),
    (`PublicBooleanLoopResultsTest.rangeBoolStride, (fun (x y : UInt64) => (PublicBooleanLoopResultsTest.rangeBoolStride x y).toUInt64), true),
    (`PublicBooleanLoopResultsTest.rangeBoolStepHelper, (fun (x y : UInt64) => (PublicBooleanLoopResultsTest.rangeBoolStepHelper x y).toUInt64), true),
    (`PublicBooleanLoopResultsTest.rangeBoolCapture, (fun (x y : UInt64) => (PublicBooleanLoopResultsTest.rangeBoolCapture x y).toUInt64), true),
    (`PublicBooleanLoopResultsTest.rangeBoolFlag, (fun (x y : UInt64) => (PublicBooleanLoopResultsTest.rangeBoolFlag x (y != 0)).toUInt64), true),
    (`PublicBooleanLoopResultsTest.rangeBoolIdInputs, (fun (x y : UInt64) => (PublicBooleanLoopResultsTest.rangeBoolIdInputs x (y != 0)).toUInt64), true),
    (`PublicBooleanLoopResultsTest.rangeBoolPure, (fun (x y : UInt64) => (PublicBooleanLoopResultsTest.rangeBoolPure x y).toUInt64), true),
    (`PublicBooleanLoopResultsTest.rangeBoolRun, (fun (x y : UInt64) => (PublicBooleanLoopResultsTest.rangeBoolRun x y).toUInt64), true)]
  let mut comparisons : Nat := 0
  for (name, native, isRange) in cases do
    let some info := env.find? name | throwError "missing declaration"
    let some value := info.value? | throwError "missing body"
    let some func := LeanExe.Extract.Core.extractScalarFunc name (some "entry") info.type value |
      throwError "{name}: Boolean loop-result extraction failed"
    let module_ : LeanExe.IR.Module := { funcs := #[func] }
    let inputs := if isRange then
      ([0, 1, 2, 7, 16, 31] : List UInt64).flatMap fun n =>
        ([0, 1, 0x8000000000000000, 0xffffffffffffffff] : List UInt64).map fun seed => (n, seed)
      else PublicBooleanLoopResultsTest.inputs
    for (x, y) in inputs do
      let expected := native x y
      let actual := module_.evalFunc 0 [x, y]
      unless actual == expected do
        throwError "{name}({x}, {y}): native={expected}, IR={actual}"
      comparisons := comparisons + 1
  unless comparisons == 240 do throwError "unexpected comparison count {comparisons}"
  Lean.logInfo m!"{comparisons} native/public Boolean loop-result IR comparisons passed"

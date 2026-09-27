import LeanExe.Extract.ScalarFunc

namespace BooleanLoopBindTest

def rangeBoolResultBindYield (count seed : UInt64) : Id Bool := do
  let value ← (do
    let mut a := seed
    for i in [:count.toNat] do
      a := a + i.toUInt64 + 1
    return a)
  return value == seed

def rangeBoolResultBindExit (count seed : UInt64) : Id Bool := do
  let value ← (do
    let mut a := seed
    for i in [:count.toNat] do
      a := a + i.toUInt64 + 1
      if a % 7 == 0 then break
    return a)
  return value % 7 == 0

def rangeBoolResultBindContinue (count seed : UInt64) : Id Bool := do
  let value ← (do
    let mut a := seed
    for i in [:count.toNat] do
      if i.toUInt64 % 3 == 0 then continue
      a := a + i.toUInt64
    return a)
  return value != seed && value != 0

def rangeBoolResultBindStride (count seed : UInt64) : Id Bool := do
  let value ← (do
    let mut a := seed
    for i in [1:count.toNat:3] do
      a := a + i.toUInt64
      if a % 5 == 0 then break
    return a)
  return decide (value ≤ seed)

def rangeBoolResultBindStepHelper (count seed : UInt64) : Id Bool := do
  let value ← (do
    let mut a := seed
    for i in [:count.toNat] do
      let f := fun x : UInt64 => x + i.toUInt64 + seed
      a := f a
      if a % 11 == 0 then break
    return a)
  return value == 0 || value == seed

def rangeBoolResultBindCapture (count seed : UInt64) : Id Bool := do
  let value ← (do
    let f := fun b : Bool => if b then seed + 7 else seed + 3
    let mut a := f false
    for i in [:count.toNat] do
      a := a + f (i.toUInt64 % 2 == 0)
    return a)
  return value == seed || value == seed + 3

def rangeBoolResultBindFlag (count : UInt64) (flag : Bool) : Id Bool := do
  let value ← (do
    let mut a := flag.toUInt64
    for i in [:count.toNat] do
      if flag && i.toUInt64 % 3 == 0 then continue
      a := a + i.toUInt64 + 1
    return a)
  return flag && value != 0

def rangeBoolResultBindIdInputs (count : Id UInt64) (flag : Id Bool) : Id Bool := do
  let value ← (do
    let mut a := (Id.run flag).toUInt64
    for i in [:(Id.run count).toNat] do
      a := a + i.toUInt64 + 1
      if Id.run flag && a % 7 == 0 then break
    return a)
  return Id.run flag || value == 0

def rangeBoolResultBindIdAction (count seed : UInt64) : Id Bool := do
  let value : Id UInt64 ← pure (Id.run do
    let mut a := seed
    for i in [:count.toNat] do
      a := a + i.toUInt64 + 1
      if a % 7 == 0 then break
    return a)
  return Id.run value != seed

def rangeBoolResultBindNestedResult (count seed : UInt64) : Id (Id Bool) := do
  let value ← (do
    let mut a := seed
    for i in [:count.toNat] do
      if i.toUInt64 % 2 == 0 then continue
      a := a + i.toUInt64 + 1
    return a)
  return pure (value == seed)

def inputs : List (UInt64 × UInt64) :=
  [(0, 0), (1, 0), (0xffffffffffffffff, 0), (0, 1), (1, 1),
   (0xffffffffffffffff, 1), (0x8000000000000000, 2), (42, 3),
   (0xffffffffffffffff, 63), (0x8000000000000001, 64), (0xffffffffffffffff, 65),
   (0x0123456789abcdef, 0xffffffffffffffff), (3, 17), (17, 3)]

end BooleanLoopBindTest

run_elab do
  let env ← Lean.getEnv
  let cases : List (Lean.Name × (UInt64 → UInt64 → UInt64) × Bool) := [
    (`BooleanLoopBindTest.rangeBoolResultBindYield, (fun (x y : UInt64) => (BooleanLoopBindTest.rangeBoolResultBindYield x y).toUInt64), true),
    (`BooleanLoopBindTest.rangeBoolResultBindExit, (fun (x y : UInt64) => (BooleanLoopBindTest.rangeBoolResultBindExit x y).toUInt64), true),
    (`BooleanLoopBindTest.rangeBoolResultBindContinue, (fun (x y : UInt64) => (BooleanLoopBindTest.rangeBoolResultBindContinue x y).toUInt64), true),
    (`BooleanLoopBindTest.rangeBoolResultBindStride, (fun (x y : UInt64) => (BooleanLoopBindTest.rangeBoolResultBindStride x y).toUInt64), true),
    (`BooleanLoopBindTest.rangeBoolResultBindStepHelper, (fun (x y : UInt64) => (BooleanLoopBindTest.rangeBoolResultBindStepHelper x y).toUInt64), true),
    (`BooleanLoopBindTest.rangeBoolResultBindCapture, (fun (x y : UInt64) => (BooleanLoopBindTest.rangeBoolResultBindCapture x y).toUInt64), true),
    (`BooleanLoopBindTest.rangeBoolResultBindFlag, (fun (x y : UInt64) => (BooleanLoopBindTest.rangeBoolResultBindFlag x (y != 0)).toUInt64), true),
    (`BooleanLoopBindTest.rangeBoolResultBindIdInputs, (fun (x y : UInt64) => (BooleanLoopBindTest.rangeBoolResultBindIdInputs x (y != 0)).toUInt64), true),
    (`BooleanLoopBindTest.rangeBoolResultBindIdAction, (fun (x y : UInt64) => (BooleanLoopBindTest.rangeBoolResultBindIdAction x y).toUInt64), true),
    (`BooleanLoopBindTest.rangeBoolResultBindNestedResult, (fun (x y : UInt64) => (BooleanLoopBindTest.rangeBoolResultBindNestedResult x y).toUInt64), true)]
  let mut comparisons : Nat := 0
  for (name, native, isRange) in cases do
    let some info := env.find? name | throwError "missing declaration"
    let some value := info.value? | throwError "missing body"
    let some func := LeanExe.Extract.Core.extractScalarFunc name (some "entry") info.type value |
      throwError "{name}: Boolean loop-bind extraction failed"
    let module_ : LeanExe.IR.Module := { funcs := #[func] }
    let inputs := if isRange then
      ([0, 1, 2, 7, 16, 31] : List UInt64).flatMap fun n =>
        ([0, 1, 0x8000000000000000, 0xffffffffffffffff] : List UInt64).map fun seed => (n, seed)
      else BooleanLoopBindTest.inputs
    for (x, y) in inputs do
      let expected := native x y
      let actual := module_.evalFunc 0 [x, y]
      unless actual == expected do
        throwError "{name}({x}, {y}): native={expected}, IR={actual}"
      comparisons := comparisons + 1
  unless comparisons == 240 do throwError "unexpected comparison count {comparisons}"
  Lean.logInfo m!"{comparisons} native/Boolean loop-bind IR comparisons passed"

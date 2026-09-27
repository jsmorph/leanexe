import LeanExe.Extract.ScalarFunc

namespace BooleanLoopFlagSetupTest

def rangeBoolFlagSetupLet (count seed : UInt64) : Bool :=
  let flag := seed % 3 == 0
  let value := Id.run do
    let mut a := seed
    for i in [:count.toNat] do
      a := a + i.toUInt64 + flag.toUInt64
    return a
  flag && value == seed

def rangeBoolFlagSetupChain (count seed : UInt64) : Bool :=
  let first := seed % 3 == 0
  let second := !first || count == 0
  let start := seed + second.toUInt64
  let value := Id.run do
    let mut a := start
    for i in [:count.toNat] do
      a := a + i.toUInt64 + first.toUInt64
    return a
  second && value == start

def rangeBoolFlagSetupBind (count seed : UInt64) : Id Bool := do
  let flag ← pure (seed != 0)
  let value ← (do
    let mut a := seed
    for i in [:count.toNat] do
      a := a + i.toUInt64 + flag.toUInt64
    return a)
  return flag || value == seed

def rangeBoolFlagSetupCondition (count seed : UInt64) : Id Bool := do
  let flag ← pure (if count == 0 then seed == 0 else seed % 2 == 0)
  let value ← (do
    let mut a := seed
    for i in [:count.toNat] do
      if flag then a := a + i.toUInt64 + 1 else a := a + 3
    return a)
  return flag && value != seed

def rangeBoolFlagSetupExit (count seed : UInt64) : Id Bool := do
  let flag ← pure (seed % 2 != 0)
  let value ← (do
    let mut a := seed
    for i in [:count.toNat] do
      a := a + i.toUInt64 + 1
      if flag && a % 7 == 0 then break
    return a)
  return flag || value == 0

def rangeBoolFlagSetupContinue (count seed : UInt64) : Bool := Id.run do
  let flag := seed % 3 == 0
  let value ← (do
    let mut a := seed
    for i in [:count.toNat] do
      if flag && i.toUInt64 % 3 == 0 then continue
      a := a + i.toUInt64 + 1
    return a)
  return flag && value == seed

def rangeBoolFlagSetupStride (count seed : UInt64) : Bool :=
  let flag := seed % 2 == 0
  let value := Id.run do
    let mut a := seed
    for i in [1:count.toNat:3] do
      a := a + i.toUInt64 + flag.toUInt64
      if a % 5 == 0 then break
    return a
  flag && decide (value ≤ seed)

def rangeBoolFlagSetupCapture (count seed : UInt64) : Id Bool := do
  let flag ← pure (seed % 7 == 0)
  let value ← (do
    let f := fun b : Bool => if b && flag then seed + 7 else seed + 3
    let mut a := f false
    for i in [:count.toNat] do
      a := a + f (i.toUInt64 % 2 == 0)
    return a)
  return flag || value == seed

def rangeBoolFlagSetupInput (count : UInt64) (input : Bool) : Bool :=
  let flag := !input || count == 0
  let value := Id.run do
    let mut a := input.toUInt64
    for i in [:count.toNat] do
      if flag && i.toUInt64 % 3 == 0 then continue
      a := a + i.toUInt64 + 1
    return a
  flag && value == input.toUInt64

def rangeBoolFlagSetupId (count : UInt64) (input : Id Bool) : Id (Id Bool) := do
  let flag : Id Bool ← pure (pure (!Id.run input || count == 0))
  let value ← (do
    let mut a := (Id.run input).toUInt64
    for i in [:count.toNat] do
      a := a + i.toUInt64 + 1
      if Id.run flag && a % 7 == 0 then break
    return a)
  return pure (Id.run flag && value == (Id.run input).toUInt64)

def inputs : List (UInt64 × UInt64) :=
  [(0, 0), (1, 0), (0xffffffffffffffff, 0), (0, 1), (1, 1),
   (0xffffffffffffffff, 1), (0x8000000000000000, 2), (42, 3),
   (0xffffffffffffffff, 63), (0x8000000000000001, 64), (0xffffffffffffffff, 65),
   (0x0123456789abcdef, 0xffffffffffffffff), (3, 17), (17, 3)]

end BooleanLoopFlagSetupTest

run_elab do
  let env ← Lean.getEnv
  let cases : List (Lean.Name × (UInt64 → UInt64 → UInt64) × Bool) := [
    (`BooleanLoopFlagSetupTest.rangeBoolFlagSetupLet, (fun (x y : UInt64) => (BooleanLoopFlagSetupTest.rangeBoolFlagSetupLet x y).toUInt64), true),
    (`BooleanLoopFlagSetupTest.rangeBoolFlagSetupChain, (fun (x y : UInt64) => (BooleanLoopFlagSetupTest.rangeBoolFlagSetupChain x y).toUInt64), true),
    (`BooleanLoopFlagSetupTest.rangeBoolFlagSetupBind, (fun (x y : UInt64) => (BooleanLoopFlagSetupTest.rangeBoolFlagSetupBind x y).toUInt64), true),
    (`BooleanLoopFlagSetupTest.rangeBoolFlagSetupCondition, (fun (x y : UInt64) => (BooleanLoopFlagSetupTest.rangeBoolFlagSetupCondition x y).toUInt64), true),
    (`BooleanLoopFlagSetupTest.rangeBoolFlagSetupExit, (fun (x y : UInt64) => (BooleanLoopFlagSetupTest.rangeBoolFlagSetupExit x y).toUInt64), true),
    (`BooleanLoopFlagSetupTest.rangeBoolFlagSetupContinue, (fun (x y : UInt64) => (BooleanLoopFlagSetupTest.rangeBoolFlagSetupContinue x y).toUInt64), true),
    (`BooleanLoopFlagSetupTest.rangeBoolFlagSetupStride, (fun (x y : UInt64) => (BooleanLoopFlagSetupTest.rangeBoolFlagSetupStride x y).toUInt64), true),
    (`BooleanLoopFlagSetupTest.rangeBoolFlagSetupCapture, (fun (x y : UInt64) => (BooleanLoopFlagSetupTest.rangeBoolFlagSetupCapture x y).toUInt64), true),
    (`BooleanLoopFlagSetupTest.rangeBoolFlagSetupInput, (fun (x y : UInt64) => (BooleanLoopFlagSetupTest.rangeBoolFlagSetupInput x (y != 0)).toUInt64), true),
    (`BooleanLoopFlagSetupTest.rangeBoolFlagSetupId, (fun (x y : UInt64) => (BooleanLoopFlagSetupTest.rangeBoolFlagSetupId x (y != 0)).toUInt64), true)]
  let mut comparisons : Nat := 0
  for (name, native, isRange) in cases do
    let some info := env.find? name | throwError "missing declaration"
    let some value := info.value? | throwError "missing body"
    let some func := LeanExe.Extract.Core.extractScalarFunc name (some "entry") info.type value |
      throwError "{name}: Boolean loop flag-setup extraction failed"
    let module_ : LeanExe.IR.Module := { funcs := #[func] }
    let inputs := if isRange then
      ([0, 1, 2, 7, 16, 31] : List UInt64).flatMap fun n =>
        ([0, 1, 0x8000000000000000, 0xffffffffffffffff] : List UInt64).map fun seed => (n, seed)
      else BooleanLoopFlagSetupTest.inputs
    for (x, y) in inputs do
      let expected := native x y
      let actual := module_.evalFunc 0 [x, y]
      unless actual == expected do
        throwError "{name}({x}, {y}): native={expected}, IR={actual}"
      comparisons := comparisons + 1
  unless comparisons == 240 do throwError "unexpected comparison count {comparisons}"
  Lean.logInfo m!"{comparisons} native/Boolean loop flag-setup IR comparisons passed"

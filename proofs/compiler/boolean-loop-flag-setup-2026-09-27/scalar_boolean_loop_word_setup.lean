import LeanExe.Extract.ScalarFunc

namespace BooleanLoopWordSetupTest

def rangeBoolWordSetupLet (count seed : UInt64) : Bool :=
  let start := seed + 7
  let value := Id.run do
    let mut a := start
    for i in [:count.toNat] do
      a := a + i.toUInt64 + 1
    return a
  value == start

def rangeBoolWordSetupChain (count seed : UInt64) : Bool :=
  let start := seed + 7
  let stop := count % 17
  let delta := seed % 5 + 1
  let value := Id.run do
    let mut a := start
    for i in [:stop.toNat] do
      a := a + i.toUInt64 + delta
    return a
  value == start || value == seed

def rangeBoolWordSetupBind (count seed : UInt64) : Id Bool := do
  let start ← pure (seed + 3)
  let stop ← pure (count % 17)
  let value ← (do
    let mut a := start
    for i in [:stop.toNat] do
      a := a + i.toUInt64 + 1
    return a)
  return value != start

def rangeBoolWordSetupCount (count seed : UInt64) : Bool :=
  let stop := count % 17
  let value := Id.run do
    let mut a := seed
    for i in [:stop.toNat] do
      a := a + i.toUInt64 + stop
    return a
  value == seed + stop

def rangeBoolWordSetupExit (count seed : UInt64) : Id Bool := do
  let delta ← pure (seed % 7 + 1)
  let value ← (do
    let mut a := seed
    for i in [:count.toNat] do
      a := a + i.toUInt64 + delta
      if a % 7 == 0 then break
    return a)
  return value % 7 == 0

def rangeBoolWordSetupContinue (count seed : UInt64) : Bool := Id.run do
  let offset := seed % 3
  let start := seed + offset
  let value ← (do
    let mut a := start
    for i in [:count.toNat] do
      if i.toUInt64 % 3 == offset then continue
      a := a + i.toUInt64 + 1
    return a)
  return value == start

def rangeBoolWordSetupStride (count seed : UInt64) : Bool :=
  let start := seed % 3
  let value := Id.run do
    let mut a := seed
    for i in [start.toNat:count.toNat:3] do
      a := a + i.toUInt64 + 1
      if a % 5 == 0 then break
    return a
  decide (value ≤ seed)

def rangeBoolWordSetupCapture (count seed : UInt64) : Id Bool := do
  let captured ← pure (seed + 7)
  let value ← (do
    let f := fun x : UInt64 => x + captured
    let mut a := f seed
    for i in [:count.toNat] do
      a := f (a + i.toUInt64)
    return a)
  return value == captured || value == seed

def rangeBoolWordSetupFlag (count : UInt64) (flag : Bool) : Bool :=
  let start := count + flag.toUInt64
  let value := Id.run do
    let mut a := start
    for i in [:count.toNat] do
      if flag && i.toUInt64 % 3 == 0 then continue
      a := a + i.toUInt64 + 1
    return a
  flag && value != start

def rangeBoolWordSetupId (count : Id UInt64) (seed : UInt64) : Id (Id Bool) := do
  let start : Id UInt64 ← pure (pure (seed + 1))
  let value ← (do
    let mut a := Id.run start
    for i in [:(Id.run count).toNat] do
      a := a + i.toUInt64 + 1
      if a % 7 == 0 then break
    return a)
  return pure (value == Id.run start)

def inputs : List (UInt64 × UInt64) :=
  [(0, 0), (1, 0), (0xffffffffffffffff, 0), (0, 1), (1, 1),
   (0xffffffffffffffff, 1), (0x8000000000000000, 2), (42, 3),
   (0xffffffffffffffff, 63), (0x8000000000000001, 64), (0xffffffffffffffff, 65),
   (0x0123456789abcdef, 0xffffffffffffffff), (3, 17), (17, 3)]

end BooleanLoopWordSetupTest

run_elab do
  let env ← Lean.getEnv
  let cases : List (Lean.Name × (UInt64 → UInt64 → UInt64) × Bool) := [
    (`BooleanLoopWordSetupTest.rangeBoolWordSetupLet, (fun (x y : UInt64) => (BooleanLoopWordSetupTest.rangeBoolWordSetupLet x y).toUInt64), true),
    (`BooleanLoopWordSetupTest.rangeBoolWordSetupChain, (fun (x y : UInt64) => (BooleanLoopWordSetupTest.rangeBoolWordSetupChain x y).toUInt64), true),
    (`BooleanLoopWordSetupTest.rangeBoolWordSetupBind, (fun (x y : UInt64) => (BooleanLoopWordSetupTest.rangeBoolWordSetupBind x y).toUInt64), true),
    (`BooleanLoopWordSetupTest.rangeBoolWordSetupCount, (fun (x y : UInt64) => (BooleanLoopWordSetupTest.rangeBoolWordSetupCount x y).toUInt64), true),
    (`BooleanLoopWordSetupTest.rangeBoolWordSetupExit, (fun (x y : UInt64) => (BooleanLoopWordSetupTest.rangeBoolWordSetupExit x y).toUInt64), true),
    (`BooleanLoopWordSetupTest.rangeBoolWordSetupContinue, (fun (x y : UInt64) => (BooleanLoopWordSetupTest.rangeBoolWordSetupContinue x y).toUInt64), true),
    (`BooleanLoopWordSetupTest.rangeBoolWordSetupStride, (fun (x y : UInt64) => (BooleanLoopWordSetupTest.rangeBoolWordSetupStride x y).toUInt64), true),
    (`BooleanLoopWordSetupTest.rangeBoolWordSetupCapture, (fun (x y : UInt64) => (BooleanLoopWordSetupTest.rangeBoolWordSetupCapture x y).toUInt64), true),
    (`BooleanLoopWordSetupTest.rangeBoolWordSetupFlag, (fun (x y : UInt64) => (BooleanLoopWordSetupTest.rangeBoolWordSetupFlag x (y != 0)).toUInt64), true),
    (`BooleanLoopWordSetupTest.rangeBoolWordSetupId, (fun (x y : UInt64) => (BooleanLoopWordSetupTest.rangeBoolWordSetupId x y).toUInt64), true)]
  let mut comparisons : Nat := 0
  for (name, native, isRange) in cases do
    let some info := env.find? name | throwError "missing declaration"
    let some value := info.value? | throwError "missing body"
    let some func := LeanExe.Extract.Core.extractScalarFunc name (some "entry") info.type value |
      throwError "{name}: Boolean loop word-setup extraction failed"
    let module_ : LeanExe.IR.Module := { funcs := #[func] }
    let inputs := if isRange then
      ([0, 1, 2, 7, 16, 31] : List UInt64).flatMap fun n =>
        ([0, 1, 0x8000000000000000, 0xffffffffffffffff] : List UInt64).map fun seed => (n, seed)
      else BooleanLoopWordSetupTest.inputs
    for (x, y) in inputs do
      let expected := native x y
      let actual := module_.evalFunc 0 [x, y]
      unless actual == expected do
        throwError "{name}({x}, {y}): native={expected}, IR={actual}"
      comparisons := comparisons + 1
  unless comparisons == 240 do throwError "unexpected comparison count {comparisons}"
  Lean.logInfo m!"{comparisons} native/Boolean loop word-setup IR comparisons passed"

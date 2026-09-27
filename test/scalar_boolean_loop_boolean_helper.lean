import LeanExe.Extract.ScalarFunc

namespace BooleanLoopBooleanHelperTest

def rangeBoolBooleanHelperRepeat (count seed : UInt64) : Bool :=
  let f := fun flag : Bool => seed + flag.toUInt64 + 1
  let value := Id.run do
    let mut a := f true
    for i in [:count.toNat] do
      a := a + f (i.toUInt64 % 2 == 0) + f false
    return a
  value == f true

def rangeBoolBooleanHelperCount (count seed : UInt64) : Bool :=
  let limit := fun flag : Bool => if flag then count % 17 else count % 5
  let value := Id.run do
    let mut a := seed
    for i in [:(limit (seed % 2 == 0)).toNat] do
      a := a + i.toUInt64 + 1
    return a
  value == seed + limit true

def rangeBoolBooleanHelperInitial (count seed : UInt64) : Bool :=
  let f := fun flag : Bool => seed * 3 + flag.toUInt64
  let value := Id.run do
    let mut a := f false
    for i in [:count.toNat] do
      a := a + f (i.toUInt64 % 2 == 0)
    return a
  value == f false

def rangeBoolBooleanHelperNested (count seed : UInt64) : Id Bool :=
  let f := fun flag : Bool => seed + flag.toUInt64
  let g := fun flag : Bool => f (!flag) + f flag
  let value := Id.run do
    let mut a := g false
    for i in [:count.toNat] do
      a := a + g (i.toUInt64 % 3 == 0)
    return a
  pure (value == g (seed == 0))

def rangeBoolBooleanHelperFlag (count : UInt64) (flag : Bool) : Bool :=
  let f := fun input : Bool => if flag && input then count + 7 else count - 3
  let value := Id.run do
    let mut a := f flag
    for i in [:count.toNat] do
      a := a + f (i.toUInt64 % 2 == 0)
    return a
  flag && value == f flag

def rangeBoolBooleanHelperExit (count seed : UInt64) : Bool :=
  let f := fun flag : Bool => seed % 5 + flag.toUInt64 + 1
  let value := Id.run do
    let mut a := seed
    for i in [:count.toNat] do
      a := a + f (i.toUInt64 % 2 == 0)
      if a % 7 == 0 then break
    return a
  f (value % 7 == 0) == f true

def rangeBoolBooleanHelperContinue (count seed : UInt64) : Bool :=
  let f := fun flag : Bool => if flag then 0 else seed % 3 + 1
  let value := Id.run do
    let mut a := seed
    for i in [:count.toNat] do
      if f (i.toUInt64 % 2 == 0) == 0 then continue
      a := a + i.toUInt64 + 1
    return a
  f (value == seed) == f true

def rangeBoolBooleanHelperStride (count seed : UInt64) : Bool :=
  let f := fun flag : Bool => if flag then seed % 3 else 0
  let value := Id.run do
    let mut a := seed
    for i in [(f true).toNat:count.toNat:3] do
      a := a + i.toUInt64 + 1
      if a % 5 == 0 then break
    return a
  f (value == seed) == f true

def rangeBoolBooleanHelperId (count : Id UInt64) (seed : UInt64) : Id Bool :=
  let f (flag : Bool) : Id (Id UInt64) := pure (pure (seed + flag.toUInt64 + 1))
  let value : Id UInt64 := Id.run do
    let mut a := Id.run (Id.run (f false))
    for i in [:(Id.run count).toNat] do
      a := a + Id.run (Id.run (f (i.toUInt64 % 2 == 0)))
    return a
  pure (Id.run value == Id.run (Id.run (f false)))

def rangeBoolBooleanHelperShadow (count seed : UInt64) : Bool :=
  let f := fun flag : Bool => seed + flag.toUInt64
  let initial := f false
  let f := fun flag : Bool => f (!flag) + count
  let value := Id.run do
    let mut a := initial
    for i in [:count.toNat] do
      a := a + f (i.toUInt64 % 2 == 0)
    return a
  value == f (initial == seed)

def inputs : List (UInt64 × UInt64) :=
  [(0, 0), (1, 0), (0xffffffffffffffff, 0), (0, 1), (1, 1),
   (0xffffffffffffffff, 1), (0x8000000000000000, 2), (42, 3),
   (0xffffffffffffffff, 63), (0x8000000000000001, 64), (0xffffffffffffffff, 65),
   (0x0123456789abcdef, 0xffffffffffffffff), (3, 17), (17, 3)]

end BooleanLoopBooleanHelperTest

run_elab do
  let env ← Lean.getEnv
  let cases : List (Lean.Name × (UInt64 → UInt64 → UInt64) × Bool) := [
    (`BooleanLoopBooleanHelperTest.rangeBoolBooleanHelperRepeat, (fun (x y : UInt64) => (BooleanLoopBooleanHelperTest.rangeBoolBooleanHelperRepeat x y).toUInt64), true),
    (`BooleanLoopBooleanHelperTest.rangeBoolBooleanHelperCount, (fun (x y : UInt64) => (BooleanLoopBooleanHelperTest.rangeBoolBooleanHelperCount x y).toUInt64), true),
    (`BooleanLoopBooleanHelperTest.rangeBoolBooleanHelperInitial, (fun (x y : UInt64) => (BooleanLoopBooleanHelperTest.rangeBoolBooleanHelperInitial x y).toUInt64), true),
    (`BooleanLoopBooleanHelperTest.rangeBoolBooleanHelperNested, (fun (x y : UInt64) => (BooleanLoopBooleanHelperTest.rangeBoolBooleanHelperNested x y).toUInt64), true),
    (`BooleanLoopBooleanHelperTest.rangeBoolBooleanHelperFlag, (fun (x y : UInt64) => (BooleanLoopBooleanHelperTest.rangeBoolBooleanHelperFlag x (y != 0)).toUInt64), true),
    (`BooleanLoopBooleanHelperTest.rangeBoolBooleanHelperExit, (fun (x y : UInt64) => (BooleanLoopBooleanHelperTest.rangeBoolBooleanHelperExit x y).toUInt64), true),
    (`BooleanLoopBooleanHelperTest.rangeBoolBooleanHelperContinue, (fun (x y : UInt64) => (BooleanLoopBooleanHelperTest.rangeBoolBooleanHelperContinue x y).toUInt64), true),
    (`BooleanLoopBooleanHelperTest.rangeBoolBooleanHelperStride, (fun (x y : UInt64) => (BooleanLoopBooleanHelperTest.rangeBoolBooleanHelperStride x y).toUInt64), true),
    (`BooleanLoopBooleanHelperTest.rangeBoolBooleanHelperId, (fun (x y : UInt64) => (BooleanLoopBooleanHelperTest.rangeBoolBooleanHelperId x y).toUInt64), true),
    (`BooleanLoopBooleanHelperTest.rangeBoolBooleanHelperShadow, (fun (x y : UInt64) => (BooleanLoopBooleanHelperTest.rangeBoolBooleanHelperShadow x y).toUInt64), true)]
  let mut comparisons : Nat := 0
  for (name, native, isRange) in cases do
    let some info := env.find? name | throwError "missing declaration"
    let some value := info.value? | throwError "missing body"
    let some func := LeanExe.Extract.Core.extractScalarFunc name (some "entry") info.type value |
      throwError "{name}: Boolean loop boolean-helper extraction failed"
    let module_ : LeanExe.IR.Module := { funcs := #[func] }
    let inputs := if isRange then
      ([0, 1, 2, 7, 16, 31] : List UInt64).flatMap fun n =>
        ([0, 1, 0x8000000000000000, 0xffffffffffffffff] : List UInt64).map fun seed => (n, seed)
      else BooleanLoopBooleanHelperTest.inputs
    for (x, y) in inputs do
      let expected := native x y
      let actual := module_.evalFunc 0 [x, y]
      unless actual == expected do
        throwError "{name}({x}, {y}): native={expected}, IR={actual}"
      comparisons := comparisons + 1
  unless comparisons == 240 do throwError "unexpected comparison count {comparisons}"
  Lean.logInfo m!"{comparisons} native/Boolean loop boolean-helper IR comparisons passed"

import LeanExe.Extract.ScalarFunc

namespace BooleanLoopPredicateHelpersTest

def rangeBoolPredicateHelperRepeat (count seed : UInt64) : Bool :=
  let f := fun x : UInt64 => x % 2 == seed % 2
  let value := Id.run do
    let mut a := seed
    for i in [:count.toNat] do
      a := a + (f i.toUInt64).toUInt64 + (f a).toUInt64
    return a
  f value && f seed

def rangeBoolPredicateHelperCount (count seed : UInt64) : Bool :=
  let f := fun x : UInt64 => x % 3 == seed % 3
  let value := Id.run do
    let mut a := seed
    for i in [:(if f count then count % 17 else count % 5).toNat] do
      a := a + i.toUInt64 + 1
    return a
  f value

def rangeBoolPredicateHelperNested (count seed : UInt64) : Bool :=
  let f := fun x : UInt64 => x % 2 == seed % 2
  let g := fun x : UInt64 => f (x + 1) || f x
  let value := Id.run do
    let mut a := seed
    for i in [:count.toNat] do
      a := a + (g i.toUInt64).toUInt64
    return a
  g value

def rangeBoolPredicateHelperExit (count seed : UInt64) : Bool :=
  let f := fun x : UInt64 => x % 7 == seed % 7
  let value := Id.run do
    let mut a := seed
    for i in [:count.toNat] do
      a := a + i.toUInt64 + 1
      if f a then break
    return a
  f value

def rangeBoolPredicateHelperId (count : Id UInt64) (seed : UInt64) : Id Bool :=
  let f (x : UInt64) : Id (Id Bool) := pure (pure (x % 3 == seed % 3))
  let value : Id UInt64 := Id.run do
    let mut a := seed
    for i in [:(Id.run count).toNat] do
      if Id.run (Id.run (f i.toUInt64)) then continue
      a := a + i.toUInt64 + 1
    return a
  pure (Id.run (Id.run (f (Id.run value))))

def rangeBoolBooleanPredicateHelperRepeat (count seed : UInt64) : Bool :=
  let f := fun flag : Bool => flag || seed % 2 == 0
  let value := Id.run do
    let mut a := seed + (f false).toUInt64
    for i in [:count.toNat] do
      a := a + (f (i.toUInt64 % 2 == 0)).toUInt64 + (f true).toUInt64
    return a
  f (value == seed)

def rangeBoolBooleanPredicateHelperFlag (count : UInt64) (flag : Bool) : Bool :=
  let f := fun input : Bool => flag && !input
  let value := Id.run do
    let mut a := (f false).toUInt64
    for i in [:count.toNat] do
      if f (i.toUInt64 % 2 == 0) then continue
      a := a + i.toUInt64 + 1
    return a
  f (value == count)

def rangeBoolBooleanPredicateHelperNested (count seed : UInt64) : Bool :=
  let f := fun flag : Bool => flag || seed == 0
  let g := fun flag : Bool => f (!flag) && f flag
  let value := Id.run do
    let mut a := seed
    for i in [:count.toNat] do
      a := a + (g (i.toUInt64 % 3 == 0)).toUInt64
    return a
  g (value == seed)

def rangeBoolBooleanPredicateHelperStride (count seed : UInt64) : Bool :=
  let f := fun flag : Bool => flag && seed % 3 == 0
  let value := Id.run do
    let mut a := seed
    for i in [(f true).toUInt64.toNat:count.toNat:3] do
      a := a + i.toUInt64 + 1
      if f (a % 5 == 0) then break
    return a
  f (value == seed)

def rangeBoolBooleanPredicateHelperId (count : Id UInt64) (seed : UInt64) : Id Bool :=
  let f (flag : Bool) : Id (Id Bool) := pure (pure (flag || seed % 2 == 0))
  let value : Id UInt64 := Id.run do
    let mut a := seed
    for i in [:(Id.run count).toNat] do
      a := a + (Id.run (Id.run (f (i.toUInt64 % 2 == 0)))).toUInt64
    return a
  pure (Id.run (Id.run (f (Id.run value == seed))))

def inputs : List (UInt64 × UInt64) :=
  [(0, 0), (1, 0), (0xffffffffffffffff, 0), (0, 1), (1, 1),
   (0xffffffffffffffff, 1), (0x8000000000000000, 2), (42, 3),
   (0xffffffffffffffff, 63), (0x8000000000000001, 64), (0xffffffffffffffff, 65),
   (0x0123456789abcdef, 0xffffffffffffffff), (3, 17), (17, 3)]

end BooleanLoopPredicateHelpersTest

run_elab do
  let env ← Lean.getEnv
  let cases : List (Lean.Name × (UInt64 → UInt64 → UInt64) × Bool) := [
    (`BooleanLoopPredicateHelpersTest.rangeBoolPredicateHelperRepeat, (fun (x y : UInt64) => (BooleanLoopPredicateHelpersTest.rangeBoolPredicateHelperRepeat x y).toUInt64), true),
    (`BooleanLoopPredicateHelpersTest.rangeBoolPredicateHelperCount, (fun (x y : UInt64) => (BooleanLoopPredicateHelpersTest.rangeBoolPredicateHelperCount x y).toUInt64), true),
    (`BooleanLoopPredicateHelpersTest.rangeBoolPredicateHelperNested, (fun (x y : UInt64) => (BooleanLoopPredicateHelpersTest.rangeBoolPredicateHelperNested x y).toUInt64), true),
    (`BooleanLoopPredicateHelpersTest.rangeBoolPredicateHelperExit, (fun (x y : UInt64) => (BooleanLoopPredicateHelpersTest.rangeBoolPredicateHelperExit x y).toUInt64), true),
    (`BooleanLoopPredicateHelpersTest.rangeBoolPredicateHelperId, (fun (x y : UInt64) => (BooleanLoopPredicateHelpersTest.rangeBoolPredicateHelperId x y).toUInt64), true),
    (`BooleanLoopPredicateHelpersTest.rangeBoolBooleanPredicateHelperRepeat, (fun (x y : UInt64) => (BooleanLoopPredicateHelpersTest.rangeBoolBooleanPredicateHelperRepeat x y).toUInt64), true),
    (`BooleanLoopPredicateHelpersTest.rangeBoolBooleanPredicateHelperFlag, (fun (x y : UInt64) => (BooleanLoopPredicateHelpersTest.rangeBoolBooleanPredicateHelperFlag x (y != 0)).toUInt64), true),
    (`BooleanLoopPredicateHelpersTest.rangeBoolBooleanPredicateHelperNested, (fun (x y : UInt64) => (BooleanLoopPredicateHelpersTest.rangeBoolBooleanPredicateHelperNested x y).toUInt64), true),
    (`BooleanLoopPredicateHelpersTest.rangeBoolBooleanPredicateHelperStride, (fun (x y : UInt64) => (BooleanLoopPredicateHelpersTest.rangeBoolBooleanPredicateHelperStride x y).toUInt64), true),
    (`BooleanLoopPredicateHelpersTest.rangeBoolBooleanPredicateHelperId, (fun (x y : UInt64) => (BooleanLoopPredicateHelpersTest.rangeBoolBooleanPredicateHelperId x y).toUInt64), true)]
  let mut comparisons : Nat := 0
  for (name, native, isRange) in cases do
    let some info := env.find? name | throwError "missing declaration"
    let some value := info.value? | throwError "missing body"
    let some func := LeanExe.Extract.Core.extractScalarFunc name (some "entry") info.type value |
      throwError "{name}: Boolean loop predicate-helpers extraction failed"
    let module_ : LeanExe.IR.Module := { funcs := #[func] }
    let inputs := if isRange then
      ([0, 1, 2, 7, 16, 31] : List UInt64).flatMap fun n =>
        ([0, 1, 0x8000000000000000, 0xffffffffffffffff] : List UInt64).map fun seed => (n, seed)
      else BooleanLoopPredicateHelpersTest.inputs
    for (x, y) in inputs do
      let expected := native x y
      let actual := module_.evalFunc 0 [x, y]
      unless actual == expected do
        throwError "{name}({x}, {y}): native={expected}, IR={actual}"
      comparisons := comparisons + 1
  unless comparisons == 240 do throwError "unexpected comparison count {comparisons}"
  Lean.logInfo m!"{comparisons} native/Boolean loop predicate-helpers IR comparisons passed"

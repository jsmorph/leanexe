import LeanExe.Extract.ScalarFunc

namespace BooleanLoopUnitHelpersTest

def rangeBoolUnitHelperRepeat (count seed : UInt64) : Bool :=
  let f := fun (_unit : Unit) (x : UInt64) => x + seed + 1
  let value := Id.run do
    let mut a := f () seed
    for i in [:count.toNat] do
      a := f () a + f () i.toUInt64
    return a
  f () value == f () (f () seed)

def rangeBoolUnitHelperCount (count seed : UInt64) : Bool :=
  let limit := fun (_unit : PUnit) (x : UInt64) => x % 17
  let value := Id.run do
    let mut a := seed
    for i in [:(limit () count).toNat] do
      a := a + i.toUInt64 + 1
    return a
  value == seed + limit () count

def rangeBoolUnitHelperInitial (count seed : UInt64) : Bool :=
  let f := fun (_unit : Unit) (x : UInt64) => x * 3 + seed
  let value := Id.run do
    let mut a := f () 0
    for i in [:count.toNat] do
      a := a + f () i.toUInt64
    return a
  value == f () 0

def rangeBoolUnitHelperNested (count seed : UInt64) : Id Bool :=
  let f := fun (_unit : Unit) (x : UInt64) => x + seed
  let g := fun (_unit : Unit) (x : UInt64) => f () (x * 3) + f () x
  let value := Id.run do
    let mut a := g () 0
    for i in [:count.toNat] do
      a := g () (a + i.toUInt64)
    return a
  pure (g () value == g () seed)

def rangeBoolUnitHelperFlag (count : UInt64) (flag : Bool) : Bool :=
  let f := fun (_unit : Unit) (x : UInt64) => if flag then x + 7 else x - 3
  let value := Id.run do
    let mut a := f () count
    for i in [:count.toNat] do
      a := f () (a + i.toUInt64)
    return a
  flag && value == f () count

def rangeBoolUnitHelperExit (count seed : UInt64) : Bool :=
  let f := fun (_unit : Unit) (x : UInt64) => x + seed % 5 + 1
  let value := Id.run do
    let mut a := seed
    for i in [:count.toNat] do
      a := f () (a + i.toUInt64)
      if a % 7 == 0 then break
    return a
  f () value % 7 == 0

def rangeBoolUnitHelperContinue (count seed : UInt64) : Bool :=
  let f := fun (_unit : Unit) (x : UInt64) => x % 3
  let value := Id.run do
    let mut a := seed
    for i in [:count.toNat] do
      if f () i.toUInt64 == 0 then continue
      a := a + i.toUInt64 + 1
    return a
  f () value == f () seed

def rangeBoolUnitHelperStride (count seed : UInt64) : Bool :=
  let f := fun (_unit : Unit) (x : UInt64) => x % 3
  let value := Id.run do
    let mut a := seed
    for i in [(f () seed).toNat:count.toNat:3] do
      a := a + i.toUInt64 + 1
      if a % 5 == 0 then break
    return a
  f () value == f () seed

def rangeBoolUnitHelperId (count : Id UInt64) (seed : UInt64) : Id Bool :=
  let f (_unit : Unit) (x : UInt64) : Id (Id UInt64) := pure (pure (x + seed + 1))
  let value : Id UInt64 := Id.run do
    let mut a := Id.run (Id.run (f () 0))
    for i in [:(Id.run count).toNat] do
      a := Id.run (Id.run (f () (a + i.toUInt64)))
    return a
  pure (Id.run (Id.run (f () (Id.run value))) == seed)

def rangeBoolUnitHelperShadow (count seed : UInt64) : Bool :=
  let f := fun (_unit : Unit) (x : UInt64) => x + seed
  let initial := f () 0
  let f := fun (_unit : Unit) (x : UInt64) => f () x + count
  let value := Id.run do
    let mut a := initial
    for i in [:count.toNat] do
      a := f () (a + i.toUInt64)
    return a
  f () value == f () initial

def inputs : List (UInt64 × UInt64) :=
  [(0, 0), (1, 0), (0xffffffffffffffff, 0), (0, 1), (1, 1),
   (0xffffffffffffffff, 1), (0x8000000000000000, 2), (42, 3),
   (0xffffffffffffffff, 63), (0x8000000000000001, 64), (0xffffffffffffffff, 65),
   (0x0123456789abcdef, 0xffffffffffffffff), (3, 17), (17, 3)]

end BooleanLoopUnitHelpersTest

run_elab do
  let env ← Lean.getEnv
  let cases : List (Lean.Name × (UInt64 → UInt64 → UInt64) × Bool) := [
    (`BooleanLoopUnitHelpersTest.rangeBoolUnitHelperRepeat, (fun (x y : UInt64) => (BooleanLoopUnitHelpersTest.rangeBoolUnitHelperRepeat x y).toUInt64), true),
    (`BooleanLoopUnitHelpersTest.rangeBoolUnitHelperCount, (fun (x y : UInt64) => (BooleanLoopUnitHelpersTest.rangeBoolUnitHelperCount x y).toUInt64), true),
    (`BooleanLoopUnitHelpersTest.rangeBoolUnitHelperInitial, (fun (x y : UInt64) => (BooleanLoopUnitHelpersTest.rangeBoolUnitHelperInitial x y).toUInt64), true),
    (`BooleanLoopUnitHelpersTest.rangeBoolUnitHelperNested, (fun (x y : UInt64) => (BooleanLoopUnitHelpersTest.rangeBoolUnitHelperNested x y).toUInt64), true),
    (`BooleanLoopUnitHelpersTest.rangeBoolUnitHelperFlag, (fun (x y : UInt64) => (BooleanLoopUnitHelpersTest.rangeBoolUnitHelperFlag x (y != 0)).toUInt64), true),
    (`BooleanLoopUnitHelpersTest.rangeBoolUnitHelperExit, (fun (x y : UInt64) => (BooleanLoopUnitHelpersTest.rangeBoolUnitHelperExit x y).toUInt64), true),
    (`BooleanLoopUnitHelpersTest.rangeBoolUnitHelperContinue, (fun (x y : UInt64) => (BooleanLoopUnitHelpersTest.rangeBoolUnitHelperContinue x y).toUInt64), true),
    (`BooleanLoopUnitHelpersTest.rangeBoolUnitHelperStride, (fun (x y : UInt64) => (BooleanLoopUnitHelpersTest.rangeBoolUnitHelperStride x y).toUInt64), true),
    (`BooleanLoopUnitHelpersTest.rangeBoolUnitHelperId, (fun (x y : UInt64) => (BooleanLoopUnitHelpersTest.rangeBoolUnitHelperId x y).toUInt64), true),
    (`BooleanLoopUnitHelpersTest.rangeBoolUnitHelperShadow, (fun (x y : UInt64) => (BooleanLoopUnitHelpersTest.rangeBoolUnitHelperShadow x y).toUInt64), true)]
  let mut comparisons : Nat := 0
  for (name, native, isRange) in cases do
    let some info := env.find? name | throwError "missing declaration"
    let some value := info.value? | throwError "missing body"
    let some func := LeanExe.Extract.Core.extractScalarFunc name (some "entry") info.type value |
      throwError "{name}: Boolean loop unit-helpers extraction failed"
    let module_ : LeanExe.IR.Module := { funcs := #[func] }
    let inputs := if isRange then
      ([0, 1, 2, 7, 16, 31] : List UInt64).flatMap fun n =>
        ([0, 1, 0x8000000000000000, 0xffffffffffffffff] : List UInt64).map fun seed => (n, seed)
      else BooleanLoopUnitHelpersTest.inputs
    for (x, y) in inputs do
      let expected := native x y
      let actual := module_.evalFunc 0 [x, y]
      unless actual == expected do
        throwError "{name}({x}, {y}): native={expected}, IR={actual}"
      comparisons := comparisons + 1
  unless comparisons == 240 do throwError "unexpected comparison count {comparisons}"
  Lean.logInfo m!"{comparisons} native/Boolean loop unit-helpers IR comparisons passed"

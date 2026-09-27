import LeanExe.Extract.ScalarFunc

namespace BooleanLoopManyHelpersTest

def rangeBoolManyHelperBinaryRepeat (count seed : UInt64) : Bool :=
  let f := fun x y : UInt64 => x + 3 * y + seed
  let value := Id.run do
    let mut a := f seed 1
    for i in [:count.toNat] do
      a := f a i.toUInt64 + f i.toUInt64 a
    return a
  f value 1 == f seed 1

def rangeBoolManyHelperBinaryCount (count seed : UInt64) : Bool :=
  let limit := fun x y : UInt64 => (x + y) % 17
  let value := Id.run do
    let mut a := seed
    for i in [:(limit count seed).toNat] do
      a := a + i.toUInt64 + 1
    return a
  value == seed + limit seed count

def rangeBoolManyHelperTernaryInitial (count seed : UInt64) : Bool :=
  let f := fun x y z : UInt64 => x + y * 3 + z * 5 + seed
  let value := Id.run do
    let mut a := f 0 1 2
    for i in [:count.toNat] do
      a := f a i.toUInt64 3
    return a
  value == f 0 1 2

def rangeBoolManyHelperTernaryNested (count seed : UInt64) : Bool :=
  let f := fun x y z : UInt64 => x + 3 * y + 5 * z + seed
  let g := fun x y z : UInt64 => f (x + 1) (y + 2) (z + 3) + f z y x
  let value := Id.run do
    let mut a := g 0 1 2
    for i in [:count.toNat] do
      a := g a i.toUInt64 1
    return a
  value == g seed 1 2

def rangeBoolManyHelperFiveFlag (count : UInt64) (flag : Bool) : Bool :=
  let f := fun a b c d e : UInt64 => if flag then a + 3*b + 5*c + 7*d + 11*e else a-b-c-d-e
  let value := Id.run do
    let mut a := f count 1 2 3 4
    for i in [:count.toNat] do
      a := f a i.toUInt64 1 2 count
    return a
  flag && value == f count 1 2 3 4

def rangeBoolManyHelperBinaryExit (count seed : UInt64) : Bool :=
  let f := fun x y : UInt64 => x + 3 * y + seed % 5 + 1
  let value := Id.run do
    let mut a := seed
    for i in [:count.toNat] do
      a := f a i.toUInt64
      if a % 7 == 0 then break
    return a
  f value 1 % 7 == 0

def rangeBoolManyHelperTernaryContinue (count seed : UInt64) : Bool :=
  let f := fun x y z : UInt64 => (x + 3 * y + 5 * z) % 3
  let value := Id.run do
    let mut a := seed
    for i in [:count.toNat] do
      if f i.toUInt64 a seed == 0 then continue
      a := a + i.toUInt64 + 1
    return a
  f value seed 1 == f seed value 1

def rangeBoolManyHelperFiveStride (count seed : UInt64) : Bool :=
  let f := fun a b c d e : UInt64 => (a + 3*b + 5*c + 7*d + 11*e) % 3
  let value := Id.run do
    let mut a := seed
    for i in [(f seed 1 2 3 4).toNat:count.toNat:3] do
      a := a + i.toUInt64 + 1
      if a % 5 == 0 then break
    return a
  f value 1 2 3 4 == f seed 1 2 3 4

def rangeBoolManyHelperFiveId (count : Id UInt64) (seed : UInt64) : Id Bool :=
  let f (a b c d e : UInt64) : Id (Id UInt64) := pure (pure (a + 3*b + 5*c + 7*d + 11*e + seed))
  let value : Id UInt64 := Id.run do
    let mut a := Id.run (Id.run (f seed 1 2 3 4))
    for i in [:(Id.run count).toNat] do
      a := Id.run (Id.run (f a i.toUInt64 1 2 3))
    return a
  pure (Id.run value == Id.run (Id.run (f seed 1 2 3 4)))

def rangeBoolManyHelperBinaryShadow (count seed : UInt64) : Bool :=
  let f := fun x y : UInt64 => x + 3 * y + seed
  let initial := f 0 1
  let f := fun x y : UInt64 => f y x + count
  let value := Id.run do
    let mut a := initial
    for i in [:count.toNat] do
      a := f a i.toUInt64
    return a
  value == f initial 1

def inputs : List (UInt64 × UInt64) :=
  [(0, 0), (1, 0), (0xffffffffffffffff, 0), (0, 1), (1, 1),
   (0xffffffffffffffff, 1), (0x8000000000000000, 2), (42, 3),
   (0xffffffffffffffff, 63), (0x8000000000000001, 64), (0xffffffffffffffff, 65),
   (0x0123456789abcdef, 0xffffffffffffffff), (3, 17), (17, 3)]

end BooleanLoopManyHelpersTest

run_elab do
  let env ← Lean.getEnv
  let cases : List (Lean.Name × (UInt64 → UInt64 → UInt64) × Bool) := [
    (`BooleanLoopManyHelpersTest.rangeBoolManyHelperBinaryRepeat, (fun (x y : UInt64) => (BooleanLoopManyHelpersTest.rangeBoolManyHelperBinaryRepeat x y).toUInt64), true),
    (`BooleanLoopManyHelpersTest.rangeBoolManyHelperBinaryCount, (fun (x y : UInt64) => (BooleanLoopManyHelpersTest.rangeBoolManyHelperBinaryCount x y).toUInt64), true),
    (`BooleanLoopManyHelpersTest.rangeBoolManyHelperTernaryInitial, (fun (x y : UInt64) => (BooleanLoopManyHelpersTest.rangeBoolManyHelperTernaryInitial x y).toUInt64), true),
    (`BooleanLoopManyHelpersTest.rangeBoolManyHelperTernaryNested, (fun (x y : UInt64) => (BooleanLoopManyHelpersTest.rangeBoolManyHelperTernaryNested x y).toUInt64), true),
    (`BooleanLoopManyHelpersTest.rangeBoolManyHelperFiveFlag, (fun (x y : UInt64) => (BooleanLoopManyHelpersTest.rangeBoolManyHelperFiveFlag x (y != 0)).toUInt64), true),
    (`BooleanLoopManyHelpersTest.rangeBoolManyHelperBinaryExit, (fun (x y : UInt64) => (BooleanLoopManyHelpersTest.rangeBoolManyHelperBinaryExit x y).toUInt64), true),
    (`BooleanLoopManyHelpersTest.rangeBoolManyHelperTernaryContinue, (fun (x y : UInt64) => (BooleanLoopManyHelpersTest.rangeBoolManyHelperTernaryContinue x y).toUInt64), true),
    (`BooleanLoopManyHelpersTest.rangeBoolManyHelperFiveStride, (fun (x y : UInt64) => (BooleanLoopManyHelpersTest.rangeBoolManyHelperFiveStride x y).toUInt64), true),
    (`BooleanLoopManyHelpersTest.rangeBoolManyHelperFiveId, (fun (x y : UInt64) => (BooleanLoopManyHelpersTest.rangeBoolManyHelperFiveId x y).toUInt64), true),
    (`BooleanLoopManyHelpersTest.rangeBoolManyHelperBinaryShadow, (fun (x y : UInt64) => (BooleanLoopManyHelpersTest.rangeBoolManyHelperBinaryShadow x y).toUInt64), true)]
  let mut comparisons : Nat := 0
  for (name, native, isRange) in cases do
    let some info := env.find? name | throwError "missing declaration"
    let some value := info.value? | throwError "missing body"
    let some func := LeanExe.Extract.Core.extractScalarFunc name (some "entry") info.type value |
      throwError "{name}: Boolean loop many-helpers extraction failed"
    let module_ : LeanExe.IR.Module := { funcs := #[func] }
    let inputs := if isRange then
      ([0, 1, 2, 7, 16, 31] : List UInt64).flatMap fun n =>
        ([0, 1, 0x8000000000000000, 0xffffffffffffffff] : List UInt64).map fun seed => (n, seed)
      else BooleanLoopManyHelpersTest.inputs
    for (x, y) in inputs do
      let expected := native x y
      let actual := module_.evalFunc 0 [x, y]
      unless actual == expected do
        throwError "{name}({x}, {y}): native={expected}, IR={actual}"
      comparisons := comparisons + 1
  unless comparisons == 240 do throwError "unexpected comparison count {comparisons}"
  Lean.logInfo m!"{comparisons} native/Boolean loop many-helpers IR comparisons passed"

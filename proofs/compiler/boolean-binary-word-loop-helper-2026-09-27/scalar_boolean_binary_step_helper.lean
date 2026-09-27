import LeanExe.Extract.ScalarFunc

namespace BinaryStepHelperTest

def rangeBinaryStepHelperDirect (count seed : UInt64) : Id UInt64 := do
  let mut a := seed
  for i in [:count.toNat] do
    let f := fun x y : UInt64 => x + 3 * y == a
    if f i.toUInt64 seed then a := a + 7 else a := a + 1
  return a

def rangeBinaryStepHelperExit (count seed : UInt64) : Id UInt64 := do
  let mut a := seed
  for i in [:count.toNat] do
    let f := fun x y : UInt64 => x + 3 * y == 7
    a := a + i.toUInt64 + 1
    if f a seed || f seed a then break
  return a

def rangeBinaryStepHelperContinue (count seed : UInt64) : Id UInt64 := do
  let mut a := seed
  for i in [:count.toNat] do
    let f := fun x y : UInt64 => (pure (x + 3 * y == a) : Id Bool)
    if Id.run (f i.toUInt64 seed) then continue
    a := a * 3 + i.toUInt64 + 1
  return a

def rangeBinaryStepHelperNested (count seed : UInt64) : Id UInt64 := do
  let mut a := seed
  for i in [:count.toNat] do
    let f := fun x y : UInt64 => x == y
    let g := fun x y : UInt64 => f (x + 3 * y) a || f seed y
    a := a + (g i.toUInt64 seed).toUInt64 + (g seed i.toUInt64).toUInt64
  return a

def rangeBinaryStepHelperUnused (count seed : UInt64) : Id UInt64 := do
  let mut a := seed
  for i in [:count.toNat] do
    let _f := fun x y : UInt64 => x + 3 * y == a
    a := a + i.toUInt64 + 1
  return a

def rangeBinaryStepHelperWordTail (count seed : UInt64) : Id UInt64 := do
  let mut a := seed
  for i in [:count.toNat] do
    let f := fun x y : UInt64 => x + 3 * y == a
    let saved := (f i.toUInt64 seed).toUInt64
    if f seed a then a := saved + 5 else a := a + saved + 1
  return a * 3 + seed

def rangeBinaryStepHelperCapturedExit (count seed : UInt64) : Id UInt64 := do
  let mut a := seed
  for i in [:count.toNat] do
    let f := fun x y : UInt64 => (x + 3 * y) % 7 == a % 7
    a := a + i.toUInt64 + 1
    if f seed a || f a seed then break
  return a

def rangeBinaryStepHelperChoice (count seed : UInt64) : Id UInt64 := do
  let mut a := seed
  for i in [:count.toNat] do
    let f := fun x y : UInt64 => x + 3 * y == a
    let first := if i.toUInt64 == 0 then seed else a
    if f first (a + i.toUInt64) then a := a + 7 else a := a * 3 + 1
    if f a first then break
  return a

def inputs : List (UInt64 × UInt64) :=
  [(0, 0), (1, 0), (0xffffffffffffffff, 0), (0, 1), (1, 1),
   (0xffffffffffffffff, 1), (0x8000000000000000, 2), (42, 3),
   (0xffffffffffffffff, 63), (0x8000000000000001, 64), (0xffffffffffffffff, 65),
   (0x0123456789abcdef, 0xffffffffffffffff), (3, 17), (17, 3)]

end BinaryStepHelperTest

run_elab do
  let env ← Lean.getEnv
  let cases : List (Lean.Name × (UInt64 → UInt64 → UInt64) × Bool) := [
    (`BinaryStepHelperTest.rangeBinaryStepHelperDirect, (fun (x y : UInt64) => BinaryStepHelperTest.rangeBinaryStepHelperDirect x y), true),
    (`BinaryStepHelperTest.rangeBinaryStepHelperExit, (fun (x y : UInt64) => BinaryStepHelperTest.rangeBinaryStepHelperExit x y), true),
    (`BinaryStepHelperTest.rangeBinaryStepHelperContinue, (fun (x y : UInt64) => BinaryStepHelperTest.rangeBinaryStepHelperContinue x y), true),
    (`BinaryStepHelperTest.rangeBinaryStepHelperNested, (fun (x y : UInt64) => BinaryStepHelperTest.rangeBinaryStepHelperNested x y), true),
    (`BinaryStepHelperTest.rangeBinaryStepHelperUnused, (fun (x y : UInt64) => BinaryStepHelperTest.rangeBinaryStepHelperUnused x y), true),
    (`BinaryStepHelperTest.rangeBinaryStepHelperWordTail, (fun (x y : UInt64) => BinaryStepHelperTest.rangeBinaryStepHelperWordTail x y), true),
    (`BinaryStepHelperTest.rangeBinaryStepHelperCapturedExit, (fun (x y : UInt64) => BinaryStepHelperTest.rangeBinaryStepHelperCapturedExit x y), true),
    (`BinaryStepHelperTest.rangeBinaryStepHelperChoice, (fun (x y : UInt64) => BinaryStepHelperTest.rangeBinaryStepHelperChoice x y), true)]
  let mut comparisons : Nat := 0
  for (name, native, isRange) in cases do
    let some info := env.find? name | throwError "missing declaration"
    let some value := info.value? | throwError "missing body"
    let some func := LeanExe.Extract.Core.extractScalarFunc name (some "entry") info.type value |
      throwError "{name}: binary Boolean step helper extraction failed"
    let module_ : LeanExe.IR.Module := { funcs := #[func] }
    let inputs := if isRange then
      ([0, 1, 2, 7, 16, 31] : List UInt64).flatMap fun n =>
        ([0, 1, 0x8000000000000000, 0xffffffffffffffff] : List UInt64).map fun seed => (n, seed)
      else BinaryStepHelperTest.inputs
    for (x, y) in inputs do
      let expected := native x y
      let actual := module_.evalFunc 0 [x, y]
      unless actual == expected do
        throwError "{name}({x}, {y}): native={expected}, IR={actual}"
      comparisons := comparisons + 1
  unless comparisons == 192 do throwError "unexpected comparison count {comparisons}"
  Lean.logInfo m!"{comparisons} native/binary Boolean step helper IR comparisons passed"

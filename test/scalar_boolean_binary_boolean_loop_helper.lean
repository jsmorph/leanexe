import LeanExe.Extract.ScalarFunc

namespace BinaryBooleanLoopHelperTest

def rangeBinaryBooleanLoopHelperDirect (count seed : UInt64) : Id Bool := do
  let f := fun x y : UInt64 => x + 3 * y == seed
  let mut a := seed != 0
  for i in [:count.toNat] do
    a := f i.toUInt64 a.toUInt64 || a
  return a

def rangeBinaryBooleanLoopHelperBound (count seed : UInt64) : Id Bool := do
  let f := fun x y : UInt64 => x + 3 * y == seed
  let n := if f count seed then count else count % 7
  let mut a := seed != 0
  for i in [:n.toNat] do
    a := (f i.toUInt64 seed) != a
  return a

def rangeBinaryBooleanLoopHelperInitial (count seed : UInt64) : Id Bool := do
  let f := fun x y : UInt64 => x + 3 * y == seed
  let mut a := f seed count
  for i in [:count.toNat] do
    a := (i.toUInt64 == seed) || !a
  return a

def rangeBinaryBooleanLoopHelperExit (count seed : UInt64) : Id Bool := do
  let f := fun x y : UInt64 => (x + 3 * y) % 7 == seed % 7
  let mut a := seed != 0
  for i in [:count.toNat] do
    a := !a
    if f i.toUInt64 a.toUInt64 || f seed i.toUInt64 then break
  return a

def rangeBinaryBooleanLoopHelperUnused (count seed : UInt64) : Id Bool := do
  let _f := fun x y : UInt64 => x + 3 * y == seed
  let mut a := seed != 0
  for i in [:count.toNat] do
    a := (i.toUInt64 == seed) || !a
  return a

def rangeBinaryBooleanLoopHelperWordTail (count seed : UInt64) : Id UInt64 := do
  let f := fun x y : UInt64 => x + 3 * y == seed
  let mut a := seed != 0
  for i in [:count.toNat] do
    a := (i.toUInt64 == seed) || !a
  return a.toUInt64 + (f a.toUInt64 seed).toUInt64 + (f seed a.toUInt64).toUInt64

def rangeBinaryBooleanLoopHelperCapture (count seed : UInt64) : Id Bool := do
  let f := fun x y : UInt64 => (x + 3 * y) % 7 == seed % 7
  let seed := seed + 1
  let mut a := seed != 0
  for i in [:count.toNat] do
    a := (f i.toUInt64 seed) != a
    if f a.toUInt64 seed then break
  return a

def rangeBinaryBooleanLoopHelperNested (count seed : UInt64) : Id Bool := do
  let f := fun x y : UInt64 => x + 3 * y == seed
  let g := fun x y : UInt64 => (pure (f y x || x == y) : Id Bool)
  let mut a := seed != 0
  for i in [:count.toNat] do
    if Id.run (g i.toUInt64 a.toUInt64) then continue
    a := (i.toUInt64 == seed) || !a
  return a

def inputs : List (UInt64 × UInt64) :=
  [(0, 0), (1, 0), (0xffffffffffffffff, 0), (0, 1), (1, 1),
   (0xffffffffffffffff, 1), (0x8000000000000000, 2), (42, 3),
   (0xffffffffffffffff, 63), (0x8000000000000001, 64), (0xffffffffffffffff, 65),
   (0x0123456789abcdef, 0xffffffffffffffff), (3, 17), (17, 3)]

end BinaryBooleanLoopHelperTest

run_elab do
  let env ← Lean.getEnv
  let cases : List (Lean.Name × (UInt64 → UInt64 → UInt64) × Bool) := [
    (`BinaryBooleanLoopHelperTest.rangeBinaryBooleanLoopHelperDirect, (fun (x y : UInt64) => (BinaryBooleanLoopHelperTest.rangeBinaryBooleanLoopHelperDirect x y).toUInt64), true),
    (`BinaryBooleanLoopHelperTest.rangeBinaryBooleanLoopHelperBound, (fun (x y : UInt64) => (BinaryBooleanLoopHelperTest.rangeBinaryBooleanLoopHelperBound x y).toUInt64), true),
    (`BinaryBooleanLoopHelperTest.rangeBinaryBooleanLoopHelperInitial, (fun (x y : UInt64) => (BinaryBooleanLoopHelperTest.rangeBinaryBooleanLoopHelperInitial x y).toUInt64), true),
    (`BinaryBooleanLoopHelperTest.rangeBinaryBooleanLoopHelperExit, (fun (x y : UInt64) => (BinaryBooleanLoopHelperTest.rangeBinaryBooleanLoopHelperExit x y).toUInt64), true),
    (`BinaryBooleanLoopHelperTest.rangeBinaryBooleanLoopHelperUnused, (fun (x y : UInt64) => (BinaryBooleanLoopHelperTest.rangeBinaryBooleanLoopHelperUnused x y).toUInt64), true),
    (`BinaryBooleanLoopHelperTest.rangeBinaryBooleanLoopHelperWordTail, (fun (x y : UInt64) => BinaryBooleanLoopHelperTest.rangeBinaryBooleanLoopHelperWordTail x y), true),
    (`BinaryBooleanLoopHelperTest.rangeBinaryBooleanLoopHelperCapture, (fun (x y : UInt64) => (BinaryBooleanLoopHelperTest.rangeBinaryBooleanLoopHelperCapture x y).toUInt64), true),
    (`BinaryBooleanLoopHelperTest.rangeBinaryBooleanLoopHelperNested, (fun (x y : UInt64) => (BinaryBooleanLoopHelperTest.rangeBinaryBooleanLoopHelperNested x y).toUInt64), true)]
  let mut comparisons : Nat := 0
  for (name, native, isRange) in cases do
    let some info := env.find? name | throwError "missing declaration"
    let some value := info.value? | throwError "missing body"
    let some func := LeanExe.Extract.Core.extractScalarFunc name (some "entry") info.type value |
      throwError "{name}: outer binary Boolean-result loop helper extraction failed"
    let module_ : LeanExe.IR.Module := { funcs := #[func] }
    let inputs := if isRange then
      ([0, 1, 2, 7, 16, 31] : List UInt64).flatMap fun n =>
        ([0, 1, 0x8000000000000000, 0xffffffffffffffff] : List UInt64).map fun seed => (n, seed)
      else BinaryBooleanLoopHelperTest.inputs
    for (x, y) in inputs do
      let expected := native x y
      let actual := module_.evalFunc 0 [x, y]
      unless actual == expected do
        throwError "{name}({x}, {y}): native={expected}, IR={actual}"
      comparisons := comparisons + 1
  unless comparisons == 192 do throwError "unexpected comparison count {comparisons}"
  Lean.logInfo m!"{comparisons} native/outer binary Boolean-result loop helper IR comparisons passed"

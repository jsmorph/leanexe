import LeanExe.Extract.ScalarFunc

namespace BinaryWordLoopHelperTest

def rangeBinaryWordLoopHelperDirect (count seed : UInt64) : Id UInt64 := do
  let f := fun x y : UInt64 => x + 3 * y == seed
  let mut a := seed
  for i in [:count.toNat] do
    a := a + (f i.toUInt64 a).toUInt64 + 1
  return a

def rangeBinaryWordLoopHelperBound (count seed : UInt64) : Id UInt64 := do
  let f := fun x y : UInt64 => x + 3 * y == seed
  let n := if f count seed then count else count % 7
  let mut a := seed
  for i in [:n.toNat] do
    a := a + i.toUInt64 + (f a seed).toUInt64
  return a

def rangeBinaryWordLoopHelperInitial (count seed : UInt64) : Id UInt64 := do
  let f := fun x y : UInt64 => x + 3 * y == seed
  let mut a := if f seed 0 then seed + 1 else seed
  for i in [:count.toNat] do
    a := a + i.toUInt64 + 1
  return a

def rangeBinaryWordLoopHelperExit (count seed : UInt64) : Id UInt64 := do
  let f := fun x y : UInt64 => (x + 3 * y) % 7 == seed % 7
  let mut a := seed
  for i in [:count.toNat] do
    a := a + i.toUInt64 + 1
    if f a seed || f seed a then break
  return a

def rangeBinaryWordLoopHelperUnused (count seed : UInt64) : Id UInt64 := do
  let _f := fun x y : UInt64 => x + 3 * y == seed
  let mut a := seed
  for i in [:count.toNat] do
    a := a + i.toUInt64 + 1
  return a

def rangeBinaryWordLoopHelperTail (count seed : UInt64) : Id UInt64 := do
  let f := fun x y : UInt64 => x + 3 * y == seed
  let mut a := seed
  for i in [:count.toNat] do
    a := a + i.toUInt64 + 1
  return a + (f a seed).toUInt64 + (f seed a).toUInt64

def rangeBinaryWordLoopHelperCapture (count seed : UInt64) : Id UInt64 := do
  let f := fun x y : UInt64 => (x + 3 * y) % 7 == seed % 7
  let seed := seed + 1
  let mut a := seed
  for i in [:count.toNat] do
    a := a + (f i.toUInt64 seed).toUInt64 + 1
    if f a seed then break
  return a + (f seed a).toUInt64

def rangeBinaryWordLoopHelperNested (count seed : UInt64) : Id UInt64 := do
  let f := fun x y : UInt64 => x + 3 * y == seed
  let g := fun x y : UInt64 => (pure (f y x || x == y) : Id Bool)
  let mut a := seed
  for i in [:count.toNat] do
    if Id.run (g i.toUInt64 a) then continue
    a := a + i.toUInt64 + 1
  return a + (Id.run (g a seed)).toUInt64

def inputs : List (UInt64 × UInt64) :=
  [(0, 0), (1, 0), (0xffffffffffffffff, 0), (0, 1), (1, 1),
   (0xffffffffffffffff, 1), (0x8000000000000000, 2), (42, 3),
   (0xffffffffffffffff, 63), (0x8000000000000001, 64), (0xffffffffffffffff, 65),
   (0x0123456789abcdef, 0xffffffffffffffff), (3, 17), (17, 3)]

end BinaryWordLoopHelperTest

run_elab do
  let env ← Lean.getEnv
  let cases : List (Lean.Name × (UInt64 → UInt64 → UInt64) × Bool) := [
    (`BinaryWordLoopHelperTest.rangeBinaryWordLoopHelperDirect, (fun (x y : UInt64) => BinaryWordLoopHelperTest.rangeBinaryWordLoopHelperDirect x y), true),
    (`BinaryWordLoopHelperTest.rangeBinaryWordLoopHelperBound, (fun (x y : UInt64) => BinaryWordLoopHelperTest.rangeBinaryWordLoopHelperBound x y), true),
    (`BinaryWordLoopHelperTest.rangeBinaryWordLoopHelperInitial, (fun (x y : UInt64) => BinaryWordLoopHelperTest.rangeBinaryWordLoopHelperInitial x y), true),
    (`BinaryWordLoopHelperTest.rangeBinaryWordLoopHelperExit, (fun (x y : UInt64) => BinaryWordLoopHelperTest.rangeBinaryWordLoopHelperExit x y), true),
    (`BinaryWordLoopHelperTest.rangeBinaryWordLoopHelperUnused, (fun (x y : UInt64) => BinaryWordLoopHelperTest.rangeBinaryWordLoopHelperUnused x y), true),
    (`BinaryWordLoopHelperTest.rangeBinaryWordLoopHelperTail, (fun (x y : UInt64) => BinaryWordLoopHelperTest.rangeBinaryWordLoopHelperTail x y), true),
    (`BinaryWordLoopHelperTest.rangeBinaryWordLoopHelperCapture, (fun (x y : UInt64) => BinaryWordLoopHelperTest.rangeBinaryWordLoopHelperCapture x y), true),
    (`BinaryWordLoopHelperTest.rangeBinaryWordLoopHelperNested, (fun (x y : UInt64) => BinaryWordLoopHelperTest.rangeBinaryWordLoopHelperNested x y), true)]
  let mut comparisons : Nat := 0
  for (name, native, isRange) in cases do
    let some info := env.find? name | throwError "missing declaration"
    let some value := info.value? | throwError "missing body"
    let some func := LeanExe.Extract.Core.extractScalarFunc name (some "entry") info.type value |
      throwError "{name}: outer binary Boolean word-loop helper extraction failed"
    let module_ : LeanExe.IR.Module := { funcs := #[func] }
    let inputs := if isRange then
      ([0, 1, 2, 7, 16, 31] : List UInt64).flatMap fun n =>
        ([0, 1, 0x8000000000000000, 0xffffffffffffffff] : List UInt64).map fun seed => (n, seed)
      else BinaryWordLoopHelperTest.inputs
    for (x, y) in inputs do
      let expected := native x y
      let actual := module_.evalFunc 0 [x, y]
      unless actual == expected do
        throwError "{name}({x}, {y}): native={expected}, IR={actual}"
      comparisons := comparisons + 1
  unless comparisons == 192 do throwError "unexpected comparison count {comparisons}"
  Lean.logInfo m!"{comparisons} native/outer binary Boolean word-loop helper IR comparisons passed"

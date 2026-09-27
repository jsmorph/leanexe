import LeanExe.Extract.ScalarFunc

namespace BinaryBooleanHelperTest

def binaryBooleanHelperDirect (x y : UInt64) : UInt64 :=
  let f := fun a b : UInt64 => a == b
  (f x y).toUInt64 + x

def binaryBooleanHelperRepeated (x y : UInt64) : UInt64 :=
  (let f := fun a b : UInt64 => a == b
   f x y || f y 0).toUInt64 + y

def binaryBooleanHelperCapture (x y : UInt64) : UInt64 :=
  (let saved := x + y
   let f := fun a b : UInt64 => a + b == saved
   f x y && f y x).toUInt64 + x

def binaryBooleanHelperNested (x y : UInt64) : UInt64 :=
  (let f := fun a b : UInt64 =>
     let g := fun n : UInt64 => n == b
     g a || g x
   f x y && f y x).toUInt64 + y

def binaryBooleanHelperRetained (x y : UInt64) : UInt64 :=
  (let f := fun (a b : UInt64) => (pure (a == b) : Id Bool)
   Id.run (f x y) || Id.run (f y 0)).toUInt64 + x

def binaryBooleanHelperUnused (x y : UInt64) : UInt64 :=
  (let _f := fun a b : UInt64 => a == b
   x == y).toUInt64 + y

def binaryBooleanHelperOrder (x y : UInt64) : UInt64 :=
  let f := fun a b : UInt64 => a + 3 * b == y
  ((f x y) != (f y x)).toUInt64 + x

def rangeBinaryBooleanHelperStep (count seed : UInt64) : Id UInt64 := do
  let mut a := seed
  for i in [:count.toNat] do
    a := a + (let f := fun x y : UInt64 => x + 3 * y == a
              f i.toUInt64 seed || f seed i.toUInt64).toUInt64
  return a

def rangeBinaryBooleanHelperExit (count seed : UInt64) : Id UInt64 := do
  let mut a := seed
  for i in [:count.toNat] do
    a := a + i.toUInt64 + 1
    if (let f := fun x y : UInt64 => x + 3 * y == 7
        f a seed || f i.toUInt64 a) then break
  return a

def rangeBinaryBooleanHelperContinue (count seed : UInt64) : Id UInt64 := do
  let mut a := seed
  for i in [:count.toNat] do
    if (let f := fun x y : UInt64 => (pure (x + 3 * y == a) : Id Bool)
        Id.run (f i.toUInt64 seed) || Id.run (f seed a)) then continue
    a := a * 3 + i.toUInt64 + 1
  return a

def rangeBinaryBooleanHelperTail (count seed : UInt64) : Id UInt64 := do
  let mut a := seed
  for i in [:count.toNat] do
    a := a + i.toUInt64 + 1
  return a + (let f := fun x y : UInt64 =>
                let g := fun n : UInt64 => n == y
                g x || g seed
              f a seed && f seed a).toUInt64

def inputs : List (UInt64 × UInt64) :=
  [(0, 0), (1, 0), (0xffffffffffffffff, 0), (0, 1), (1, 1),
   (0xffffffffffffffff, 1), (0x8000000000000000, 2), (42, 3),
   (0xffffffffffffffff, 63), (0x8000000000000001, 64), (0xffffffffffffffff, 65),
   (0x0123456789abcdef, 0xffffffffffffffff), (3, 17), (17, 3)]

end BinaryBooleanHelperTest

run_elab do
  let env ← Lean.getEnv
  let cases : List (Lean.Name × (UInt64 → UInt64 → UInt64) × Bool) := [
    (`BinaryBooleanHelperTest.binaryBooleanHelperDirect, (fun (x y : UInt64) => BinaryBooleanHelperTest.binaryBooleanHelperDirect x y), false),
    (`BinaryBooleanHelperTest.binaryBooleanHelperRepeated, (fun (x y : UInt64) => BinaryBooleanHelperTest.binaryBooleanHelperRepeated x y), false),
    (`BinaryBooleanHelperTest.binaryBooleanHelperCapture, (fun (x y : UInt64) => BinaryBooleanHelperTest.binaryBooleanHelperCapture x y), false),
    (`BinaryBooleanHelperTest.binaryBooleanHelperNested, (fun (x y : UInt64) => BinaryBooleanHelperTest.binaryBooleanHelperNested x y), false),
    (`BinaryBooleanHelperTest.binaryBooleanHelperRetained, (fun (x y : UInt64) => BinaryBooleanHelperTest.binaryBooleanHelperRetained x y), false),
    (`BinaryBooleanHelperTest.binaryBooleanHelperUnused, (fun (x y : UInt64) => BinaryBooleanHelperTest.binaryBooleanHelperUnused x y), false),
    (`BinaryBooleanHelperTest.binaryBooleanHelperOrder, (fun (x y : UInt64) => BinaryBooleanHelperTest.binaryBooleanHelperOrder x y), false),
    (`BinaryBooleanHelperTest.rangeBinaryBooleanHelperStep, (fun (x y : UInt64) => BinaryBooleanHelperTest.rangeBinaryBooleanHelperStep x y), true),
    (`BinaryBooleanHelperTest.rangeBinaryBooleanHelperExit, (fun (x y : UInt64) => BinaryBooleanHelperTest.rangeBinaryBooleanHelperExit x y), true),
    (`BinaryBooleanHelperTest.rangeBinaryBooleanHelperContinue, (fun (x y : UInt64) => BinaryBooleanHelperTest.rangeBinaryBooleanHelperContinue x y), true),
    (`BinaryBooleanHelperTest.rangeBinaryBooleanHelperTail, (fun (x y : UInt64) => BinaryBooleanHelperTest.rangeBinaryBooleanHelperTail x y), true)]
  let mut comparisons : Nat := 0
  for (name, native, isRange) in cases do
    let some info := env.find? name | throwError "missing declaration"
    let some value := info.value? | throwError "missing body"
    let some func := LeanExe.Extract.Core.extractScalarFunc name (some "entry") info.type value |
      throwError "{name}: binary Boolean helper extraction failed"
    let module_ : LeanExe.IR.Module := { funcs := #[func] }
    let inputs := if isRange then
      ([0, 1, 2, 7, 16, 31] : List UInt64).flatMap fun n =>
        ([0, 1, 0x8000000000000000, 0xffffffffffffffff] : List UInt64).map fun seed => (n, seed)
      else BinaryBooleanHelperTest.inputs
    for (x, y) in inputs do
      let expected := native x y
      let actual := module_.evalFunc 0 [x, y]
      unless actual == expected do
        throwError "{name}({x}, {y}): native={expected}, IR={actual}"
      comparisons := comparisons + 1
  unless comparisons == 194 do throwError "unexpected comparison count {comparisons}"
  Lean.logInfo m!"{comparisons} native/binary Boolean helper IR comparisons passed"

import LeanExe.Extract.ScalarFunc

namespace BooleanHelperIdInputTest

def booleanHelperIdInputWord (x y : UInt64) : UInt64 :=
  (let f := fun n : Id UInt64 => (Id.run n) == y
   f x && f 0).toUInt64 + x

def booleanHelperIdInputBoolean (x y : UInt64) : UInt64 :=
  (let f := fun b : Id Bool => (Id.run b) != (x == y)
   f (x == 0) || f (y == 0)).toUInt64 + y

def booleanHelperIdInputNested (x y : UInt64) : UInt64 :=
  (let f := fun n : Id (Id UInt64) =>
    let g := fun b : Id (Id Bool) => (Id.run (Id.run b)) || y == 0
    g ((Id.run (Id.run n)) == y) && g false
   f x || f y).toUInt64 + x

def booleanHelperIdInputCapture (x y : UInt64) : UInt64 :=
  let saved := x + y
  (let f := fun n : Id UInt64 =>
     let g := fun b : Id Bool => (Id.run b) != (saved == y)
     g ((Id.run n) == saved) || g (x == 0)
   f x && f y).toUInt64 + y

def booleanHelperIdInputUnused (x y : UInt64) : UInt64 :=
  (let _unused := fun b : Id Bool =>
     let g := fun n : Id UInt64 => (Id.run n) == y
     (Id.run b) || g x || g 0
   x == y).toUInt64 + x

def booleanHelperIdInputProposition (x y : UInt64) : UInt64 :=
  if x < y ∧ (let f := fun n : Id UInt64 => (Id.run n) == y; f x || f y) then x + 7 else y + 3

def rangeBooleanHelperIdInputStep (count seed : UInt64) : Id UInt64 := do
  let mut a := seed
  for i in [:count.toNat] do
    a := a + (let f := fun n : Id UInt64 => (Id.run n) == a; f i.toUInt64 || f seed).toUInt64
  return a

def rangeBooleanHelperIdInputExit (count seed : UInt64) : Id UInt64 := do
  let mut a := seed
  for i in [:count.toNat] do
    a := a + i.toUInt64 + 1
    if (let f := fun b : Id Bool => (Id.run b) != (a == seed); f (decide (a > 7)) && f (i.toUInt64 == seed)) then break
  return a

def rangeBooleanHelperIdInputContinue (count seed : UInt64) : Id UInt64 := do
  let mut a := seed
  for i in [:count.toNat] do
    if (let f := fun n : Id (Id UInt64) => (Id.run (Id.run n)) == a; f i.toUInt64 || f seed) then continue
    a := a * 3 + i.toUInt64 + 1
  return a

def rangeBooleanHelperIdInputTail (count seed : UInt64) : Id UInt64 := do
  let mut a := seed
  for i in [:count.toNat] do
    a := a + i.toUInt64 + 1
  return a + (let f := fun b : Id Bool => (Id.run b) != (a == seed); f (a == 0) || f (seed == 0)).toUInt64

def inputs : List (UInt64 × UInt64) :=
  [(0, 0), (1, 0), (0xffffffffffffffff, 0), (0, 1), (1, 1),
   (0xffffffffffffffff, 1), (0x8000000000000000, 2), (42, 3),
   (0xffffffffffffffff, 63), (0x8000000000000001, 64), (0xffffffffffffffff, 65),
   (0x0123456789abcdef, 0xffffffffffffffff), (3, 17), (17, 3)]

end BooleanHelperIdInputTest

run_elab do
  let env ← Lean.getEnv
  let cases : List (Lean.Name × (UInt64 → UInt64 → UInt64) × Bool) := [
    (`BooleanHelperIdInputTest.booleanHelperIdInputWord, (fun (x y : UInt64) => BooleanHelperIdInputTest.booleanHelperIdInputWord x y), false),
    (`BooleanHelperIdInputTest.booleanHelperIdInputBoolean, (fun (x y : UInt64) => BooleanHelperIdInputTest.booleanHelperIdInputBoolean x y), false),
    (`BooleanHelperIdInputTest.booleanHelperIdInputNested, (fun (x y : UInt64) => BooleanHelperIdInputTest.booleanHelperIdInputNested x y), false),
    (`BooleanHelperIdInputTest.booleanHelperIdInputCapture, (fun (x y : UInt64) => BooleanHelperIdInputTest.booleanHelperIdInputCapture x y), false),
    (`BooleanHelperIdInputTest.booleanHelperIdInputUnused, (fun (x y : UInt64) => BooleanHelperIdInputTest.booleanHelperIdInputUnused x y), false),
    (`BooleanHelperIdInputTest.booleanHelperIdInputProposition, (fun (x y : UInt64) => BooleanHelperIdInputTest.booleanHelperIdInputProposition x y), false),
    (`BooleanHelperIdInputTest.rangeBooleanHelperIdInputStep, (fun (x y : UInt64) => BooleanHelperIdInputTest.rangeBooleanHelperIdInputStep x y), true),
    (`BooleanHelperIdInputTest.rangeBooleanHelperIdInputExit, (fun (x y : UInt64) => BooleanHelperIdInputTest.rangeBooleanHelperIdInputExit x y), true),
    (`BooleanHelperIdInputTest.rangeBooleanHelperIdInputContinue, (fun (x y : UInt64) => BooleanHelperIdInputTest.rangeBooleanHelperIdInputContinue x y), true),
    (`BooleanHelperIdInputTest.rangeBooleanHelperIdInputTail, (fun (x y : UInt64) => BooleanHelperIdInputTest.rangeBooleanHelperIdInputTail x y), true)]
  let mut comparisons : Nat := 0
  for (name, native, isRange) in cases do
    let some info := env.find? name | throwError "missing declaration"
    let some value := info.value? | throwError "missing body"
    let some func := LeanExe.Extract.Core.extractScalarFunc name (some "entry") info.type value |
      throwError "{name}: retained Id helper input extraction failed"
    let module_ : LeanExe.IR.Module := { funcs := #[func] }
    let inputs := if isRange then
      ([0, 1, 2, 7, 16, 31] : List UInt64).flatMap fun n =>
        ([0, 1, 0x8000000000000000, 0xffffffffffffffff] : List UInt64).map fun seed => (n, seed)
      else BooleanHelperIdInputTest.inputs
    for (x, y) in inputs do
      let expected := native x y
      let actual := module_.evalFunc 0 [x, y]
      unless actual == expected do
        throwError "{name}({x}, {y}): native={expected}, IR={actual}"
      comparisons := comparisons + 1
  unless comparisons == 180 do throwError "unexpected comparison count {comparisons}"
  Lean.logInfo m!"{comparisons} native/retained Id helper input IR comparisons passed"

import LeanExe.Extract.ScalarFunc

namespace BooleanHelperGeneralBodyTest

def booleanHelperBodyNested (x y : UInt64) : UInt64 :=
  (let f := fun n : UInt64 =>
    let g := fun k : UInt64 => k == y
    g n || g 0
   f x && f y).toUInt64 + x

def booleanHelperBodyWrapped (x y : UInt64) : UInt64 :=
  (let f := fun b : Bool => Id.run do
    let g := fun k : Bool => k || x == y
    return g b && g (y == 0)
   f (x == 0) || f (x == y)).toUInt64 + y

def booleanHelperBodyMixed (x y : UInt64) : UInt64 :=
  (let f := fun n : UInt64 =>
    let g := fun b : Bool => b || n == y
    g (n == 0) && g (y == 0)
   f x || f (x + y)).toUInt64 + x

def booleanHelperBodyCaptures (x y : UInt64) : UInt64 :=
  (let p := fun n : UInt64 => n == y
   let f := fun b : Bool =>
    let g := fun n : UInt64 => p n || b
    g x && g 0
   f (x == 0) || f (y == 0)).toUInt64 + y

def booleanHelperBodyUnused (x y : UInt64) : UInt64 :=
  (let _unused := fun n : UInt64 =>
    let g := fun k : UInt64 => k == y
    g n || g 0
   x == y).toUInt64 + x

def booleanHelperBodyChoice (x y : UInt64) : UInt64 :=
  (let f := fun n : UInt64 =>
    if _h : n < y then (let g := fun k : UInt64 => k % 3 == 0; g n || g y)
    else (let g := fun b : Bool => !b || y == 0; g (n == 0) && g (n == y))
   f x && f y).toUInt64 + x

def rangeHelperBodyStep (count seed : UInt64) : Id UInt64 := do
  let mut a := seed
  for i in [:count.toNat] do
    if (let f := fun n : UInt64 => (let g := fun k : UInt64 => k % 3 == 0; g n || g a); f a && f i.toUInt64) then
      a := a + i.toUInt64 + 7
    else a := a * 3 + 1
  return a

def rangeHelperBodyExit (count seed : UInt64) : Id UInt64 := do
  let mut a := seed
  for i in [:count.toNat] do
    a := a + i.toUInt64 + 1
    if _h : (let f := fun b : Bool => (let g := fun n : UInt64 => n % 7 == 0 || b; g a && g seed); f (i.toUInt64 == 0) || f (a == seed)) then break
  return a

def rangeHelperBodyContinue (count seed : UInt64) : Id UInt64 := do
  let mut a := seed
  for i in [:count.toNat] do
    if (let f := fun n : UInt64 => (let g := fun b : Bool => b || n == seed; g (n % 3 == 0) && g (a == 0)); f a || f i.toUInt64) then continue
    a := a * 3 + i.toUInt64 + 1
  return a

def rangeHelperBodyTail (count seed : UInt64) : Id UInt64 := do
  let mut a := seed
  for i in [:count.toNat] do
    a := a + i.toUInt64 + 1
  return (let f := fun b : Bool => Id.run do
    let g := fun n : UInt64 => n == seed || b
    return g a && g 0
   f (a == 0) || f (a == seed)).toUInt64 + a

def inputs : List (UInt64 × UInt64) :=
  [(0, 0), (1, 0), (0xffffffffffffffff, 0), (0, 1), (1, 1),
   (0xffffffffffffffff, 1), (0x8000000000000000, 2), (42, 3),
   (0xffffffffffffffff, 63), (0x8000000000000001, 64), (0xffffffffffffffff, 65),
   (0x0123456789abcdef, 0xffffffffffffffff), (3, 17), (17, 3)]

end BooleanHelperGeneralBodyTest

run_elab do
  let env ← Lean.getEnv
  let cases : List (Lean.Name × (UInt64 → UInt64 → UInt64) × Bool) := [
    (`BooleanHelperGeneralBodyTest.booleanHelperBodyNested, (fun (x y : UInt64) => BooleanHelperGeneralBodyTest.booleanHelperBodyNested x y), false),
    (`BooleanHelperGeneralBodyTest.booleanHelperBodyWrapped, (fun (x y : UInt64) => BooleanHelperGeneralBodyTest.booleanHelperBodyWrapped x y), false),
    (`BooleanHelperGeneralBodyTest.booleanHelperBodyMixed, (fun (x y : UInt64) => BooleanHelperGeneralBodyTest.booleanHelperBodyMixed x y), false),
    (`BooleanHelperGeneralBodyTest.booleanHelperBodyCaptures, (fun (x y : UInt64) => BooleanHelperGeneralBodyTest.booleanHelperBodyCaptures x y), false),
    (`BooleanHelperGeneralBodyTest.booleanHelperBodyUnused, (fun (x y : UInt64) => BooleanHelperGeneralBodyTest.booleanHelperBodyUnused x y), false),
    (`BooleanHelperGeneralBodyTest.booleanHelperBodyChoice, (fun (x y : UInt64) => BooleanHelperGeneralBodyTest.booleanHelperBodyChoice x y), false),
    (`BooleanHelperGeneralBodyTest.rangeHelperBodyStep, (fun (x y : UInt64) => BooleanHelperGeneralBodyTest.rangeHelperBodyStep x y), true),
    (`BooleanHelperGeneralBodyTest.rangeHelperBodyExit, (fun (x y : UInt64) => BooleanHelperGeneralBodyTest.rangeHelperBodyExit x y), true),
    (`BooleanHelperGeneralBodyTest.rangeHelperBodyContinue, (fun (x y : UInt64) => BooleanHelperGeneralBodyTest.rangeHelperBodyContinue x y), true),
    (`BooleanHelperGeneralBodyTest.rangeHelperBodyTail, (fun (x y : UInt64) => BooleanHelperGeneralBodyTest.rangeHelperBodyTail x y), true)]
  let mut comparisons : Nat := 0
  for (name, native, isRange) in cases do
    let some info := env.find? name | throwError "missing declaration"
    let some value := info.value? | throwError "missing body"
    let some func := LeanExe.Extract.Core.extractScalarFunc name (some "entry") info.type value |
      throwError "{name}: general Boolean helper body extraction failed"
    let module_ : LeanExe.IR.Module := { funcs := #[func] }
    let inputs := if isRange then
      ([0, 1, 2, 7, 16, 31] : List UInt64).flatMap fun n =>
        ([0, 1, 0x8000000000000000, 0xffffffffffffffff] : List UInt64).map fun seed => (n, seed)
      else BooleanHelperGeneralBodyTest.inputs
    for (x, y) in inputs do
      let expected := native x y
      let actual := module_.evalFunc 0 [x, y]
      unless actual == expected do
        throwError "{name}({x}, {y}): native={expected}, IR={actual}"
      comparisons := comparisons + 1
  unless comparisons == 180 do throwError "unexpected comparison count {comparisons}"
  Lean.logInfo m!"{comparisons} native/general Boolean helper body IR comparisons passed"

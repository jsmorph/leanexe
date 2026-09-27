import LeanExe.Extract.ScalarFunc

namespace PublicResultIdTest

def publicIdWord (x y : UInt64) : Id UInt64 := pure (x + y)

def publicIdNested (x y : UInt64) : Id (Id UInt64) :=
  pure (pure (if x < y then x / y else y % x))

def publicIdBind (x y : UInt64) : Id UInt64 := do
  let n ← pure (x + y)
  let flag ← pure (n == 0)
  return if flag then n + 3 else y - 7

def publicIdBool (x y : UInt64) : Id Bool := pure (x != y && x != 0)

def publicIdBoolNested (x y : UInt64) : Id (Id Bool) :=
  pure (pure (decide (x < y ∧ ¬ (y == 0))))

def publicIdBoolHelper (x y : UInt64) : Id Bool := pure (
  let f : UInt64 → Bool := fun n => n != y
  f (x + 1))

def rangePublicIdYield (count seed : UInt64) : Id UInt64 := do
  let mut a := seed
  for i in [:count.toNat] do
    a := a + i.toUInt64 + 1
  return a

def rangePublicIdExit (count seed : UInt64) : Id (Id UInt64) := pure (Id.run do
  let mut a := seed
  for i in [:count.toNat] do
    a := a + i.toUInt64 + 1
    if a % 7 == 0 then break
  return a)

def rangePublicIdContinue (count seed : UInt64) : Id UInt64 := do
  let mut a := seed
  for i in [:count.toNat] do
    if i.toUInt64 % 3 == 0 then continue
    a := a + i.toUInt64
  return a

def rangePublicIdCapture (count seed : UInt64) : Id UInt64 := do
  let f := fun b : Bool => b && seed != 0
  let g := fun b : Bool => if b then seed + 1 else seed
  let mut a := g (f (count == 0))
  for i in [:count.toNat] do
    a := a + g (f (a == seed)) + i.toUInt64
    if a % 7 == 0 then break
  return a

def inputs : List (UInt64 × UInt64) :=
  [(0, 0), (1, 0), (0xffffffffffffffff, 0), (0, 1), (1, 1),
   (0xffffffffffffffff, 1), (0x8000000000000000, 2), (42, 3),
   (0xffffffffffffffff, 63), (0x8000000000000001, 64), (0xffffffffffffffff, 65),
   (0x0123456789abcdef, 0xffffffffffffffff), (3, 17), (17, 3)]

end PublicResultIdTest

run_elab do
  let env ← Lean.getEnv
  let cases : List (Lean.Name × (UInt64 → UInt64 → UInt64) × Bool) := [
    (`PublicResultIdTest.publicIdWord, (fun x y => Id.run (PublicResultIdTest.publicIdWord x y)), false),
    (`PublicResultIdTest.publicIdNested, (fun x y => Id.run (PublicResultIdTest.publicIdNested x y)), false),
    (`PublicResultIdTest.publicIdBind, (fun x y => Id.run (PublicResultIdTest.publicIdBind x y)), false),
    (`PublicResultIdTest.publicIdBool, (fun x y => (PublicResultIdTest.publicIdBool x y).toUInt64), false),
    (`PublicResultIdTest.publicIdBoolNested, (fun x y => (PublicResultIdTest.publicIdBoolNested x y).toUInt64), false),
    (`PublicResultIdTest.publicIdBoolHelper, (fun x y => (PublicResultIdTest.publicIdBoolHelper x y).toUInt64), false),
    (`PublicResultIdTest.rangePublicIdYield, (fun x y => Id.run (PublicResultIdTest.rangePublicIdYield x y)), true),
    (`PublicResultIdTest.rangePublicIdExit, (fun x y => Id.run (PublicResultIdTest.rangePublicIdExit x y)), true),
    (`PublicResultIdTest.rangePublicIdContinue, (fun x y => Id.run (PublicResultIdTest.rangePublicIdContinue x y)), true),
    (`PublicResultIdTest.rangePublicIdCapture, (fun x y => Id.run (PublicResultIdTest.rangePublicIdCapture x y)), true)]
  let mut comparisons : Nat := 0
  for (name, native, isRange) in cases do
    let some info := env.find? name | throwError "missing declaration"
    let some value := info.value? | throwError "missing body"
    let some func := LeanExe.Extract.Core.extractScalarFunc name (some "entry") info.type value |
      throwError "{name}: reusable Boolean helper extraction failed"
    let module_ : LeanExe.IR.Module := { funcs := #[func] }
    let inputs := if isRange then
      ([0, 1, 2, 7, 16, 31] : List UInt64).flatMap fun n =>
        ([0, 1, 0x8000000000000000, 0xffffffffffffffff] : List UInt64).map fun seed => (n, seed)
      else PublicResultIdTest.inputs
    for (x, y) in inputs do
      let expected := native x y
      let actual := module_.evalFunc 0 [x, y]
      unless actual == expected do
        throwError "{name}({x}, {y}): native={expected}, IR={actual}"
      comparisons := comparisons + 1
  unless comparisons == 180 do throwError "unexpected comparison count {comparisons}"
  Lean.logInfo m!"{comparisons} native/public result-Id IR comparisons passed"

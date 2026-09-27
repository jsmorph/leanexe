import LeanExe.Extract.ScalarFunc

namespace ExtendedMixedGuardTest

def extendedMixedJunction (x y : UInt64) : UInt64 :=
  let f := fun b : Bool => b && x != y
  if (f (x == 0) && (x != y || f true)) ∧ x < y then x + 3 else y + 7

def extendedMixedChoice (x y : UInt64) : UInt64 :=
  let f := fun b : Bool => b && x != y
  if x ≤ y ∨ (if x < y then f true else f false) then x + 1 else y

def extendedMixedLet (x y : UInt64) : UInt64 :=
  let f := fun b : Bool => b && x != y
  if (Id.run (let flag := f (x == 0); let word := x + flag.toUInt64; f (word != y))) ∧ x < y then x + y else x - y

def extendedMixedBind (x y : UInt64) : UInt64 :=
  let f := fun b : Bool => b && x != y
  if x = 0 ∨ (Id.run do let flag ← pure (f (x == 0)); return f (!flag)) then x + 1 else y + 2

def extendedMixedWrapped (x y : UInt64) : UInt64 :=
  let f := fun b : Bool => b && x != y
  let saved := decide ((Id.run (pure (f true))) ∧ x < y)
  saved.toUInt64 + x

def extendedMixedRelation (x y : UInt64) : UInt64 :=
  let f := fun b : Bool => b && x != y
  let g := fun b : Bool => if (f b == b) ∧ x < y then f true else f false
  (g true).toUInt64 + (g false).toUInt64 + y

def rangeExtendedMixedStep (count seed : UInt64) : UInt64 := Id.run do
  let mut a := seed
  for i in [:count.toNat] do
    let f := fun b : Bool => b && a != 0
    if (f (i.toUInt64 != seed) || f true) ∧ i.toUInt64 < a then break
    a := a + i.toUInt64 + 1
  return a

def rangeExtendedMixedContinue (count seed : UInt64) : UInt64 := Id.run do
  let mut a := seed
  for i in [:count.toNat] do
    let f := fun n : UInt64 => n != seed
    if a = 0 ∨ (Id.run (let flag := f i.toUInt64; !flag)) then
      a := a + 3
      continue
    a := a + i.toUInt64 + 1
  return a

def rangeExtendedMixedOuter (count seed : UInt64) : UInt64 := Id.run do
  let f := fun b : Bool => b && seed != 0
  let g := fun n : UInt64 => n != seed
  let mut a := if (Id.run (pure (f true))) ∧ count < seed then seed + 1 else seed
  for i in [:count.toNat] do
    if (f (g i.toUInt64) != g a) ∧ a < seed then a := a + 2 else a := a + 1
  return a + (decide ((f true && g a) ∨ a = seed)).toUInt64

def rangeExtendedMixedHelper (count seed : UInt64) : UInt64 := Id.run do
  let f := fun b : Bool => b && seed != 0
  let g := fun b : Bool => if (Id.run do let flag ← pure (f b); return f (!flag)) ∧ seed < count then !b else b
  let mut a := seed
  for i in [:count.toNat] do
    if (if a = 0 then g true else g false) ∧ i.toUInt64 < a then break
    a := a + (f (g true)).toUInt64 + 1
  return a

def inputs : List (UInt64 × UInt64) :=
  [(0, 0), (1, 0), (0xffffffffffffffff, 0), (0, 1), (1, 1),
   (0xffffffffffffffff, 1), (0x8000000000000000, 2), (42, 3),
   (0xffffffffffffffff, 63), (0x8000000000000001, 64), (0xffffffffffffffff, 65),
   (0x0123456789abcdef, 0xffffffffffffffff), (3, 17), (17, 3)]

end ExtendedMixedGuardTest

run_elab do
  let env ← Lean.getEnv
  let cases : List (Lean.Name × (UInt64 → UInt64 → UInt64) × Bool) := [
    (`ExtendedMixedGuardTest.extendedMixedJunction, ExtendedMixedGuardTest.extendedMixedJunction, false),
    (`ExtendedMixedGuardTest.extendedMixedChoice, ExtendedMixedGuardTest.extendedMixedChoice, false),
    (`ExtendedMixedGuardTest.extendedMixedLet, ExtendedMixedGuardTest.extendedMixedLet, false),
    (`ExtendedMixedGuardTest.extendedMixedBind, ExtendedMixedGuardTest.extendedMixedBind, false),
    (`ExtendedMixedGuardTest.extendedMixedWrapped, ExtendedMixedGuardTest.extendedMixedWrapped, false),
    (`ExtendedMixedGuardTest.extendedMixedRelation, ExtendedMixedGuardTest.extendedMixedRelation, false),
    (`ExtendedMixedGuardTest.rangeExtendedMixedStep, ExtendedMixedGuardTest.rangeExtendedMixedStep, true),
    (`ExtendedMixedGuardTest.rangeExtendedMixedContinue, ExtendedMixedGuardTest.rangeExtendedMixedContinue, true),
    (`ExtendedMixedGuardTest.rangeExtendedMixedOuter, ExtendedMixedGuardTest.rangeExtendedMixedOuter, true),
    (`ExtendedMixedGuardTest.rangeExtendedMixedHelper, ExtendedMixedGuardTest.rangeExtendedMixedHelper, true)]
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
      else ExtendedMixedGuardTest.inputs
    for (x, y) in inputs do
      let expected := native x y
      let actual := module_.evalFunc 0 [x, y]
      unless actual == expected do
        throwError "{name}({x}, {y}): native={expected}, IR={actual}"
      comparisons := comparisons + 1
  unless comparisons == 180 do throwError "unexpected comparison count {comparisons}"
  Lean.logInfo m!"{comparisons} native/extended mixed-guard IR comparisons passed"

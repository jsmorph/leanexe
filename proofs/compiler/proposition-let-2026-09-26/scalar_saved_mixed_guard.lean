import LeanExe.Extract.ScalarFunc

namespace SavedMixedGuardTest

def savedMixedLeft (x y : UInt64) : UInt64 :=
  let flag := x != 0
  if flag ∧ x < y then x + 3 else y + 7

def savedMixedRight (x y : UInt64) : UInt64 :=
  let f := fun b : Bool => b && x != y
  let flag := f (x == 0)
  if x ≤ y ∨ flag then (f (!flag)).toUInt64 + x else y

def savedMixedPair (x y : UInt64) : UInt64 :=
  let a := x != 0
  let b := y == 0
  if a ∧ ¬ b then x + y else x - y

def savedMixedNegation (x y : UInt64) : UInt64 :=
  let flag := x != y
  if ¬ (flag ∧ ¬ (x = 0 ∨ !flag)) then x + 1 else y + 2

def savedMixedDecision (x y : UInt64) : UInt64 :=
  let flag := x != y
  let saved := decide ((flag ∧ x < y) ∨ (!flag ∧ y < x))
  saved.toUInt64 + x

def savedMixedHelper (x y : UInt64) : UInt64 :=
  let f := fun b : Bool => if b ∧ x < y then !b else b
  let a := x != 0
  (f a).toUInt64 + (f (!a)).toUInt64 + y

def rangeSavedMixedStep (count seed : UInt64) : UInt64 := Id.run do
  let mut a := seed
  for i in [:count.toNat] do
    let flag := a != 0
    if flag ∧ i.toUInt64 < a then break
    a := a + i.toUInt64 + 1
  return a

def rangeSavedMixedContinue (count seed : UInt64) : UInt64 := Id.run do
  let mut a := seed
  for i in [:count.toNat] do
    let flag := i.toUInt64 == seed
    if a = 0 ∨ !flag then
      a := a + 3
      continue
    a := a + i.toUInt64 + 1
  return a

def rangeSavedMixedOuter (count seed : UInt64) : UInt64 := Id.run do
  let flag := seed != 0
  let mut a := if flag ∧ count < seed then seed + 1 else seed
  for i in [:count.toNat] do
    let other := a == i.toUInt64
    if flag ∧ ¬ other then a := a + 2 else a := a + 1
  return a + (decide (flag ∨ a = seed)).toUInt64

def rangeSavedMixedHelper (count seed : UInt64) : UInt64 := Id.run do
  let f := fun b : Bool => if b ∧ seed < count then !b else b
  let mut a := seed
  for i in [:count.toNat] do
    let flag := f (a == 0)
    if ¬ (flag ∧ i.toUInt64 < a) then
      a := a + (f (!flag)).toUInt64 + 1
    else break
  return a

def inputs : List (UInt64 × UInt64) :=
  [(0, 0), (1, 0), (0xffffffffffffffff, 0), (0, 1), (1, 1),
   (0xffffffffffffffff, 1), (0x8000000000000000, 2), (42, 3),
   (0xffffffffffffffff, 63), (0x8000000000000001, 64), (0xffffffffffffffff, 65),
   (0x0123456789abcdef, 0xffffffffffffffff), (3, 17), (17, 3)]

end SavedMixedGuardTest

run_elab do
  let env ← Lean.getEnv
  let cases : List (Lean.Name × (UInt64 → UInt64 → UInt64) × Bool) := [
    (`SavedMixedGuardTest.savedMixedLeft, SavedMixedGuardTest.savedMixedLeft, false),
    (`SavedMixedGuardTest.savedMixedRight, SavedMixedGuardTest.savedMixedRight, false),
    (`SavedMixedGuardTest.savedMixedPair, SavedMixedGuardTest.savedMixedPair, false),
    (`SavedMixedGuardTest.savedMixedNegation, SavedMixedGuardTest.savedMixedNegation, false),
    (`SavedMixedGuardTest.savedMixedDecision, SavedMixedGuardTest.savedMixedDecision, false),
    (`SavedMixedGuardTest.savedMixedHelper, SavedMixedGuardTest.savedMixedHelper, false),
    (`SavedMixedGuardTest.rangeSavedMixedStep, SavedMixedGuardTest.rangeSavedMixedStep, true),
    (`SavedMixedGuardTest.rangeSavedMixedContinue, SavedMixedGuardTest.rangeSavedMixedContinue, true),
    (`SavedMixedGuardTest.rangeSavedMixedOuter, SavedMixedGuardTest.rangeSavedMixedOuter, true),
    (`SavedMixedGuardTest.rangeSavedMixedHelper, SavedMixedGuardTest.rangeSavedMixedHelper, true)]
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
      else SavedMixedGuardTest.inputs
    for (x, y) in inputs do
      let expected := native x y
      let actual := module_.evalFunc 0 [x, y]
      unless actual == expected do
        throwError "{name}({x}, {y}): native={expected}, IR={actual}"
      comparisons := comparisons + 1
  unless comparisons == 180 do throwError "unexpected comparison count {comparisons}"
  Lean.logInfo m!"{comparisons} native/saved mixed-guard IR comparisons passed"

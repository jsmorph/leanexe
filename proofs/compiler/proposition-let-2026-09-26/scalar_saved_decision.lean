import LeanExe.Extract.ScalarFunc

namespace SavedDecisionTest

def savedReannotatedDecide (x y : UInt64) : UInt64 :=
  let flag := @decide (@Eq (Id UInt64) ((x + y) % 7) (0))
    (instDecidableEqUInt64 ((x + y) % 7) (0))
  if flag then x + 1 else y * 3

def savedReannotatedNested (x y : UInt64) : UInt64 :=
  let flag := @decide ((@LT.lt (Id UInt64) instLTUInt64 (x + 1) (y * 7)) ∨ (@Ne (Id (Id UInt64)) ((x + y) % 5) (0)))
    (@instDecidableOr (@LT.lt (Id UInt64) instLTUInt64 (x + 1) (y * 7)) (@Ne (Id (Id UInt64)) ((x + y) % 5) (0))
      (UInt64.decLt (x + 1) (y * 7)) (@instDecidableNot (@Eq (Id (Id UInt64)) ((x + y) % 5) (0)) (instDecidableEqUInt64 ((x + y) % 5) (0))))
  if !(flag && (x == y)) then x ^^^ y else x + y

def savedReannotatedChoice (x y : UInt64) : UInt64 :=
  let flag := @ite Bool
    ((@LT.lt (Id UInt64) instLTUInt64 (x + 1) (y * 7)) ∨ (@Ne (Id (Id UInt64)) ((x + y) % 5) (0)))
    (@instDecidableOr (@LT.lt (Id UInt64) instLTUInt64 (x + 1) (y * 7)) (@Ne (Id (Id UInt64)) ((x + y) % 5) (0))
      (UInt64.decLt (x + 1) (y * 7)) (@instDecidableNot (@Eq (Id (Id UInt64)) ((x + y) % 5) (0)) (instDecidableEqUInt64 ((x + y) % 5) (0))))
    (x != 0) (y == 0)
  if flag then x + 1 else y * 3

def savedReannotatedDependentChoice (x y : UInt64) : UInt64 :=
  let flag := @dite Bool
    ((@LT.lt (Id UInt64) instLTUInt64 (x + 1) (y * 7)) ∨ (@Ne (Id (Id UInt64)) ((x + y) % 5) (0)))
    (@instDecidableOr (@LT.lt (Id UInt64) instLTUInt64 (x + 1) (y * 7)) (@Ne (Id (Id UInt64)) ((x + y) % 5) (0))
      (UInt64.decLt (x + 1) (y * 7)) (@instDecidableNot (@Eq (Id (Id UInt64)) ((x + y) % 5) (0)) (instDecidableEqUInt64 ((x + y) % 5) (0))))
    (fun _ => let other := x == 0; other || y != 0) (fun _ => let other := y == 0; other && x != 0)
  if flag then x + 1 else y * 3

def savedReannotatedDo (x y : UInt64) : UInt64 := Id.run do
  let flag ← pure (@decide ((@LT.lt (Id UInt64) instLTUInt64 (x + 1) (y * 7)) ∨ (@Ne (Id (Id UInt64)) ((x + y) % 5) (0)))
    (@instDecidableOr (@LT.lt (Id UInt64) instLTUInt64 (x + 1) (y * 7)) (@Ne (Id (Id UInt64)) ((x + y) % 5) (0))
      (UInt64.decLt (x + 1) (y * 7)) (@instDecidableNot (@Eq (Id (Id UInt64)) ((x + y) % 5) (0)) (instDecidableEqUInt64 ((x + y) % 5) (0)))))
  if flag then return x + 1 else return y * 3

def savedReannotatedHelper (x y : UInt64) : UInt64 :=
  let f := fun z : UInt64 =>
    let flag := @decide (@LE.le (Id (Id UInt64)) instLEUInt64 (z + 1) (y * 3))
      (UInt64.decLe (z + 1) (y * 3))
    if flag then z + 1 else z * 3
  f x + f y

def savedReannotatedCaptured (x y : UInt64) : UInt64 :=
  let flag := @decide ((@LT.lt (Id UInt64) instLTUInt64 (x + 1) (y * 7)) ∨ (@Ne (Id (Id UInt64)) ((x + y) % 5) (0)))
    (@instDecidableOr (@LT.lt (Id UInt64) instLTUInt64 (x + 1) (y * 7)) (@Ne (Id (Id UInt64)) ((x + y) % 5) (0))
      (UInt64.decLt (x + 1) (y * 7)) (@instDecidableNot (@Eq (Id (Id UInt64)) ((x + y) % 5) (0)) (instDecidableEqUInt64 ((x + y) % 5) (0))))
  let f := fun z : UInt64 => if flag then z + x else z * y
  f x + f y

def savedReannotatedUnused (x y : UInt64) : UInt64 :=
  let _flag := @decide ((@LT.lt (Id UInt64) instLTUInt64 (x + 1) (y * 7)) ∨ (@Ne (Id (Id UInt64)) ((x + y) % 5) (0)))
    (@instDecidableOr (@LT.lt (Id UInt64) instLTUInt64 (x + 1) (y * 7)) (@Ne (Id (Id UInt64)) ((x + y) % 5) (0))
      (UInt64.decLt (x + 1) (y * 7)) (@instDecidableNot (@Eq (Id (Id UInt64)) ((x + y) % 5) (0)) (instDecidableEqUInt64 ((x + y) % 5) (0))))
  x + y

def rangeSavedReannotated (count seed : UInt64) : UInt64 := Id.run do
  let mut a := seed
  for i in [:count.toNat] do
    let flag := @decide (@LT.lt (Id (Id UInt64)) instLTUInt64 (UInt64.ofNat i + 1) (seed % 7))
      (UInt64.decLt (UInt64.ofNat i + 1) (seed % 7))
    if flag then continue
    a := a + UInt64.ofNat i + 1
    if a % 5 == 0 then break
  return a

def rangeSavedReannotatedChoice (count seed : UInt64) : UInt64 :=
  forIn (m := Id) [:count.toNat] seed fun i a =>
    let flag := @ite Bool
      ((@GE.ge (Id (Id UInt64)) instLEUInt64 (UInt64.ofNat i + 1) (seed % 7)) ∧ (@Ne (Id UInt64) ((a + UInt64.ofNat i) % 5) (0)))
      (@instDecidableAnd (@GE.ge (Id (Id UInt64)) instLEUInt64 (UInt64.ofNat i + 1) (seed % 7)) (@Ne (Id UInt64) ((a + UInt64.ofNat i) % 5) (0))
        (UInt64.decLe (seed % 7) (UInt64.ofNat i + 1)) (@instDecidableNot (@Eq (Id UInt64) ((a + UInt64.ofNat i) % 5) (0)) (instDecidableEqUInt64 ((a + UInt64.ofNat i) % 5) (0))))
      (a == 0) (seed != 0)
    if flag then pure (.done (a + UInt64.ofNat i))
    else pure (.yield (a * 3 + UInt64.ofNat i))

def rangeSavedReannotatedDependentChoice (count seed : UInt64) : UInt64 :=
  forIn (m := Id) [:count.toNat] seed fun i a =>
    let flag := @dite Bool
      ((@GE.ge (Id (Id UInt64)) instLEUInt64 (UInt64.ofNat i + 1) (seed % 7)) ∧ (@Ne (Id UInt64) ((a + UInt64.ofNat i) % 5) (0)))
      (@instDecidableAnd (@GE.ge (Id (Id UInt64)) instLEUInt64 (UInt64.ofNat i + 1) (seed % 7)) (@Ne (Id UInt64) ((a + UInt64.ofNat i) % 5) (0))
        (UInt64.decLe (seed % 7) (UInt64.ofNat i + 1)) (@instDecidableNot (@Eq (Id UInt64) ((a + UInt64.ofNat i) % 5) (0)) (instDecidableEqUInt64 ((a + UInt64.ofNat i) % 5) (0))))
      (fun _ => a == 0) (fun _ => seed != 0)
    if flag then pure (.done (a + UInt64.ofNat i))
    else pure (.yield (a * 3 + UInt64.ofNat i))

def inputs : List (UInt64 × UInt64) :=
  [(0, 0), (1, 0), (0xffffffffffffffff, 0), (0, 1), (1, 1),
   (0xffffffffffffffff, 1), (0x8000000000000000, 2), (42, 3),
   (0xffffffffffffffff, 63), (0x8000000000000001, 64), (0xffffffffffffffff, 65),
   (0x0123456789abcdef, 0xffffffffffffffff), (3, 17), (17, 3)]

end SavedDecisionTest

run_elab do
  let env ← Lean.getEnv
  let cases : List (Lean.Name × (UInt64 → UInt64 → UInt64) × Bool) := [
    (`SavedDecisionTest.savedReannotatedDecide, SavedDecisionTest.savedReannotatedDecide, false),
    (`SavedDecisionTest.savedReannotatedNested, SavedDecisionTest.savedReannotatedNested, false),
    (`SavedDecisionTest.savedReannotatedChoice, SavedDecisionTest.savedReannotatedChoice, false),
    (`SavedDecisionTest.savedReannotatedDependentChoice, SavedDecisionTest.savedReannotatedDependentChoice, false),
    (`SavedDecisionTest.savedReannotatedDo, SavedDecisionTest.savedReannotatedDo, false),
    (`SavedDecisionTest.savedReannotatedHelper, SavedDecisionTest.savedReannotatedHelper, false),
    (`SavedDecisionTest.savedReannotatedCaptured, SavedDecisionTest.savedReannotatedCaptured, false),
    (`SavedDecisionTest.savedReannotatedUnused, SavedDecisionTest.savedReannotatedUnused, false),
    (`SavedDecisionTest.rangeSavedReannotated, SavedDecisionTest.rangeSavedReannotated, true),
    (`SavedDecisionTest.rangeSavedReannotatedChoice, SavedDecisionTest.rangeSavedReannotatedChoice, true),
    (`SavedDecisionTest.rangeSavedReannotatedDependentChoice, SavedDecisionTest.rangeSavedReannotatedDependentChoice, true)]
  let mut comparisons : Nat := 0
  for (name, native, isRange) in cases do
    let some info := env.find? name | throwError "missing declaration"
    let some value := info.value? | throwError "missing body"
    let some func := LeanExe.Extract.Core.extractScalarFunc name (some "entry") info.type value |
      throwError "{name}: reannotated comparison extraction failed"
    let module_ : LeanExe.IR.Module := { funcs := #[func] }
    let inputs := if isRange then
      ([0, 1, 2, 7, 16, 31] : List UInt64).flatMap fun n =>
        ([0, 1, 0x8000000000000000, 0xffffffffffffffff] : List UInt64).map fun seed => (n, seed)
      else SavedDecisionTest.inputs
    for (x, y) in inputs do
      let expected := native x y
      let actual := module_.evalFunc 0 [x, y]
      unless actual == expected do
        throwError "{name}({x}, {y}): native={expected}, IR={actual}"
      comparisons := comparisons + 1
  unless comparisons == 184 do throwError "unexpected comparison count {comparisons}"
  Lean.logInfo m!"{comparisons} native/saved-decision IR comparisons passed"

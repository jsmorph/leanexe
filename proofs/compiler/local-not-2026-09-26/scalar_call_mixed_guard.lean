import LeanExe.Extract.ScalarFunc

namespace CallMixedGuardTest

def callMixedBool (x y : UInt64) : UInt64 :=
  let f := fun b : Bool => b && x != y
  if f (x == 0) ∧ x < y then x + 3 else y + 7

def callMixedWord (x y : UInt64) : UInt64 :=
  let f := fun n : UInt64 => n != x
  if x ≤ y ∨ f (x + y) then (f y).toUInt64 + x else y

def callMixedPair (x y : UInt64) : UInt64 :=
  let f := fun b : Bool => b && x != y
  let g := fun n : UInt64 => n != x
  if f true ∧ ¬ g y then x + y else x - y

def callMixedNegation (x y : UInt64) : UInt64 :=
  let f := fun b : Bool => b && x != y
  let g := fun n : UInt64 => n != x
  if ¬ (f (g y) ∧ ¬ (x = 0 ∨ !f true)) then x + 1 else y + 2

def callMixedDecision (x y : UInt64) : UInt64 :=
  let f := fun b : Bool => b && x != y
  let g := fun n : UInt64 => n != x
  let saved := decide ((f (x == 0) ∧ x < y) ∨ (!g y ∧ y < x))
  saved.toUInt64 + x

def callMixedHelper (x y : UInt64) : UInt64 :=
  let f := fun b : Bool => b && x != y
  let g := fun n : UInt64 => if f (n == 0) ∧ n < x then f true else f false
  (g x).toUInt64 + (g y).toUInt64 + y

def rangeCallMixedStep (count seed : UInt64) : UInt64 := Id.run do
  let mut a := seed
  for i in [:count.toNat] do
    let f := fun b : Bool => b && a != 0
    if f (i.toUInt64 != seed) ∧ i.toUInt64 < a then break
    a := a + i.toUInt64 + 1
  return a

def rangeCallMixedContinue (count seed : UInt64) : UInt64 := Id.run do
  let mut a := seed
  for i in [:count.toNat] do
    let f := fun n : UInt64 => n != seed
    if a = 0 ∨ !f i.toUInt64 then
      a := a + 3
      continue
    a := a + i.toUInt64 + 1
  return a

def rangeCallMixedOuter (count seed : UInt64) : UInt64 := Id.run do
  let f := fun b : Bool => b && seed != 0
  let g := fun n : UInt64 => n != seed
  let mut a := if f true ∧ count < seed then seed + 1 else seed
  for i in [:count.toNat] do
    if f (g i.toUInt64) ∧ ¬ g a then a := a + 2 else a := a + 1
  return a + (decide (f true ∨ a = seed)).toUInt64

def rangeCallMixedHelper (count seed : UInt64) : UInt64 := Id.run do
  let f := fun b : Bool => b && seed != 0
  let g := fun b : Bool => if f b ∧ seed < count then !b else b
  let mut a := seed
  for i in [:count.toNat] do
    if ¬ (g (a == 0) ∧ i.toUInt64 < a) then
      a := a + (f (g true)).toUInt64 + 1
    else break
  return a

def inputs : List (UInt64 × UInt64) :=
  [(0, 0), (1, 0), (0xffffffffffffffff, 0), (0, 1), (1, 1),
   (0xffffffffffffffff, 1), (0x8000000000000000, 2), (42, 3),
   (0xffffffffffffffff, 63), (0x8000000000000001, 64), (0xffffffffffffffff, 65),
   (0x0123456789abcdef, 0xffffffffffffffff), (3, 17), (17, 3)]

end CallMixedGuardTest

run_elab do
  let env ← Lean.getEnv
  let cases : List (Lean.Name × (UInt64 → UInt64 → UInt64) × Bool) := [
    (`CallMixedGuardTest.callMixedBool, CallMixedGuardTest.callMixedBool, false),
    (`CallMixedGuardTest.callMixedWord, CallMixedGuardTest.callMixedWord, false),
    (`CallMixedGuardTest.callMixedPair, CallMixedGuardTest.callMixedPair, false),
    (`CallMixedGuardTest.callMixedNegation, CallMixedGuardTest.callMixedNegation, false),
    (`CallMixedGuardTest.callMixedDecision, CallMixedGuardTest.callMixedDecision, false),
    (`CallMixedGuardTest.callMixedHelper, CallMixedGuardTest.callMixedHelper, false),
    (`CallMixedGuardTest.rangeCallMixedStep, CallMixedGuardTest.rangeCallMixedStep, true),
    (`CallMixedGuardTest.rangeCallMixedContinue, CallMixedGuardTest.rangeCallMixedContinue, true),
    (`CallMixedGuardTest.rangeCallMixedOuter, CallMixedGuardTest.rangeCallMixedOuter, true),
    (`CallMixedGuardTest.rangeCallMixedHelper, CallMixedGuardTest.rangeCallMixedHelper, true)]
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
      else CallMixedGuardTest.inputs
    for (x, y) in inputs do
      let expected := native x y
      let actual := module_.evalFunc 0 [x, y]
      unless actual == expected do
        throwError "{name}({x}, {y}): native={expected}, IR={actual}"
      comparisons := comparisons + 1
  unless comparisons == 180 do throwError "unexpected comparison count {comparisons}"
  Lean.logInfo m!"{comparisons} native/call mixed-guard IR comparisons passed"

import LeanExe.Extract.ScalarFunc

namespace BooleanPredicateStepTest

def rangeBooleanPredicateBreak (count seed : UInt64) : UInt64 := Id.run do
  let mut a := seed
  for i in [:count.toNat] do
    let f := fun b : Bool => b || a == 0
    a := a + UInt64.ofNat i
    if (f (a % 7 == 0)).toUInt64 == 1 then break
  return a

def rangeBooleanPredicateContinue (count seed : UInt64) : UInt64 := Id.run do
  let mut a := seed
  for i in [:count.toNat] do
    let f := fun b : Bool => b && a != seed
    if (f (UInt64.ofNat i % 3 == 0)).toUInt64 != 0 then continue
    a := a * 3 + UInt64.ofNat i + 1
  return a

def rangeBooleanPredicateCapture (count seed : UInt64) : UInt64 := Id.run do
  let mut a := seed
  for i in [:count.toNat] do
    let saved := a
    let flag := a != 0
    let f := fun b : Bool => flag && (b || saved % 11 == 0)
    a := a + UInt64.ofNat i
    if (f (a == saved)).toUInt64 == 1 then break
  return a

def rangeBooleanPredicateNested (count seed : UInt64) : UInt64 :=
  forIn (m := Id) [:count.toNat] seed fun i a =>
    let f := fun b : Bool => !b
    let g := fun b : Bool => (f b).toUInt64 == 0
    if (g (a % 5 == 0)).toUInt64 == 1 then pure (.done (a + 1))
    else pure (.yield (a * 3 + UInt64.ofNat i))

def rangeBooleanPredicateStepHelper (count seed : UInt64) : UInt64 :=
  forIn (m := Id) [:count.toNat] seed fun i a =>
    let f : Bool → Id (Id Bool) := fun b => b && a != 0
    let finish := fun n : UInt64 =>
      if (f (n % 7 == 0)).toUInt64 == 1 then ForInStep.done (n + a) else .yield (n * 3)
    finish (a + UInt64.ofNat i)

def rangeBooleanPredicateUnused (count seed : UInt64) : UInt64 :=
  forIn (m := Id) [:count.toNat] seed fun i a =>
    let _f := fun b : Bool => b && a / seed == 0
    pure (.yield (a + UInt64.ofNat i))

def inputs : List (UInt64 × UInt64) :=
  ([0, 1, 2, 7, 16, 31] : List UInt64).flatMap fun n =>
    ([0, 1, 0x8000000000000000, 0xffffffffffffffff] : List UInt64).map fun seed => (n, seed)

end BooleanPredicateStepTest

run_elab do
  let env ← Lean.getEnv
  let cases : List (Lean.Name × (UInt64 → UInt64 → UInt64)) := [
    (`BooleanPredicateStepTest.rangeBooleanPredicateBreak, BooleanPredicateStepTest.rangeBooleanPredicateBreak),
    (`BooleanPredicateStepTest.rangeBooleanPredicateContinue, BooleanPredicateStepTest.rangeBooleanPredicateContinue),
    (`BooleanPredicateStepTest.rangeBooleanPredicateCapture, BooleanPredicateStepTest.rangeBooleanPredicateCapture),
    (`BooleanPredicateStepTest.rangeBooleanPredicateNested, BooleanPredicateStepTest.rangeBooleanPredicateNested),
    (`BooleanPredicateStepTest.rangeBooleanPredicateStepHelper, BooleanPredicateStepTest.rangeBooleanPredicateStepHelper),
    (`BooleanPredicateStepTest.rangeBooleanPredicateUnused, BooleanPredicateStepTest.rangeBooleanPredicateUnused)]
  let mut comparisons : Nat := 0
  for (name, native) in cases do
    let some info := env.find? name | throwError "missing declaration"
    let some value := info.value? | throwError "missing body"
    let some func := LeanExe.Extract.Core.extractScalarFunc name (some "entry") info.type value |
      throwError "{name}: Boolean-input step predicate extraction failed"
    let module_ : LeanExe.IR.Module := { funcs := #[func] }
    for (x, y) in BooleanPredicateStepTest.inputs do
      let expected := native x y
      let actual := module_.evalFunc 0 [x, y]
      unless actual == expected do
        throwError "{name}({x}, {y}): native={expected}, IR={actual}"
      comparisons := comparisons + 1
  unless comparisons == 144 do throwError "unexpected comparison count {comparisons}"
  Lean.logInfo m!"{comparisons} native/Boolean-input step predicate IR comparisons passed"

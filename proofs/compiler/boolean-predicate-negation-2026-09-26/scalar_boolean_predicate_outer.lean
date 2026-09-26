import LeanExe.Extract.ScalarFunc

namespace OuterBooleanPredicateTest

def rangeOuterBooleanPredicateBounds (count seed : UInt64) : UInt64 := Id.run do
  let f := fun b : Bool => b || seed == 0
  let stop := count + (f false).toUInt64
  let mut a := seed + (f (count == 0)).toUInt64
  for i in [:stop.toNat] do
    if (f (a % 7 == 0)).toUInt64 == 1 then break
    a := a + UInt64.ofNat i + 1
  return a + (f (a == seed)).toUInt64

def rangeOuterBooleanPredicateCapture (count seed : UInt64) : UInt64 := Id.run do
  let flag := seed != 0
  let shift := fun n : UInt64 => n + seed
  let f := fun b : Bool => flag && (b || shift seed % 7 == 0)
  let mut a := seed
  for i in [:count.toNat] do
    if (f (UInt64.ofNat i % 3 == 0)).toUInt64 != 0 then continue
    a := a * 3 + UInt64.ofNat i + 1
  return a + (f false).toUInt64

def rangeOuterBooleanPredicateNested (count seed : UInt64) : UInt64 := Id.run do
  let f := fun b : Bool => !b
  let g := fun b : Bool => (f b).toUInt64 == 0
  let mut a := seed + 1
  for i in [:count.toNat] do
    let h := fun b : Bool => (g b).toUInt64 == 1 && a != seed
    if (h (a % 5 == 0)).toUInt64 == 1 then break
    a := a + UInt64.ofNat i + 1
  return a + (g (a == seed)).toUInt64

def rangeOuterBooleanPredicateShadow (count seed : UInt64) : UInt64 := Id.run do
  let f := fun b : Bool => b || seed == 0
  let saved := (f (count == 0)).toUInt64
  let f := fun b : Bool => saved != 0 || b
  let mut a := seed
  for i in [:count.toNat] do
    if (f (UInt64.ofNat i % 3 == 0)).toUInt64 == 1 then continue
    a := a * 3 + (f (a == seed)).toUInt64
  return a

def rangeOuterBooleanPredicateUnused (count seed : UInt64) : UInt64 := Id.run do
  let _f := fun b : Bool => b && count / seed == 0
  let mut a := seed
  for i in [:count.toNat] do
    a := a + UInt64.ofNat i
  return a

def rangeOuterBooleanPredicateScalarHelper (count seed : UInt64) : UInt64 := Id.run do
  let f := fun b : Bool => b && seed != 0
  let g := fun n : UInt64 => if (f (n % 7 == 0)).toUInt64 == 1 then n + seed else n * 3
  let mut a := seed
  for i in [:count.toNat] do
    a := g (a + UInt64.ofNat i)
    if (f (a % 7 == 0)).toUInt64 == 1 then break
  return g a

def rangeOuterBooleanPredicateId (count seed : UInt64) : UInt64 := Id.run do
  let f : Bool → Id (Id Bool) := fun b => b || count == 0
  let initial ← pure (seed + (f false).toUInt64)
  let mut a := initial
  for i in [:count.toNat] do
    let converted ← pure (f (a == seed)).toUInt64
    if converted == 1 then break
    a := a + UInt64.ofNat i
  return a + (f (a == count)).toUInt64

def rangeOuterBooleanPredicateStride (count seed : UInt64) : UInt64 := Id.run do
  let f := fun b : Bool => b && seed != 0
  let first := (f (seed % 5 == 0)).toUInt64
  let mut a := seed
  for i in [first.toNat:count.toNat:3] do
    a := a + UInt64.ofNat i
    if (f (a % 7 == 0)).toUInt64 == 1 then break
  return a

def inputs : List (UInt64 × UInt64) :=
  ([0, 1, 2, 7, 16, 31] : List UInt64).flatMap fun n =>
    ([0, 1, 0x8000000000000000, 0xffffffffffffffff] : List UInt64).map fun seed => (n, seed)

end OuterBooleanPredicateTest

run_elab do
  let env ← Lean.getEnv
  let cases : List (Lean.Name × (UInt64 → UInt64 → UInt64)) := [
    (`OuterBooleanPredicateTest.rangeOuterBooleanPredicateBounds, OuterBooleanPredicateTest.rangeOuterBooleanPredicateBounds),
    (`OuterBooleanPredicateTest.rangeOuterBooleanPredicateCapture, OuterBooleanPredicateTest.rangeOuterBooleanPredicateCapture),
    (`OuterBooleanPredicateTest.rangeOuterBooleanPredicateNested, OuterBooleanPredicateTest.rangeOuterBooleanPredicateNested),
    (`OuterBooleanPredicateTest.rangeOuterBooleanPredicateShadow, OuterBooleanPredicateTest.rangeOuterBooleanPredicateShadow),
    (`OuterBooleanPredicateTest.rangeOuterBooleanPredicateUnused, OuterBooleanPredicateTest.rangeOuterBooleanPredicateUnused),
    (`OuterBooleanPredicateTest.rangeOuterBooleanPredicateScalarHelper, OuterBooleanPredicateTest.rangeOuterBooleanPredicateScalarHelper),
    (`OuterBooleanPredicateTest.rangeOuterBooleanPredicateId, OuterBooleanPredicateTest.rangeOuterBooleanPredicateId),
    (`OuterBooleanPredicateTest.rangeOuterBooleanPredicateStride, OuterBooleanPredicateTest.rangeOuterBooleanPredicateStride)]
  let mut comparisons : Nat := 0
  for (name, native) in cases do
    let some info := env.find? name | throwError "missing declaration"
    let some value := info.value? | throwError "missing body"
    let some func := LeanExe.Extract.Core.extractScalarFunc name (some "entry") info.type value |
      throwError "{name}: outer Boolean-input predicate extraction failed"
    let module_ : LeanExe.IR.Module := { funcs := #[func] }
    for (x, y) in OuterBooleanPredicateTest.inputs do
      let expected := native x y
      let actual := module_.evalFunc 0 [x, y]
      unless actual == expected do
        throwError "{name}({x}, {y}): native={expected}, IR={actual}"
      comparisons := comparisons + 1
  unless comparisons == 192 do throwError "unexpected comparison count {comparisons}"
  Lean.logInfo m!"{comparisons} native/outer Boolean-input predicate IR comparisons passed"

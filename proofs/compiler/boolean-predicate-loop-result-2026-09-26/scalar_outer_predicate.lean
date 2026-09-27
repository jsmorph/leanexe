import LeanExe.Extract.ScalarFunc

namespace OuterPredicateTest

def rangeOuterPredicateBounds (count seed : UInt64) : UInt64 := Id.run do
  let f := fun n : UInt64 => n == seed
  let stop := count + (f 0).toUInt64
  let mut a := seed + (f count).toUInt64
  for i in [:stop.toNat] do
    if f a || f (UInt64.ofNat i) then break
    a := a + UInt64.ofNat i + 1
  return a + (f a).toUInt64

def rangeOuterPredicateCapture (count seed : UInt64) : UInt64 := Id.run do
  let flag := seed != 0
  let shift := fun n : UInt64 => n + seed
  let f := fun n : UInt64 => flag && shift n % 7 == 0
  let mut a := seed
  for i in [:count.toNat] do
    if f a && !f (UInt64.ofNat i) then continue
    a := a * 3 + UInt64.ofNat i + 1
  return a + (f seed).toUInt64

def rangeOuterPredicateNested (count seed : UInt64) : UInt64 := Id.run do
  let f := fun n : UInt64 => n == seed
  let g := fun n : UInt64 => f n || f (n + 1)
  let mut a := seed + 1
  for i in [:count.toNat] do
    let h := fun n : UInt64 => g n && !f (n + a)
    if h a || h (UInt64.ofNat i) then break
    a := a + UInt64.ofNat i + 1
  return a + (g a).toUInt64

def rangeOuterPredicateShadow (count seed : UInt64) : UInt64 := Id.run do
  let f := fun n : UInt64 => n == seed
  let saved := f count
  let f := fun n : UInt64 => saved || n % 3 == 0
  let mut a := seed
  for i in [:count.toNat] do
    if f (UInt64.ofNat i) then continue
    a := a * 3 + (f a).toUInt64
  return a

def rangeOuterPredicateUnused (count seed : UInt64) : UInt64 := Id.run do
  let _f := fun n : UInt64 => n / seed == count
  let mut a := seed
  for i in [:count.toNat] do
    a := a + UInt64.ofNat i
  return a

def rangeOuterPredicateScalarHelper (count seed : UInt64) : UInt64 := Id.run do
  let f := fun n : UInt64 => n % 7 == 0
  let g := fun n : UInt64 => if f n then n + seed else n * 3
  let mut a := seed
  for i in [:count.toNat] do
    a := g (a + UInt64.ofNat i)
    if f a then break
  return g a

def rangeOuterPredicateId (count seed : UInt64) : UInt64 := Id.run do
  let f : UInt64 → Id (Id Bool) := fun n => n != seed
  let initial ← pure (if (show Bool from f count) then seed + 1 else seed)
  let mut a := initial
  for i in [:count.toNat] do
    let flag ← pure (f a && f (UInt64.ofNat i))
    if flag then break
    a := a + UInt64.ofNat i
  return a + (f a).toUInt64

def rangeOuterPredicateStride (count seed : UInt64) : UInt64 := Id.run do
  let f := fun n : UInt64 => n % 5 == 0
  let first := (f seed).toUInt64
  let mut a := seed
  for i in [first.toNat:count.toNat:3] do
    a := a + UInt64.ofNat i
    if f a || f (a + 1) then break
  return a

def inputs : List (UInt64 × UInt64) :=
  ([0, 1, 2, 7, 16, 31] : List UInt64).flatMap fun n =>
    ([0, 1, 0x8000000000000000, 0xffffffffffffffff] : List UInt64).map fun seed => (n, seed)

end OuterPredicateTest

run_elab do
  let env ← Lean.getEnv
  let cases : List (Lean.Name × (UInt64 → UInt64 → UInt64)) := [
    (`OuterPredicateTest.rangeOuterPredicateBounds, OuterPredicateTest.rangeOuterPredicateBounds),
    (`OuterPredicateTest.rangeOuterPredicateCapture, OuterPredicateTest.rangeOuterPredicateCapture),
    (`OuterPredicateTest.rangeOuterPredicateNested, OuterPredicateTest.rangeOuterPredicateNested),
    (`OuterPredicateTest.rangeOuterPredicateShadow, OuterPredicateTest.rangeOuterPredicateShadow),
    (`OuterPredicateTest.rangeOuterPredicateUnused, OuterPredicateTest.rangeOuterPredicateUnused),
    (`OuterPredicateTest.rangeOuterPredicateScalarHelper, OuterPredicateTest.rangeOuterPredicateScalarHelper),
    (`OuterPredicateTest.rangeOuterPredicateId, OuterPredicateTest.rangeOuterPredicateId),
    (`OuterPredicateTest.rangeOuterPredicateStride, OuterPredicateTest.rangeOuterPredicateStride)]
  let mut comparisons : Nat := 0
  for (name, native) in cases do
    let some info := env.find? name | throwError "missing declaration"
    let some value := info.value? | throwError "missing body"
    let some func := LeanExe.Extract.Core.extractScalarFunc name (some "entry") info.type value |
      throwError "{name}: reusable Boolean helper extraction failed"
    let module_ : LeanExe.IR.Module := { funcs := #[func] }
    for (x, y) in OuterPredicateTest.inputs do
      let expected := native x y
      let actual := module_.evalFunc 0 [x, y]
      unless actual == expected do
        throwError "{name}({x}, {y}): native={expected}, IR={actual}"
      comparisons := comparisons + 1
  unless comparisons == 192 do throwError "unexpected comparison count {comparisons}"
  Lean.logInfo m!"{comparisons} native/outer-predicate IR comparisons passed"

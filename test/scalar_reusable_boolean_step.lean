import LeanExe.Extract.ScalarFunc

namespace ReusableBooleanStepTest

def rangeReusableBooleanBreak (count seed : UInt64) : UInt64 := Id.run do
  let mut a := seed
  for i in [:count.toNat] do
    let f := fun n : UInt64 => n % 7 == 0
    a := a + UInt64.ofNat i
    if f a || f (a + 1) then break
  return a

def rangeReusableBooleanContinue (count seed : UInt64) : UInt64 := Id.run do
  let mut a := seed
  for i in [:count.toNat] do
    let f := fun n : UInt64 => n % 3 == 0
    if f (UInt64.ofNat i) && !f a then continue
    a := a * 3 + UInt64.ofNat i + 1
  return a

def rangeReusableBooleanCapture (count seed : UInt64) : UInt64 := Id.run do
  let mut a := seed
  for i in [:count.toNat] do
    let saved := a
    let flag := a != 0
    let shift := fun n : UInt64 => n + saved
    let f := fun n : UInt64 => flag && shift n % 11 == 0
    a := a + UInt64.ofNat i
    if f a || f saved then break
  return a

def rangeReusableBooleanNested (count seed : UInt64) : UInt64 :=
  forIn (m := Id) [:count.toNat] seed fun i a =>
    let f := fun n : UInt64 => n % 5 == 0
    let g := fun n : UInt64 => !f n && f (n + 1)
    if g a || g (UInt64.ofNat i) then pure (.done (a + 1))
    else pure (.yield (a * 3 + UInt64.ofNat i))

def rangeReusableBooleanStepHelper (count seed : UInt64) : UInt64 :=
  forIn (m := Id) [:count.toNat] seed fun i a =>
    let f : UInt64 → Id Bool := fun n => n % 7 == 0
    let finish := fun n : UInt64 =>
      if f n && !f (n + 1) then ForInStep.done (n + a) else .yield (n * 3)
    finish (a + UInt64.ofNat i)

def rangeReusableBooleanUnused (count seed : UInt64) : UInt64 :=
  forIn (m := Id) [:count.toNat] seed fun i a =>
    let _f := fun n : UInt64 => n / a == seed
    pure (.yield (a + UInt64.ofNat i))

def inputs : List (UInt64 × UInt64) :=
  ([0, 1, 2, 7, 16, 31] : List UInt64).flatMap fun n =>
    ([0, 1, 0x8000000000000000, 0xffffffffffffffff] : List UInt64).map fun seed => (n, seed)

end ReusableBooleanStepTest

run_elab do
  let env ← Lean.getEnv
  let cases : List (Lean.Name × (UInt64 → UInt64 → UInt64)) := [
    (`ReusableBooleanStepTest.rangeReusableBooleanBreak, ReusableBooleanStepTest.rangeReusableBooleanBreak),
    (`ReusableBooleanStepTest.rangeReusableBooleanContinue, ReusableBooleanStepTest.rangeReusableBooleanContinue),
    (`ReusableBooleanStepTest.rangeReusableBooleanCapture, ReusableBooleanStepTest.rangeReusableBooleanCapture),
    (`ReusableBooleanStepTest.rangeReusableBooleanNested, ReusableBooleanStepTest.rangeReusableBooleanNested),
    (`ReusableBooleanStepTest.rangeReusableBooleanStepHelper, ReusableBooleanStepTest.rangeReusableBooleanStepHelper),
    (`ReusableBooleanStepTest.rangeReusableBooleanUnused, ReusableBooleanStepTest.rangeReusableBooleanUnused)]
  let mut comparisons : Nat := 0
  for (name, native) in cases do
    let some info := env.find? name | throwError "missing declaration"
    let some value := info.value? | throwError "missing body"
    let some func := LeanExe.Extract.Core.extractScalarFunc name (some "entry") info.type value |
      throwError "{name}: reusable Boolean helper extraction failed"
    let module_ : LeanExe.IR.Module := { funcs := #[func] }
    for (x, y) in ReusableBooleanStepTest.inputs do
      let expected := native x y
      let actual := module_.evalFunc 0 [x, y]
      unless actual == expected do
        throwError "{name}({x}, {y}): native={expected}, IR={actual}"
      comparisons := comparisons + 1
  unless comparisons == 144 do throwError "unexpected comparison count {comparisons}"
  Lean.logInfo m!"{comparisons} native/reusable-Boolean step IR comparisons passed"

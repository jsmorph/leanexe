import LeanExe.Extract.ScalarFunc

namespace PUnitTest

def punitExplicit (x y : UInt64) : UInt64 :=
  let f : PUnit.{1} → UInt64 → UInt64 := fun _ a => a * 3 + x
  f PUnit.unit y

def punitCapture (x y : UInt64) : UInt64 :=
  let bias := x + 7
  let f : PUnit.{1} → UInt64 → UInt64 := fun _ a => a + bias
  let bias := y + 11
  f PUnit.unit bias - f PUnit.unit x

def punitChain (x y : UInt64) : UInt64 :=
  let f : PUnit.{1} → UInt64 → UInt64 := fun _ a => a ^^^ x
  let g : Unit → UInt64 → UInt64 := fun _ a => f PUnit.unit (a + y)
  g () x + f () y

def punitUnused (x y : UInt64) : UInt64 :=
  let _f : PUnit.{1} → UInt64 → UInt64 := fun _ a => if a ≤ x then min a y else max a y
  x + y

def punitDo (x y : UInt64) : UInt64 := Id.run do
  let f : PUnit.{1} → UInt64 → Id UInt64 := fun _ a => do
    let mut z := a
    if z < x then z := z + y else z := z - y
    return z ^^^ x
  let z ← f PUnit.unit y
  let result ← f PUnit.unit (z + x)
  return result

def punitNested (x y : UInt64) : UInt64 :=
  let f : PUnit.{1} → UInt64 → UInt64 := fun _ a =>
    let g : PUnit.{1} → UInt64 → UInt64 := fun _ b => (a + b) ^^^ x
    if true && a == y then g PUnit.unit y else g PUnit.unit (a + y)
  f PUnit.unit x + f PUnit.unit y

def rangePUnitJoined (count seed : UInt64) : UInt64 :=
  let result := Id.run do
    let mut a := seed
    for i in [:count.toNat] do
      if !(false || UInt64.ofNat i % 2 == 0) then a := a + 1 else a := a + 3
      if ¬False ∧ (true && a % 7 == 0) then break
    return a
  if true then result + seed else result - count

def rangePUnitStep (count seed : UInt64) : UInt64 :=
  forIn (m := Id) [:count.toNat] seed fun i a =>
    let finish : PUnit.{1} → UInt64 → Id (ForInStep UInt64) := fun _ x =>
      if x % 5 == seed % 5 then pure (.done (x + 7))
      else pure (.yield (x + UInt64.ofNat i))
    finish PUnit.unit (a + 1)

def rangePUnitScalar (count seed : UInt64) : UInt64 := Id.run do
  let mut a := seed
  for i in [:count.toNat] do
    let f : PUnit.{1} → UInt64 → UInt64 := fun _ x => x + UInt64.ofNat i + seed
    if UInt64.ofNat i % 3 == 1 then continue
    a := f PUnit.unit a
    if a % 7 == 2 then break
  return a

def rangePUnitYield (count seed : UInt64) : UInt64 := Id.run do
  let mut a := seed
  for i in [:count.toNat] do
    if UInt64.ofNat i % 2 == 0 then a := a + 3 else a := a + 1
    a := a ^^^ seed
  return a

def rangePUnitOuter (count seed : UInt64) : UInt64 :=
  let f : PUnit.{1} → UInt64 → UInt64 := fun _ x => x + seed + 1
  let result := Id.run do
    let mut a := f PUnit.unit seed
    for i in [:(f PUnit.unit count % 17).toNat] do
      a := f PUnit.unit (a + UInt64.ofNat i)
      if a % 5 == 0 then break
    return a
  f PUnit.unit result

def rangePUnitStride (count seed : UInt64) : UInt64 := Id.run do
  let mut a := seed
  for i in [1:count.toNat:3] do
    if UInt64.ofNat i % 2 == 0 then a := a + 11 else a := a - 7
    if a % 3 == 0 then continue
    a := a + UInt64.ofNat i
    if a % 5 == 1 then break
  return a

def punitHigherUniverse (x y : UInt64) : UInt64 :=
  let f : PUnit.{2} → UInt64 → UInt64 := fun _ a => a + x
  f PUnit.unit y

def punitUnsupportedBody (x y : UInt64) : UInt64 :=
  let f : PUnit.{1} → UInt64 → UInt64 := fun _ a => @Min.min UInt64 ⟨fun b c => b + c⟩ a x
  f PUnit.unit y

def punitUnusedUnsupported (x y : UInt64) : UInt64 :=
  let _f : PUnit.{1} → UInt64 → UInt64 := fun _ a => @Min.min UInt64 ⟨fun b c => b ^^^ c⟩ a y
  x + y

def inputs : List (UInt64 × UInt64) :=
  [(0, 0), (1, 0), (0xffffffffffffffff, 0), (0, 1), (1, 1),
   (0xffffffffffffffff, 1), (0x8000000000000000, 2), (42, 3),
   (0xffffffffffffffff, 63), (0x8000000000000001, 64), (0xffffffffffffffff, 65),
   (0x0123456789abcdef, 0xffffffffffffffff), (3, 17), (17, 3)]

end PUnitTest

run_elab do
  let env ← Lean.getEnv
  let cases : List (Lean.Name × (UInt64 → UInt64 → UInt64) × Bool) := [
    (`PUnitTest.punitExplicit, PUnitTest.punitExplicit, false),
    (`PUnitTest.punitCapture, PUnitTest.punitCapture, false),
    (`PUnitTest.punitChain, PUnitTest.punitChain, false),
    (`PUnitTest.punitUnused, PUnitTest.punitUnused, false),
    (`PUnitTest.punitDo, PUnitTest.punitDo, false),
    (`PUnitTest.punitNested, PUnitTest.punitNested, false),
    (`PUnitTest.rangePUnitJoined, PUnitTest.rangePUnitJoined, true),
    (`PUnitTest.rangePUnitStep, PUnitTest.rangePUnitStep, true),
    (`PUnitTest.rangePUnitScalar, PUnitTest.rangePUnitScalar, true),
    (`PUnitTest.rangePUnitYield, PUnitTest.rangePUnitYield, true),
    (`PUnitTest.rangePUnitOuter, PUnitTest.rangePUnitOuter, true),
    (`PUnitTest.rangePUnitStride, PUnitTest.rangePUnitStride, true)]
  for (name, native, isRange) in cases do
    let some info := env.find? name | throwError "missing declaration"
    let some value := info.value? | throwError "missing body"
    let some func := LeanExe.Extract.Core.extractScalarFunc name (some "entry") info.type value |
      throwError "{name}: PUnit continuation extraction failed"
    let module_ : LeanExe.IR.Module := { funcs := #[func] }
    let inputs := if isRange then
      ([0, 1, 2, 7, 16, 31] : List UInt64).flatMap fun n =>
        ([0, 1, 0x8000000000000000, 0xffffffffffffffff] : List UInt64).map fun seed => (n, seed)
      else PUnitTest.inputs
    for (x, y) in inputs do
      let expected := native x y
      let actual := module_.evalFunc 0 [x, y]
      unless actual == expected do
        throwError "{name}({x}, {y}): native={expected}, IR={actual}"
  for name in [`PUnitTest.punitHigherUniverse, `PUnitTest.punitUnsupportedBody, `PUnitTest.punitUnusedUnsupported] do
    let some info := env.find? name | throwError "missing declaration"
    let some value := info.value? | throwError "missing body"
    unless (LeanExe.Extract.Core.extractScalarFunc name (some "entry") info.type value).isNone do
      throwError "{name}: unsupported PUnit continuation accepted"
  Lean.logInfo "228 native/PUnit-continuation IR comparisons and three rejection tests passed"

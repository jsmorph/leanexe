import LeanExe.Extract.ScalarFunc

namespace RangeBinaryFunctionTest

def rangeBinaryLocal (count seed : UInt64) : UInt64 := Id.run do
  let mut a := seed
  for i in [:count.toNat] do
    let f := fun x y : UInt64 => x * 3 + y + UInt64.ofNat i
    a := f a seed
  return a

def rangeBinaryCapture (count seed : UInt64) : UInt64 := Id.run do
  let mut a := seed
  for i in [1:count.toNat:2] do
    let f := fun x y : UInt64 => a + x - y
    a := a + 7
    a := f a (UInt64.ofNat i)
  return a

def rangeBinaryNested (count seed : UInt64) : UInt64 := Id.run do
  let mut a := seed
  for i in [(seed % 3).toNat:count.toNat] do
    let f := fun x y : UInt64 =>
      let g := fun p q : UInt64 => p * x + q * y + UInt64.ofNat i
      g a seed
    a := f seed a
  return a

def rangeBinaryDo (count seed : UInt64) : UInt64 := Id.run do
  let mut a := seed
  for i in [:count.toNat] do
    let f : UInt64 → UInt64 → Id UInt64 := fun x y => do
      let c ← if x < y then pure (x + 7) else pure (y + seed)
      return c + UInt64.ofNat i
    let delta ← f a (UInt64.ofNat i)
    if delta % 5 == seed % 5 then break
    a := delta * 3 + 1
  return a

def rangeBinaryContinue (count seed : UInt64) : UInt64 := Id.run do
  let mut a := seed
  for i in [:count.toNat] do
    let f := fun x y : UInt64 => if x < y then x + y else x - y
    if f (UInt64.ofNat i) seed % 3 == 0 then continue
    a := f a (UInt64.ofNat i)
    if UInt64.ofNat i == 11 then break
  return a

def rangeBinaryUnused (count seed : UInt64) : UInt64 := Id.run do
  let mut a := seed
  for i in [:count.toNat] do
    let _f := fun x y : UInt64 => (x + a) / (y - UInt64.ofNat i)
    a := a + UInt64.ofNat i + 1
  return a

def binaryRangeHelper (x : UInt64) : UInt64 := x + 1

def rangeBinaryUnsupported (count seed : UInt64) : UInt64 := Id.run do
  let mut a := seed
  for i in [:count.toNat] do
    let _f := fun x y : UInt64 => binaryRangeHelper x + y
    a := a + UInt64.ofNat i
  return a

def rangeBinaryPartial (count seed : UInt64) : UInt64 := Id.run do
  let mut a := seed
  for i in [:count.toNat] do
    let f := fun x y : UInt64 => x + y
    let g := f a
    a := g (UInt64.ofNat i)
  return a

end RangeBinaryFunctionTest

run_elab do
  let env ← Lean.getEnv
  let cases : List (Lean.Name × (UInt64 → UInt64 → UInt64)) := [
    (`RangeBinaryFunctionTest.rangeBinaryLocal, RangeBinaryFunctionTest.rangeBinaryLocal),
    (`RangeBinaryFunctionTest.rangeBinaryCapture, RangeBinaryFunctionTest.rangeBinaryCapture),
    (`RangeBinaryFunctionTest.rangeBinaryNested, RangeBinaryFunctionTest.rangeBinaryNested),
    (`RangeBinaryFunctionTest.rangeBinaryDo, RangeBinaryFunctionTest.rangeBinaryDo),
    (`RangeBinaryFunctionTest.rangeBinaryContinue, RangeBinaryFunctionTest.rangeBinaryContinue),
    (`RangeBinaryFunctionTest.rangeBinaryUnused, RangeBinaryFunctionTest.rangeBinaryUnused)]
  for (name, native) in cases do
    let some info := env.find? name | throwError "missing declaration"
    let some value := info.value? | throwError "missing body"
    let some func := LeanExe.Extract.Core.extractScalarFunc name (some "entry") info.type value |
      throwError "{name}: binary-function range extraction failed"
    let module_ : LeanExe.IR.Module := { funcs := #[func] }
    for count in ([0, 1, 2, 7, 16, 31] : List UInt64) do
      for seed in ([0, 1, 0x8000000000000000, 0xffffffffffffffff] : List UInt64) do
        let expected := native count seed
        let actual := module_.evalFunc 0 [count, seed]
        unless actual == expected do
          throwError "{name}({count}, {seed}): native={expected}, IR={actual}"
  for name in [`RangeBinaryFunctionTest.rangeBinaryUnsupported, `RangeBinaryFunctionTest.rangeBinaryPartial] do
    let some info := env.find? name | throwError "missing declaration"
    let some value := info.value? | throwError "missing body"
    unless (LeanExe.Extract.Core.extractScalarFunc name (some "entry") info.type value).isNone do
      throwError "{name}: unsupported binary function accepted"
  Lean.logInfo "144 native/range-binary-function IR comparisons and two rejection tests passed"

import LeanExe.Extract.ScalarFunc

namespace OuterRangeFunctionTest

def rangeOuterUnary (count seed : UInt64) : UInt64 := Id.run do
  let f := fun x : UInt64 => x * 3 + seed
  let mut a := seed
  for i in [:count.toNat] do
    a := f a + UInt64.ofNat i
  return f a

def rangeOuterBinary (count seed : UInt64) : UInt64 := Id.run do
  let f := fun x y : UInt64 => x * 3 + y - seed
  let mut a := seed
  for i in [:count.toNat] do
    a := f a (UInt64.ofNat i)
    if a % 7 == 0 then break
  return f a count

def rangeOuterUnit (count seed : UInt64) : UInt64 := Id.run do
  let f := fun (_ : Unit) (x : UInt64) => x + seed + 1
  let mut a := f () seed
  for i in [1:count.toNat:2] do
    a := f () (a + UInt64.ofNat i)
  return f () a

def rangeOuterCapture (count seed : UInt64) : UInt64 := Id.run do
  let mut a := seed
  let f := fun x : UInt64 => x + a
  a := a + 17
  for i in [:count.toNat] do
    a := f a + UInt64.ofNat i
    if !(a % 5 != seed % 5) then break
  return f a

def rangeOuterBounds (count seed : UInt64) : UInt64 := Id.run do
  let endpoint := fun x y : UInt64 => (x + y) % 7
  let mut a := endpoint seed count
  for i in [(endpoint seed 1).toNat:(endpoint count seed + 16).toNat] do
    a := a + UInt64.ofNat i
  return endpoint a seed

def rangeOuterChained (count seed : UInt64) : UInt64 := Id.run do
  let f := fun x : UInt64 => x + seed
  let g := fun x y : UInt64 => f (x * 3) + y
  let mut a := seed
  for i in [:count.toNat] do
    if UInt64.ofNat i % 3 == 0 then continue
    a := g a (UInt64.ofNat i)
  return g a count

def rangeOuterNested (count seed : UInt64) : UInt64 := Id.run do
  let f := fun x y : UInt64 =>
    let g := fun z : UInt64 => if !(z == x) then z + y else z * 3
    g seed + g x
  let mut a := f seed count
  for i in [:count.toNat] do
    a := f a (UInt64.ofNat i)
  return f a seed

def rangeOuterDo (count seed : UInt64) : UInt64 := Id.run do
  let f : UInt64 → Id UInt64 := fun x => do
    let z ← if x < seed then pure (x + 3) else pure (x / 3)
    return z + 1
  let mut a ← f seed
  for i in [:count.toNat] do
    let z ← f a
    a := z + UInt64.ofNat i
    if a % 5 == 0 then break
  let result ← f a
  return result

def rangeOuterUnused (count seed : UInt64) : UInt64 := Id.run do
  let _f := fun x y : UInt64 => x / y + seed
  let mut a := seed
  for i in [:count.toNat] do
    a := a + UInt64.ofNat i + 1
  return a

def rangeOuterStep (count seed : UInt64) : UInt64 := Id.run do
  let f := fun x y : UInt64 => x * 3 + y + seed
  let result ← forIn (m := Id) [:count.toNat] seed fun i a =>
    let finish : UInt64 → UInt64 → Id (ForInStep UInt64) := fun x y => do
      let z ← pure (f x y)
      if z % 5 == seed % 5 then return .done (z + 7)
      return .yield (z + UInt64.ofNat i)
    finish a seed
  return f result count

def outerRangeExternal (x : UInt64) : UInt64 := x + 1

def rangeOuterUnsupported (count seed : UInt64) : UInt64 := Id.run do
  let _f := fun x : UInt64 => outerRangeExternal x
  let mut a := seed
  for i in [:count.toNat] do
    a := a + UInt64.ofNat i
  return a

def rangeOuterThree (count seed : UInt64) : UInt64 := Id.run do
  let f := fun x y z : UInt64 => x + y + z
  let mut a := seed
  for i in [:count.toNat] do
    a := f a seed (UInt64.ofNat i)
  return a

def rangeOuterNat (count seed : UInt64) : UInt64 := Id.run do
  let f := fun x : Nat => UInt64.ofNat x
  let mut a := seed
  for i in [:count.toNat] do
    a := a + f i
  return a

def rangeOuterPartial (count seed : UInt64) : UInt64 := Id.run do
  let f := fun x y : UInt64 => x + y
  let g := f seed
  let mut a := seed
  for i in [:count.toNat] do
    a := g a + UInt64.ofNat i
  return a

end OuterRangeFunctionTest

run_elab do
  let env ← Lean.getEnv
  let cases : List (Lean.Name × (UInt64 → UInt64 → UInt64)) := [
    (`OuterRangeFunctionTest.rangeOuterUnary, OuterRangeFunctionTest.rangeOuterUnary),
    (`OuterRangeFunctionTest.rangeOuterBinary, OuterRangeFunctionTest.rangeOuterBinary),
    (`OuterRangeFunctionTest.rangeOuterUnit, OuterRangeFunctionTest.rangeOuterUnit),
    (`OuterRangeFunctionTest.rangeOuterCapture, OuterRangeFunctionTest.rangeOuterCapture),
    (`OuterRangeFunctionTest.rangeOuterBounds, OuterRangeFunctionTest.rangeOuterBounds),
    (`OuterRangeFunctionTest.rangeOuterChained, OuterRangeFunctionTest.rangeOuterChained),
    (`OuterRangeFunctionTest.rangeOuterNested, OuterRangeFunctionTest.rangeOuterNested),
    (`OuterRangeFunctionTest.rangeOuterDo, OuterRangeFunctionTest.rangeOuterDo),
    (`OuterRangeFunctionTest.rangeOuterUnused, OuterRangeFunctionTest.rangeOuterUnused),
    (`OuterRangeFunctionTest.rangeOuterStep, OuterRangeFunctionTest.rangeOuterStep),
    (`OuterRangeFunctionTest.rangeOuterThree, OuterRangeFunctionTest.rangeOuterThree)]
  for (name, native) in cases do
    let some info := env.find? name | throwError "missing declaration"
    let some value := info.value? | throwError "missing body"
    let some func := LeanExe.Extract.Core.extractScalarFunc name (some "entry") info.type value |
      throwError "{name}: outer-function range extraction failed"
    let module_ : LeanExe.IR.Module := { funcs := #[func] }
    for count in ([0, 1, 2, 7, 16, 31] : List UInt64) do
      for seed in ([0, 1, 0x8000000000000000, 0xffffffffffffffff] : List UInt64) do
        let expected := native count seed
        let actual := module_.evalFunc 0 [count, seed]
        unless actual == expected do
          throwError "{name}({count}, {seed}): native={expected}, IR={actual}"
  for name in [`OuterRangeFunctionTest.rangeOuterUnsupported, `OuterRangeFunctionTest.rangeOuterNat, `OuterRangeFunctionTest.rangeOuterPartial] do
    let some info := env.find? name | throwError "missing declaration"
    let some value := info.value? | throwError "missing body"
    unless (LeanExe.Extract.Core.extractScalarFunc name (some "entry") info.type value).isNone do
      throwError "{name}: unsupported outer function accepted"
  Lean.logInfo "264 native/outer-range-function IR comparisons and three rejection tests passed"

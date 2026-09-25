import LeanExe.Extract.ScalarFunc

namespace RangeLetResultTest

def rangeLetResult (count seed : UInt64) : UInt64 :=
  let result := Id.run do
    let mut a := seed
    for i in [:count.toNat] do
      a := a + UInt64.ofNat i + 1
    return a
  result * 3 + seed

def rangeLetDirect (count seed : UInt64) : UInt64 :=
  let result : UInt64 := forIn (m := Id) [:count.toNat] seed fun i a =>
    if UInt64.ofNat i == seed % 7 then .done (a + 9) else .yield (a * 3 + 1)
  result + count

def rangeLetCapture (count seed : UInt64) : UInt64 :=
  let captured := seed + 7
  let result := Id.run do
    let mut a := captured
    for i in [:count.toNat] do
      a := a + captured + UInt64.ofNat i
    return a
  let captured := result + 11
  result + captured

def rangeLetAliases (count seed : UInt64) : UInt64 :=
  let result := Id.run do
    let mut a := seed
    for _ in [:count.toNat] do
      a := a * 3 + 1
    return a
  let alias := result
  let result := alias + 7
  result - alias / 3

def rangeLetUnused (count seed : UInt64) : UInt64 :=
  let _ignored := Id.run do
    let mut a := seed
    for i in [:count.toNat] do
      a := a + UInt64.ofNat i
      if a % 5 == 0 then break
    return a
  seed + count

def rangeLetStride (count seed : UInt64) : UInt64 :=
  let result := Id.run do
    let mut a := seed
    for i in [(seed % 3).toNat:count.toNat:2] do
      a := a + UInt64.ofNat i
      if a % 7 == seed % 7 then break
    return a
  if !(result == seed) then result + 11 else result * 3

def rangeLetContinue (count seed : UInt64) : UInt64 :=
  let result := Id.run do
    let mut a := seed
    for i in [:count.toNat] do
      if UInt64.ofNat i % 3 == 0 then continue
      a := a + UInt64.ofNat i
    return a
  result ^^^ seed

def rangeLetMonadic (count seed : UInt64) : UInt64 := Id.run do
  let result := Id.run do
    let mut a := seed
    for i in [:count.toNat] do
      let x ← pure (a + UInt64.ofNat i)
      a := x * 3
    return a
  let z ← pure (result + 7)
  return z * 3 + seed

def rangeLetHelper (count seed : UInt64) : UInt64 :=
  let f := fun x y : UInt64 => x * 3 + y + seed
  let result := Id.run do
    let mut a := seed
    for i in [:count.toNat] do
      a := f a (UInt64.ofNat i)
    return a
  let g := fun x : UInt64 => f x result
  g seed + g count

def rangeLetNested (count seed : UInt64) : UInt64 :=
  let outer :=
    let start := seed + 3
    let inner := Id.run do
      let mut a := start
      for i in [1:count.toNat] do
        a := a + UInt64.ofNat i
      return a
    inner * 3 + start
  outer + seed

def rangeLetExternal (x : UInt64) : UInt64 := x + 1

def rangeLetUnsupported (count seed : UInt64) : UInt64 :=
  let _ignored := Id.run do
    let mut a := seed
    for i in [:count.toNat] do
      a := rangeLetExternal a + UInt64.ofNat i
    return a
  seed + count

def rangeLetTwoLoops (count seed : UInt64) : UInt64 :=
  let first := Id.run do
    let mut a := seed
    for _ in [:count.toNat] do
      a := a + 1
    return a
  let second := Id.run do
    let mut a := first
    for _ in [:count.toNat] do
      a := a * 3
    return a
  second

def rangeLetBool (count seed : UInt64) : UInt64 :=
  let flag := Id.run do
    let mut a := seed
    for _ in [:count.toNat] do
      a := a + 1
    return a == 0
  if flag then count else seed

end RangeLetResultTest

run_elab do
  let env ← Lean.getEnv
  let cases : List (Lean.Name × (UInt64 → UInt64 → UInt64)) := [
    (`RangeLetResultTest.rangeLetResult, RangeLetResultTest.rangeLetResult),
    (`RangeLetResultTest.rangeLetDirect, RangeLetResultTest.rangeLetDirect),
    (`RangeLetResultTest.rangeLetCapture, RangeLetResultTest.rangeLetCapture),
    (`RangeLetResultTest.rangeLetAliases, RangeLetResultTest.rangeLetAliases),
    (`RangeLetResultTest.rangeLetUnused, RangeLetResultTest.rangeLetUnused),
    (`RangeLetResultTest.rangeLetStride, RangeLetResultTest.rangeLetStride),
    (`RangeLetResultTest.rangeLetContinue, RangeLetResultTest.rangeLetContinue),
    (`RangeLetResultTest.rangeLetMonadic, RangeLetResultTest.rangeLetMonadic),
    (`RangeLetResultTest.rangeLetHelper, RangeLetResultTest.rangeLetHelper),
    (`RangeLetResultTest.rangeLetNested, RangeLetResultTest.rangeLetNested)]
  for (name, native) in cases do
    let some info := env.find? name | throwError "missing declaration"
    let some value := info.value? | throwError "missing body"
    let some func := LeanExe.Extract.Core.extractScalarFunc name (some "entry") info.type value |
      throwError "{name}: let-result range extraction failed"
    let module_ : LeanExe.IR.Module := { funcs := #[func] }
    for count in ([0, 1, 2, 7, 16, 31] : List UInt64) do
      for seed in ([0, 1, 0x8000000000000000, 0xffffffffffffffff] : List UInt64) do
        let expected := native count seed
        let actual := module_.evalFunc 0 [count, seed]
        unless actual == expected do
          throwError "{name}({count}, {seed}): native={expected}, IR={actual}"
  for name in [`RangeLetResultTest.rangeLetUnsupported, `RangeLetResultTest.rangeLetTwoLoops, `RangeLetResultTest.rangeLetBool] do
    let some info := env.find? name | throwError "missing declaration"
    let some value := info.value? | throwError "missing body"
    unless (LeanExe.Extract.Core.extractScalarFunc name (some "entry") info.type value).isNone do
      throwError "{name}: unsupported range let accepted"
  Lean.logInfo "240 native/range-let-result IR comparisons and three rejection tests passed"

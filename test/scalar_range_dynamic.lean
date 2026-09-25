import LeanExe.Extract.ScalarFunc

namespace RangeDynamicTest

def rangeDynamicStart (count seed : UInt64) : UInt64 := Id.run do
  let mut a := seed
  for i in [(seed % 7).toNat:count.toNat] do
    a := a * 3 + UInt64.ofNat i
  return a

def rangeDynamicLiteral (count seed : UInt64) : UInt64 :=
  forIn (m := Id) [count.toNat:8] seed fun i a => .yield (a + UInt64.ofNat i)

def rangeDynamicComputed (count seed : UInt64) : UInt64 := Id.run do
  let mut a := seed
  for i in [(count / 2).toNat:(count + seed % 3).toNat] do
    a := a + UInt64.ofNat i
  return a

def rangeDynamicCapture (count seed : UInt64) : UInt64 := Id.run do
  let mut a := seed
  for i in [a.toNat:(a + count).toNat] do
    a := a + UInt64.ofNat i + 7
  return a

def rangeDynamicHigh (count seed : UInt64) : UInt64 :=
  forIn (m := Id) [(18446744073709551615 - count).toNat:18446744073709551615] seed fun i a =>
    .yield (a + UInt64.ofNat i)

def rangeDynamicEmpty (count seed : UInt64) : UInt64 :=
  forIn (m := Id) [(count + 1).toNat:count.toNat] seed fun i a => .yield (a + UInt64.ofNat i)

def rangeDynamicEqual (count seed : UInt64) : UInt64 :=
  forIn (m := Id) [(seed + count).toNat:(seed + count).toNat] seed fun i a => .done (a + UInt64.ofNat i)

def rangeDynamicHugeBreak (count seed : UInt64) : UInt64 :=
  forIn (m := Id) [(seed % 7).toNat:18446744073709551615] seed fun i a => .done (a + UInt64.ofNat i + count)

def rangeDynamicContinue (count seed : UInt64) : UInt64 := Id.run do
  let mut a := seed
  for i in [(seed % 5).toNat:count.toNat] do
    if UInt64.ofNat i % 3 == 0 then continue
    a := a + UInt64.ofNat i
    if UInt64.ofNat i == 11 then break
  return a

def rangeDynamicJoin (count seed : UInt64) : UInt64 :=
  forIn (m := Id) [(seed % 5).toNat:count.toNat] seed fun i a => do
    let result ← if UInt64.ofNat i == 7 then pure (.done (a + 11)) else pure (.yield (a + UInt64.ofNat i))
    return result

def rangeDynamicChoice (count seed : UInt64) : UInt64 := Id.run do
  let mut a := seed
  for i in [(if count < seed then count / 2 else 0).toNat:count.toNat] do
    let f := fun x : UInt64 => x + UInt64.ofNat i
    a := f a
  return a

def dynamicNatAddition (seed : UInt64) : UInt64 :=
  forIn (m := Id) [(seed.toNat + 1):10] seed fun _ a => .done a

def dynamicHelper (seed : UInt64) : UInt64 := seed + 1
def dynamicCalledStart (seed : UInt64) : UInt64 :=
  forIn (m := Id) [(dynamicHelper seed).toNat:10] seed fun _ a => .done a

end RangeDynamicTest

run_elab do
  let env ← Lean.getEnv
  let cases : List (Lean.Name × (UInt64 → UInt64 → UInt64)) := [
    (`RangeDynamicTest.rangeDynamicStart, RangeDynamicTest.rangeDynamicStart),
    (`RangeDynamicTest.rangeDynamicLiteral, RangeDynamicTest.rangeDynamicLiteral),
    (`RangeDynamicTest.rangeDynamicComputed, RangeDynamicTest.rangeDynamicComputed),
    (`RangeDynamicTest.rangeDynamicCapture, RangeDynamicTest.rangeDynamicCapture),
    (`RangeDynamicTest.rangeDynamicHigh, RangeDynamicTest.rangeDynamicHigh),
    (`RangeDynamicTest.rangeDynamicEmpty, RangeDynamicTest.rangeDynamicEmpty),
    (`RangeDynamicTest.rangeDynamicEqual, RangeDynamicTest.rangeDynamicEqual),
    (`RangeDynamicTest.rangeDynamicHugeBreak, RangeDynamicTest.rangeDynamicHugeBreak),
    (`RangeDynamicTest.rangeDynamicContinue, RangeDynamicTest.rangeDynamicContinue),
    (`RangeDynamicTest.rangeDynamicJoin, RangeDynamicTest.rangeDynamicJoin),
    (`RangeDynamicTest.rangeDynamicChoice, RangeDynamicTest.rangeDynamicChoice)]
  for (name, native) in cases do
    let some info := env.find? name | throwError "missing declaration"
    let some value := info.value? | throwError "missing body"
    let some func := LeanExe.Extract.Core.extractScalarFunc name (some "entry") info.type value |
      throwError "{name}: dynamic range extraction failed"
    let module_ : LeanExe.IR.Module := { funcs := #[func] }
    for count in ([0, 1, 2, 7, 16, 31] : List UInt64) do
      for seed in ([0, 1, 0x8000000000000000, 0xffffffffffffffff] : List UInt64) do
        let expected := native count seed
        let actual := module_.evalFunc 0 [count, seed]
        unless actual == expected do
          throwError "{name}({count}, {seed}): native={expected}, IR={actual}"
  for name in [`RangeDynamicTest.dynamicNatAddition, `RangeDynamicTest.dynamicCalledStart] do
    let some info := env.find? name | throwError "missing declaration"
    let some value := info.value? | throwError "missing body"
    unless (LeanExe.Extract.Core.extractScalarFunc name (some "entry") info.type value).isNone do
      throwError "{name}: unsupported dynamic range accepted"
  Lean.logInfo "264 native/dynamic-range IR comparisons and two rejection tests passed"

import LeanExe.Extract.ScalarFunc

namespace RangeIntervalTest

def rangeFromOne (count seed : UInt64) : UInt64 := Id.run do
  let mut a := seed
  for i in [1:count.toNat] do
    a := a * 3 + UInt64.ofNat i
  return a

def rangeIntervalLiteral (count seed : UInt64) : UInt64 := Id.run do
  let mut a := seed
  for i in [3:8] do
    a := a + UInt64.ofNat i + count
  return a

def rangeIntervalEmpty (count seed : UInt64) : UInt64 :=
  forIn (m := Id) [8:3] seed fun i a => .yield (a + UInt64.ofNat i + count)

def rangeIntervalEqual (count seed : UInt64) : UInt64 :=
  forIn (m := Id) [7:7] seed fun i a => .done (a + UInt64.ofNat i + count)

def rangeIntervalBreak (count seed : UInt64) : UInt64 := Id.run do
  let mut a := seed
  for i in [5:count.toNat] do
    a := a + UInt64.ofNat i
    if UInt64.ofNat i == 7 then break
    a := a * 3
  return a

def rangeIntervalContinue (count seed : UInt64) : UInt64 := Id.run do
  let mut a := seed
  for i in [1:count.toNat] do
    if UInt64.ofNat i % 3 == 0 then continue
    a := a + UInt64.ofNat i
    if UInt64.ofNat i == 11 then break
  return a

def rangeIntervalCapture (count seed : UInt64) : UInt64 := Id.run do
  let delta := seed + 7
  let mut a := seed * 3
  for i in [2:(count + 1).toNat] do
    let f := fun x : UInt64 => x + delta + UInt64.ofNat i
    a := f a
  return a - delta

def rangeIntervalJoin (count seed : UInt64) : UInt64 :=
  forIn (m := Id) [3:count.toNat] seed fun i a => do
    let result ← if UInt64.ofNat i == 7 then pure (.done (a + 11)) else pure (.yield (a + UInt64.ofNat i))
    return result

def rangeIntervalHigh (count seed : UInt64) : UInt64 :=
  forIn (m := Id) [18446744073709551613:18446744073709551615] seed fun i a =>
    .yield (a + UInt64.ofNat i + count)

def rangeIntervalMaxEmpty (count seed : UInt64) : UInt64 :=
  forIn (m := Id) [18446744073709551615:count.toNat] seed fun i a => .done (a + UInt64.ofNat i)

def rangeIntervalHugeBreak (count seed : UInt64) : UInt64 :=
  forIn (m := Id) [2:18446744073709551615] seed fun i a => .done (a + UInt64.ofNat i + count)

def intervalOverflow (seed : UInt64) : UInt64 :=
  forIn (m := Id) [18446744073709551616:0] seed fun _ a => .done a

@[instance_reducible] def customFirst : OfNat Nat 8 := ⟨9⟩
def intervalCustom (seed : UInt64) : UInt64 :=
  forIn (m := Id) [(@OfNat.ofNat Nat 8 customFirst):10] seed fun _ a => .done a

def intervalDynamic (seed : UInt64) : UInt64 :=
  forIn (m := Id) [seed.toNat:10] seed fun _ a => .done a

end RangeIntervalTest

run_elab do
  let env ← Lean.getEnv
  let cases : List (Lean.Name × (UInt64 → UInt64 → UInt64)) := [
    (`RangeIntervalTest.rangeFromOne, RangeIntervalTest.rangeFromOne),
    (`RangeIntervalTest.rangeIntervalLiteral, RangeIntervalTest.rangeIntervalLiteral),
    (`RangeIntervalTest.rangeIntervalEmpty, RangeIntervalTest.rangeIntervalEmpty),
    (`RangeIntervalTest.rangeIntervalEqual, RangeIntervalTest.rangeIntervalEqual),
    (`RangeIntervalTest.rangeIntervalBreak, RangeIntervalTest.rangeIntervalBreak),
    (`RangeIntervalTest.rangeIntervalContinue, RangeIntervalTest.rangeIntervalContinue),
    (`RangeIntervalTest.rangeIntervalCapture, RangeIntervalTest.rangeIntervalCapture),
    (`RangeIntervalTest.rangeIntervalJoin, RangeIntervalTest.rangeIntervalJoin),
    (`RangeIntervalTest.rangeIntervalHigh, RangeIntervalTest.rangeIntervalHigh),
    (`RangeIntervalTest.rangeIntervalMaxEmpty, RangeIntervalTest.rangeIntervalMaxEmpty),
    (`RangeIntervalTest.rangeIntervalHugeBreak, RangeIntervalTest.rangeIntervalHugeBreak)]
  for (name, native) in cases do
    let some info := env.find? name | throwError "missing declaration"
    let some value := info.value? | throwError "missing body"
    let some func := LeanExe.Extract.Core.extractScalarFunc name (some "entry") info.type value |
      throwError "{name}: interval extraction failed"
    let module_ : LeanExe.IR.Module := { funcs := #[func] }
    for count in ([0, 1, 2, 7, 16, 31] : List UInt64) do
      for seed in ([0, 1, 0x8000000000000000, 0xffffffffffffffff] : List UInt64) do
        let expected := native count seed
        let actual := module_.evalFunc 0 [count, seed]
        unless actual == expected do
          throwError "{name}({count}, {seed}): native={expected}, IR={actual}"
  for name in [`RangeIntervalTest.intervalOverflow, `RangeIntervalTest.intervalCustom] do
    let some info := env.find? name | throwError "missing declaration"
    let some value := info.value? | throwError "missing body"
    unless (LeanExe.Extract.Core.extractScalarFunc name (some "entry") info.type value).isNone do
      throwError "{name}: unsupported interval accepted"
  Lean.logInfo "264 native/interval IR comparisons and two rejection tests passed"

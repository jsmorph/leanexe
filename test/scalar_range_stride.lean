import LeanExe.Extract.ScalarFunc

namespace RangeStrideTest

def rangeStrideTwo (count seed : UInt64) : UInt64 := Id.run do
  let mut a := seed
  for i in [0:count.toNat:2] do
    a := a * 3 + UInt64.ofNat i
  return a

def rangeStrideLiteral (count seed : UInt64) : UInt64 :=
  forIn (m := Id) [2:15:3] seed fun i a => .yield (a + UInt64.ofNat i + count)

def rangeStrideDynamic (count seed : UInt64) : UInt64 := Id.run do
  let mut a := seed
  for i in [(seed % 5).toNat:count.toNat:3] do
    a := a + UInt64.ofNat i
  return a

def rangeStrideCapture (count seed : UInt64) : UInt64 := Id.run do
  let mut a := seed
  for i in [a.toNat:(a + count).toNat:3] do
    a := a + UInt64.ofNat i + 7
  return a

def rangeStrideHigh (count seed : UInt64) : UInt64 :=
  forIn (m := Id) [(18446744073709551615 - count).toNat:18446744073709551615:2] seed fun i a =>
    .yield (a + UInt64.ofNat i)

def rangeStrideEmpty (count seed : UInt64) : UInt64 :=
  forIn (m := Id) [8:3:7] seed fun i a => .yield (a + UInt64.ofNat i + count)

def rangeStrideHuge (count seed : UInt64) : UInt64 :=
  forIn (m := Id) [0:count.toNat:18446744073709551615] seed fun i a => .yield (a + UInt64.ofNat i + 7)

def rangeStrideHugeTwo (count seed : UInt64) : UInt64 :=
  forIn (m := Id) [0:18446744073709551615:18446744073709551614] seed fun i a => .yield (a + UInt64.ofNat i + count)

def rangeStrideHugeBreak (count seed : UInt64) : UInt64 :=
  forIn (m := Id) [1:18446744073709551615:2] seed fun i a => .done (a + UInt64.ofNat i + count)

def rangeStrideContinue (count seed : UInt64) : UInt64 := Id.run do
  let mut a := seed
  for i in [1:count.toNat:2] do
    if UInt64.ofNat i % 3 == 0 then continue
    a := a + UInt64.ofNat i
    if UInt64.ofNat i == 11 then break
  return a

def rangeStrideJoin (count seed : UInt64) : UInt64 :=
  forIn (m := Id) [2:count.toNat:3] seed fun i a => do
    let result ← if UInt64.ofNat i == 8 then pure (.done (a + 11)) else pure (.yield (a + UInt64.ofNat i))
    return result

def rangeStrideOne (count seed : UInt64) : UInt64 :=
  forIn (m := Id) [2:count.toNat:1] seed fun i a => .yield (a + UInt64.ofNat i)

def strideOverflow (seed : UInt64) : UInt64 :=
  forIn (m := Id) [0:10:18446744073709551616] seed fun _ a => .done a

@[instance_reducible] def customStride : OfNat Nat 2 := ⟨3⟩
def strideCustom (seed : UInt64) : UInt64 :=
  forIn (m := Id) [0:10:(@OfNat.ofNat Nat 2 customStride)] seed fun _ a => .done a

def strideDynamic (seed : UInt64) : UInt64 :=
  forIn (m := Id) ({start := 0, stop := 10, step := seed.toNat + 1, step_pos := Nat.zero_lt_succ _} : Std.Legacy.Range) seed fun _ a => .done a

end RangeStrideTest

run_elab do
  let env ← Lean.getEnv
  let cases : List (Lean.Name × (UInt64 → UInt64 → UInt64)) := [
    (`RangeStrideTest.rangeStrideTwo, RangeStrideTest.rangeStrideTwo),
    (`RangeStrideTest.rangeStrideLiteral, RangeStrideTest.rangeStrideLiteral),
    (`RangeStrideTest.rangeStrideDynamic, RangeStrideTest.rangeStrideDynamic),
    (`RangeStrideTest.rangeStrideCapture, RangeStrideTest.rangeStrideCapture),
    (`RangeStrideTest.rangeStrideHigh, RangeStrideTest.rangeStrideHigh),
    (`RangeStrideTest.rangeStrideEmpty, RangeStrideTest.rangeStrideEmpty),
    (`RangeStrideTest.rangeStrideHuge, RangeStrideTest.rangeStrideHuge),
    (`RangeStrideTest.rangeStrideHugeTwo, RangeStrideTest.rangeStrideHugeTwo),
    (`RangeStrideTest.rangeStrideHugeBreak, RangeStrideTest.rangeStrideHugeBreak),
    (`RangeStrideTest.rangeStrideContinue, RangeStrideTest.rangeStrideContinue),
    (`RangeStrideTest.rangeStrideJoin, RangeStrideTest.rangeStrideJoin),
    (`RangeStrideTest.rangeStrideOne, RangeStrideTest.rangeStrideOne)]
  for (name, native) in cases do
    let some info := env.find? name | throwError "missing declaration"
    let some value := info.value? | throwError "missing body"
    let some func := LeanExe.Extract.Core.extractScalarFunc name (some "entry") info.type value |
      throwError "{name}: strided range extraction failed"
    let module_ : LeanExe.IR.Module := { funcs := #[func] }
    for count in ([0, 1, 2, 7, 16, 31] : List UInt64) do
      for seed in ([0, 1, 0x8000000000000000, 0xffffffffffffffff] : List UInt64) do
        let expected := native count seed
        let actual := module_.evalFunc 0 [count, seed]
        unless actual == expected do
          throwError "{name}({count}, {seed}): native={expected}, IR={actual}"
  for name in [`RangeStrideTest.strideOverflow, `RangeStrideTest.strideCustom, `RangeStrideTest.strideDynamic] do
    let some info := env.find? name | throwError "missing declaration"
    let some value := info.value? | throwError "missing body"
    unless (LeanExe.Extract.Core.extractScalarFunc name (some "entry") info.type value).isNone do
      throwError "{name}: unsupported strided range accepted"
  unless (LeanExe.Extract.Core.scalarRangeStride?
      (LeanExe.Source.Scalar.Range.natLiteral 0) (.const ``Nat.zero_lt_one [])).isNone do
    throwError "zero stride accepted"
  Lean.logInfo "288 native/stride IR comparisons and four rejection tests passed"

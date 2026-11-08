import Examples.Binary32.Program
import LeanExe.Dialect.Build
import Verified.Reflect.Command

/-!
A program of the binary32 conversions for AArch64: `convCheck n` applies
`Examples.Binary32.piecewise32`, whose comparisons, negation, absolute value, `min`, and `max` give
`FCMP`, `FSUB`, and the integer code of `f32Abs`, to `n` inputs, each the conversion of a signed
32-bit word to binary32 by `SCVTF` scaled by 2^-21, with the bounds -500 and 700.  For each input
it returns four words: the bits of the result, its truncation to an unsigned 64-bit integer by
`FCVTZU`, its truncation to a signed 32-bit integer by `FCVTZS`, zero-extended, and the bits of the
absolute value of `Float32.ofBits` of another word, which canonicalizes a NaN.  The inputs below
-500 give negative results, which `FCVTZU` saturates to 0 and `FCVTZS` keeps.
-/

namespace TestSupport.A64.Conv32

/-- The four words of the input `i`. -/
def convWord (i k : UInt64) : UInt64 :=
  let x := (Int32.ofUInt32 (i * 2654435761 + 12345).toUInt32).toFloat32 * 0.000000476837158203125
  let y := Examples.Binary32.piecewise32 x (-500.0) 700.0
  if k == 0 then y.toBits.toUInt64
  else if k == 1 then y.toUInt64
  else if k == 2 then y.toInt32.toUInt32.toUInt64
  else (Float32.ofBits (i * 2246822519).toUInt32).abs.toBits.toUInt64

/-- The four words of each of the inputs below `n`. -/
def convCheck (n : UInt64) : Array UInt64 :=
  LeanExe.build (4 * n) fun e => convWord (e / 4) (e % 4)

verified_compile compiled := [Examples.Binary32.piecewise32, convWord, convCheck]

end TestSupport.A64.Conv32

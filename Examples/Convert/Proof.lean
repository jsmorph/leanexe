import Examples.Convert.Program
import Examples.Convert.Spec
import LeanExe.ProofKit.Signed64Wasm

/-! The programs meet their specifications, by the equations of `LeanExe.ProofKit.Signed64Wasm`
between Lean's conversions and Talos's, and for `scale` by `F64Bits.toBits_mul`, which equates
Lean's product with Talos's `mul`.  `special_values` states, by the kernel's evaluation of the
programs, the results at the special values: the signed zeros, NaN, the infinities, `±2^63` and
their neighbors, the integers `2^53 + 1` and `2^53 + 3` and their negations, which round to even
in binary64 at different magnitudes, and `2^62 + 2^38 + 1`, which rounds up in binary32 although
its rounding to binary64 is the tie `2^62 + 2^38`, whose rounding to binary32 is `2^62`. -/

namespace Examples.Convert

open LeanExe.ProofKit

theorem toDouble_spec (a : Int64) : (toDouble a).toBits = expectedToDouble a :=
  Signed64Wasm.toBits_toFloat a

theorem toSingle_spec (a : Int64) : (toSingle a).toBits = expectedToSingle a :=
  Signed64Wasm.toBits_toFloat32 a

theorem ofDouble_spec (x : Float) : (ofDouble x).toUInt64 = expectedOfDouble x :=
  Signed64Wasm.toInt64_eq x

theorem ofSingle_spec (x : Float32) : (ofSingle x).toUInt64 = expectedOfSingle x :=
  Signed64Wasm.toInt64_eq32 x

theorem scale_spec (a : Int64) (k : Float) : (scale a k).toUInt64 = expectedScale a k := by
  unfold scale expectedScale
  rw [Signed64Wasm.toInt64_eq, F64Bits.toBits_mul, Signed64Wasm.toBits_toFloat]

theorem special_values :
    (ofDouble (Float.ofBits 0x7FF8000000000000)).toUInt64 = 0 ∧
    (ofDouble (Float.ofBits 0x8000000000000000)).toUInt64 = 0 ∧
    (ofDouble (Float.ofBits 0xBFE0000000000000)).toUInt64 = 0 ∧
    (ofDouble (Float.ofBits 0xBFF8000000000000)).toUInt64 = 0xFFFFFFFFFFFFFFFF ∧
    (ofDouble (Float.ofBits 0xC3E0000000000000)).toUInt64 = 0x8000000000000000 ∧
    (ofDouble (Float.ofBits 0xC3E0000000000001)).toUInt64 = 0x8000000000000000 ∧
    (ofDouble (Float.ofBits 0xFFF0000000000000)).toUInt64 = 0x8000000000000000 ∧
    (ofDouble (Float.ofBits 0x43DFFFFFFFFFFFFF)).toUInt64 = 0x7FFFFFFFFFFFFC00 ∧
    (ofDouble (Float.ofBits 0x43E0000000000000)).toUInt64 = 0x7FFFFFFFFFFFFFFF ∧
    (ofDouble (Float.ofBits 0x7FF0000000000000)).toUInt64 = 0x7FFFFFFFFFFFFFFF ∧
    (ofSingle (Float32.ofBits 0x7FC00000)).toUInt64 = 0 ∧
    (ofSingle (Float32.ofBits 0x80000000)).toUInt64 = 0 ∧
    (ofSingle (Float32.ofBits 0xDF000000)).toUInt64 = 0x8000000000000000 ∧
    (ofSingle (Float32.ofBits 0xDF000001)).toUInt64 = 0x8000000000000000 ∧
    (ofSingle (Float32.ofBits 0xFF800000)).toUInt64 = 0x8000000000000000 ∧
    (ofSingle (Float32.ofBits 0x5EFFFFFF)).toUInt64 = 0x7FFFFF8000000000 ∧
    (ofSingle (Float32.ofBits 0x5F000000)).toUInt64 = 0x7FFFFFFFFFFFFFFF ∧
    (toDouble 9007199254740993).toBits = 0x4340000000000000 ∧
    (toDouble 9007199254740995).toBits = 0x4340000000000002 ∧
    (toDouble (-9007199254740993)).toBits = 0xC340000000000000 ∧
    (toDouble (-9007199254740995)).toBits = 0xC340000000000002 ∧
    (toDouble Int64.maxValue).toBits = 0x43E0000000000000 ∧
    (toDouble Int64.minValue).toBits = 0xC3E0000000000000 ∧
    (toDouble (Int64.minValue + 1)).toBits = 0xC3E0000000000000 ∧
    (toSingle 16777217).toBits = 0x4B800000 ∧
    (toSingle 16777219).toBits = 0x4B800002 ∧
    (toSingle (-16777217)).toBits = 0xCB800000 ∧
    (toSingle 4611686293305294849).toBits = 0x5E800001 ∧
    (toSingle (-4611686293305294849)).toBits = 0xDE800001 ∧
    (toSingle Int64.maxValue).toBits = 0x5F000000 ∧
    (toSingle Int64.minValue).toBits = 0xDF000000 := by
  decide +kernel

#print axioms scale_spec
#print axioms special_values

end Examples.Convert

import LeanExe.Build
import LeanExe.Loop
import LeanExe.Float32

/-!
GPT-2 124M in binary32, written for WGSL kernels: every array is built element by element, and
the functions that kernels share are marked `@[inline]`, so that the compiler unfolds them into
each kernel.
-/

namespace LeanExe.Examples.Gpt32

/-- `e^x` in binary32.  The argument is clamped to `[-104, 89]`, which maps a NaN to 89;
`k = nearest (c · log₂ e)` and `r = c - k · ln 2` with `ln 2` in two parts, the first with nine
significant bits so that `k · 0.693359375` is exact.  The Taylor polynomial of degree 7 gives
`e^r`, which is multiplied by `2^k` as two normal powers of two built from their bits, with
`k + 254` taken from the bits of `k + 1.5 · 2^23`.  Against correctly rounded results the error
is at most 1.19 ulp over `[-90, 90]` (review of 2026-10-04); no theorem bounds it. -/
@[inline] def exp32 (x : Float32) : Float32 :=
  let a := if x ≤ 89.0 then x else 89.0
  let c := if -104.0 ≤ a then a else -104.0
  let kf := LeanExe.Float32.nearest (c * 1.44269502162933349609375)
  let r := c - kf * 0.693359375 + kf * 0.000212194441701285541057586669921875
  let p := 1.0 + r * (1.0 + r * (0.5 + r * (0.16666667163372039794921875 +
    r * (0.0416666679084300994873046875 + r * (0.008333333767950534820556640625 +
    r * (0.001388888922519981861114501953125 + r * 0.000198412701138295233249664306640625))))))
  let m := (kf + 12582912.0).toBits.toUInt64 - 1262485250
  let h := m / 2
  p * Float32.ofBits (h * 8388608).toUInt32 * Float32.ofBits ((m - h) * 8388608).toUInt32

/-- `exp32` of each element of `x`. -/
def expArray32 (x : Array Float32) : Array Float32 :=
  LeanExe.build x.size.toUInt64 fun i => exp32 x[i.toNat]!

end LeanExe.Examples.Gpt32

import LeanExe.Dialect.Loop
import LeanExe.Dialect.Build
import LeanExe.Dialect.RepeatWhile
import LeanExe.Dialect.InsertErase
import LeanExe.Dialect.Float32

/-! The thirty-second program of the verified compiler: `log1p`, ported from fdlibm as FreeBSD's
`lib/msun/src` has it at commit `20381bce4b63975494a2f4bc84257f6932e6d379` (`s_log1p.c`, Copyright
(C) 1993 by Sun Microsystems, Inc., freely distributable with this notice).  The code writes
`1 + x = 2 ^ k (1 + f)` with `√2/2 < 1 + f < √2`.  For `k ≠ 0` it keeps the rounding error of
`u = 1 + x` as the correction `c/u`, and for `k = 0` it takes `f = x`.  It computes `log1p f` from
`s = f/(2 + f)` as `f - (f²/2 - s (f²/2 + R))`, where the polynomial `R` of degree 14 in `s`
approximates `(log (1 + s) - log (1 - s))/s - 2` within `2 ^ -58.45`, and adds `k ln 2` with `ln 2`
in two parts.  When `k ≠ 0` and `f` lies in `[-3 · 2 ^ -21, 2 ^ -20)`, where fdlibm's comment says
`|f| < 2 ^ -20`, the code takes `f²/2 (1 - 2f/3)` instead of `R`, and an `x` below `2 ^ -29` in
magnitude gives `x - x²/2`, or `x` below `2 ^ -54`.  fdlibm states an error below one unit in the
last place.  Each constant is written as the bit pattern that fdlibm's source gives beside its
decimal value, and `0.66666666666666666` as the bits of the nearest double.  The dialect has no
floating-point flags, and the expressions that fdlibm evaluates only for their flags keep their
values: `-two54/vzero` is `-two54/0`, and the guard `two54 + x > 0` stays.  fdlibm's signed high
word `hx` is a word here, so a comparison of `hx` with a positive bound also tests its sign bit, and
its signed `k` is two's complement, converted to a double as `Log.logCore` converts its `k`.
`Log1pAccuracy.lean` checks the results against a reference computed with Lean's integers.

The notices of the ported files follow verbatim, as their licenses require.

`s_log1p.c`:

    ====================================================
    Copyright (C) 1993 by Sun Microsystems, Inc. All rights reserved.

    Developed at SunPro, a Sun Microsystems, Inc. business.
    Permission to use, copy, modify, and distribute this
    software is freely granted, provided that this notice
    is preserved.
    ====================================================
-/

namespace Library.Numerics.Float64.Log1p

/-- The end of fdlibm's `log1p` for `1 + x = 2 ^ k (1 + f)`, with `k` in two's complement, the
correction `c` divided by `u`, and `hu`, the high word of `1 + f` or of `(1 + f)/2` without its
exponent, or the word that fdlibm derives from it, 0 only for `f` in `[-3 · 2 ^ -21, 2 ^ -20)`.  For
`k = 0` the correction is not used. -/
def log1pTail (f c : Float) (k hu : UInt64) : Float :=
  let ln2Hi := Float.ofBits 0x3FE62E42FEE00000  --  6.93147180369123816490e-01
  let ln2Lo := Float.ofBits 0x3DEA39EF35793C76  --  1.90821492927058770002e-10
  let Lp1 := Float.ofBits 0x3FE5555555555593    --  6.666666666666735130e-01
  let Lp2 := Float.ofBits 0x3FD999999997FA04    --  3.999999999940941908e-01
  let Lp3 := Float.ofBits 0x3FD2492494229359    --  2.857142874366239149e-01
  let Lp4 := Float.ofBits 0x3FCC71C51D8E78AF    --  2.222219843214978396e-01
  let Lp5 := Float.ofBits 0x3FC7466496CB03DE    --  1.818357216161805012e-01
  let Lp6 := Float.ofBits 0x3FC39A09D078C69F    --  1.531383769920937332e-01
  let Lp7 := Float.ofBits 0x3FC2F112DF3E5244    --  1.479819860511658591e-01
  let hfsq := 0.5 * f * f
  let kd := if k >>> 63 == 1 then -(0 - k).toFloat else k.toFloat
  if hu == 0 then
    if f == 0.0 then
      if k == 0 then 0.0
      else
        let c := c + kd * ln2Lo
        kd * ln2Hi + c
    else
      let R := hfsq * (1.0 - Float.ofBits 0x3FE5555555555555 * f)  -- 0.66666666666666666
      if k == 0 then f - R else kd * ln2Hi - ((R - (kd * ln2Lo + c)) - f)
  else
    let s := f / (2.0 + f)
    let z := s * s
    let R := z * (Lp1 + z * (Lp2 + z * (Lp3 + z * (Lp4 + z * (Lp5 + z * (Lp6 + z * Lp7))))))
    if k == 0 then f - (hfsq - s * (hfsq + R))
    else kd * ln2Hi - ((hfsq - (s * (hfsq + R) + (kd * ln2Lo + c))) - f)

/-- fdlibm's `log1p`, `log (1 + x)`.  `hx` is the high word of `x`, `ax` that of `|x|`, and
`small` is fdlibm's `hx < 0x3FDA827A` for the signed `hx`: a negative `x` or `1 + x` below
`√2` or so.  -1 gives `-∞`, an `x` below -1 or a NaN gives NaN, and `∞` gives `∞`.  From `2 ^ 53`
on, `u` is `x` itself and the correction is 0.  `u` is normalized to `[√2/2, √2)` by setting its
exponent, which adds 1 to `k` when the fraction of `u` reaches that of `√2`. -/
def log1p (x : Float) : Float :=
  let two54 := Float.ofBits 0x4350000000000000  --  1.80143985094819840000e+16
  let hx := x.toBits >>> 32
  let ax := hx &&& 0x7fffffff
  let neg := hx >>> 31 == 1
  let small := neg || hx < 0x3FDA827A
  if small && ax ≥ 0x3ff00000 then
    if x == -1.0 then -two54 / 0.0 else (x - x) / (x - x)
  else if small && ax < 0x3e200000 then
    if two54 + x > 0.0 && ax < 0x3c900000 then x else x - x * x * 0.5
  else if small && ((!neg && hx != 0) || (neg && hx ≤ 0xbfd2bec4)) then
    log1pTail x 0.0 0 1
  else if !neg && hx ≥ 0x7ff00000 then x + x
  else
    let (u, k, c) :=
      if neg || hx < 0x43400000 then
        let u := 1.0 + x
        let k := ((u.toBits >>> 32) >>> 20) - 1023
        let c := if k >>> 63 == 0 && k != 0 then 1.0 - (u - x) else x - (u - 1.0)
        (u, k, c / u)
      else (x, ((x.toBits >>> 32) >>> 20) - 1023, 0.0)
    let hu := (u.toBits >>> 32) &&& 0x000fffff
    let low := u.toBits &&& 0xFFFFFFFF
    if hu < 0x6a09e then
      log1pTail (Float.ofBits (((hu ||| 0x3ff00000) <<< 32) ||| low) - 1.0) c k hu
    else
      log1pTail (Float.ofBits (((hu ||| 0x3fe00000) <<< 32) ||| low) - 1.0) c (k + 1)
        ((0x00100000 - hu) >>> 2)

end Library.Numerics.Float64.Log1p

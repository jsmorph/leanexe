import Verified.Reflect.Command

/-! The thirty-third program of the verified compiler: `atan` and `atan2`, ported from fdlibm as
FreeBSD's `lib/msun/src` has it at commit `20381bce4b63975494a2f4bc84257f6932e6d379` (`s_atan.c`
and `e_atan2.c`, Copyright (C) 1993 by Sun Microsystems, Inc., freely distributable with this
notice).  `atan` evaluates an odd polynomial of degree 23 directly for `|x| < 7/16`, and above
that reduces `|x|` to `t` with `atan |x| = atan c + atan t` for `c` one of `1/2`, `1`, `3/2`, and
`∞`, adding `atan c` in two parts from fdlibm's tables `atanhi` and `atanlo`.  `atan2 y x` handles
the signed zeros, the infinities, and NaN by IEEE 754's rules, gives `atan y` for `x = 1`, `±π/2`
when `|y/x|` exceeds `2 ^ 60` or so, `±π` when `x < 0` and `|y/x|` is below `2 ^ -60` or so, and
otherwise `atan |y/x|`, placed in the quadrant of `(x, y)` with `π` in two parts.  fdlibm
states no error bound for either function.  Each constant is written as the bit pattern that
fdlibm's source gives beside its decimal value, and `1.0e+300` and `1.0e-300`, which serve only to
raise the inexact flag, as the bits of those decimals.  The dialect has no floating-point flags,
and the expressions that fdlibm evaluates only for their flags keep their values: the guard
`huge + x > 1` stays, and `π + tiny` is `π` rounded.  fdlibm's index `id = -1` of the direct
polynomial is 4 here, its four table entries are selected by comparisons, and its signed high
words are words, so a comparison with a positive bound also tests the sign bit.  `atan2`'s
`k = (iy - ix) >> 20` is the arithmetic shift of the difference in two's complement, and
`nan_mix (x, y)` is `x + y`.  `AtanAccuracy.lean` checks the results against a reference computed
with Lean's integers.

The notices of the ported files follow verbatim, as their licenses require.

`s_atan.c`:

    ====================================================
    Copyright (C) 1993 by Sun Microsystems, Inc. All rights reserved.

    Developed at SunPro, a Sun Microsystems, Inc. business.
    Permission to use, copy, modify, and distribute this
    software is freely granted, provided that this notice
    is preserved.
    ====================================================

`e_atan2.c`:

    ====================================================
    Copyright (C) 1993 by Sun Microsystems, Inc. All rights reserved.

    Developed at SunSoft, a Sun Microsystems, Inc. business.
    Permission to use, copy, modify, and distribute this
    software is freely granted, provided that this notice
    is preserved.
    ====================================================
-/

namespace Verified.Examples.Atan

/-- fdlibm's `atan`.  `ix` is the high word of `|x|`.  From `2 ^ 66` on, the result is `±π/2`
rounded, and NaN gives NaN. -/
def atan (x : Float) : Float :=
  let atanhi0 := Float.ofBits 0x3FDDAC670561BB4F  -- atan(0.5)hi 4.63647609000806093515e-01
  let atanhi1 := Float.ofBits 0x3FE921FB54442D18  -- atan(1.0)hi 7.85398163397448278999e-01
  let atanhi2 := Float.ofBits 0x3FEF730BD281F69B  -- atan(1.5)hi 9.82793723247329054082e-01
  let atanhi3 := Float.ofBits 0x3FF921FB54442D18  -- atan(inf)hi 1.57079632679489655800e+00
  let atanlo0 := Float.ofBits 0x3C7A2B7F222F65E2  -- atan(0.5)lo 2.26987774529616870924e-17
  let atanlo1 := Float.ofBits 0x3C81A62633145C07  -- atan(1.0)lo 3.06161699786838301793e-17
  let atanlo2 := Float.ofBits 0x3C7007887AF0CBBD  -- atan(1.5)lo 1.39033110312309984516e-17
  let atanlo3 := Float.ofBits 0x3C91A62633145C07  -- atan(inf)lo 6.12323399573676603587e-17
  let aT0 := Float.ofBits 0x3FD555555555550D   --  3.33333333333329318027e-01
  let aT1 := Float.ofBits 0xBFC999999998EBC4   -- -1.99999999998764832476e-01
  let aT2 := Float.ofBits 0x3FC24924920083FF   --  1.42857142725034663711e-01
  let aT3 := Float.ofBits 0xBFBC71C6FE231671   -- -1.11111104054623557880e-01
  let aT4 := Float.ofBits 0x3FB745CDC54C206E   --  9.09088713343650656196e-02
  let aT5 := Float.ofBits 0xBFB3B0F2AF749A6D   -- -7.69187620504482999495e-02
  let aT6 := Float.ofBits 0x3FB10D66A0D03D51   --  6.66107313738753120669e-02
  let aT7 := Float.ofBits 0xBFADDE2D52DEFD9A   -- -5.83357013379057348645e-02
  let aT8 := Float.ofBits 0x3FA97B4B24760DEB   --  4.97687799461593236017e-02
  let aT9 := Float.ofBits 0xBFA2B4442C6A6C2F   -- -3.65315727442169155270e-02
  let aT10 := Float.ofBits 0x3F90AD3AE322DA11  --  1.62858201153657823623e-02
  let huge := Float.ofBits 0x7E37E43C8800759C  --  1.0e+300
  let hx := x.toBits >>> 32
  let ix := hx &&& 0x7fffffff
  let neg := hx >>> 31 == 1
  if ix ≥ 0x44100000 then
    if ix > 0x7ff00000 || (ix == 0x7ff00000 && x.toBits &&& 0xFFFFFFFF != 0) then x + x
    else if neg then -atanhi3 - atanlo3 else atanhi3 + atanlo3
  else if ix < 0x3e400000 && huge + x > 1.0 then x
  else
    let (id, t) :=
      if ix < 0x3fdc0000 then ((4 : UInt64), x)
      else
        let a := x.abs
        if ix < 0x3ff30000 then
          if ix < 0x3fe60000 then ((0 : UInt64), (2.0 * a - 1.0) / (2.0 + a))
          else ((1 : UInt64), (a - 1.0) / (a + 1.0))
        else if ix < 0x40038000 then ((2 : UInt64), (a - 1.5) / (1.0 + 1.5 * a))
        else ((3 : UInt64), -1.0 / a)
    let z := t * t
    let w := z * z
    let s1 := z * (aT0 + w * (aT2 + w * (aT4 + w * (aT6 + w * (aT8 + w * aT10)))))
    let s2 := w * (aT1 + w * (aT3 + w * (aT5 + w * (aT7 + w * aT9))))
    if id == 4 then t - t * (s1 + s2)
    else
      let hi := if id == 0 then atanhi0 else if id == 1 then atanhi1
        else if id == 2 then atanhi2 else atanhi3
      let lo := if id == 0 then atanlo0 else if id == 1 then atanlo1
        else if id == 2 then atanlo2 else atanlo3
      let z := hi - ((t * (s1 + s2) - lo) - t)
      if neg then -z else z

/-- fdlibm's `atan2 y x`, the argument of `(x, y)`.  `ix` and `iy` are the high words of `|x|`
and `|y|`, and `lx` and `ly` the low words.  `m` is twice the sign bit of `x` plus that of `y`.
The NaN test is fdlibm's: `(lx | -lx) >> 31` is 1 when the low word is not 0. -/
def atan2 (y x : Float) : Float :=
  let tiny := Float.ofBits 0x01A56E1FC2F8F359    --  1.0e-300
  let pi_o_4 := Float.ofBits 0x3FE921FB54442D18  --  7.8539816339744827900E-01
  let pi_o_2 := Float.ofBits 0x3FF921FB54442D18  --  1.5707963267948965580E+00
  let pi := Float.ofBits 0x400921FB54442D18      --  3.1415926535897931160E+00
  let pi_lo := Float.ofBits 0x3CA1A62633145C07   --  1.2246467991473531772E-16
  let hx := x.toBits >>> 32
  let lx := x.toBits &&& 0xFFFFFFFF
  let ix := hx &&& 0x7fffffff
  let hy := y.toBits >>> 32
  let ly := y.toBits &&& 0xFFFFFFFF
  let iy := hy &&& 0x7fffffff
  if (ix ||| ((lx ||| ((0 - lx) &&& 0xFFFFFFFF)) >>> 31)) > 0x7ff00000 ||
      (iy ||| ((ly ||| ((0 - ly) &&& 0xFFFFFFFF)) >>> 31)) > 0x7ff00000 then x + y
  else if hx == 0x3ff00000 && lx == 0 then atan y
  else
    let m := ((hy >>> 31) &&& (1 : UInt64)) ||| ((hx >>> 30) &&& (2 : UInt64))
    if (iy ||| ly) == 0 then
      if m == 0 || m == 1 then y else if m == 2 then pi + tiny else -pi - tiny
    else if (ix ||| lx) == 0 then
      if hy >>> 31 == 1 then -pi_o_2 - tiny else pi_o_2 + tiny
    else if ix == 0x7ff00000 then
      if iy == 0x7ff00000 then
        if m == 0 then pi_o_4 + tiny else if m == 1 then -pi_o_4 - tiny
        else if m == 2 then 3.0 * pi_o_4 + tiny else -3.0 * pi_o_4 - tiny
      else
        if m == 0 then 0.0 else if m == 1 then -0.0 else if m == 2 then pi + tiny else -pi - tiny
    else if iy == 0x7ff00000 then
      if hy >>> 31 == 1 then -pi_o_2 - tiny else pi_o_2 + tiny
    else
      let d := iy - ix
      let k := (d >>> 20) ||| (if d >>> 63 == 1 then 0xFFFFF00000000000 else 0)
      let (z, m) :=
        if k >>> 63 == 0 && k > 60 then (pi_o_2 + 0.5 * pi_lo, m &&& (1 : UInt64))
        else if hx >>> 31 == 1 && k >>> 63 == 1 && k < 0xFFFFFFFFFFFFFFC4 then (0.0, m)
        else (atan (y / x).abs, m)
      if m == 0 then z else if m == 1 then -z
      else if m == 2 then pi - (z - pi_lo) else (z - pi_lo) - pi

verified_compile compiled := [atan, atan2]

end Verified.Examples.Atan

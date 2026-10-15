import Verified.Reflect.Command

/-! The fortieth program of the verified compiler: `log10`, ported from fdlibm as FreeBSD's
`lib/msun/src` has it at commit `20381bce4b63975494a2f4bc84257f6932e6d379` (`e_log10.c` and
`k_log.h`, Copyright (C) 1993 by Sun Microsystems, Inc., freely distributable with this notice).
Arm's optimized-routines has no double `log10` in `math/`, only `log10f`.  The code writes
`x = 2 ^ k (1 + f)` with `√2/2 < 1 + f < √2`, computes `log (1 + f) - f + f²/2` with `k_log.h`'s
`k_log1p`, from `s = f/(2 + f)` and a polynomial of degree 14 in `s` that approximates
`(log (1 + s) - log (1 - s))/s - 2` within `2 ^ -58.45`, and forms
`(f - f²/2 + k_log1p f)/ln 10 + k log10 2` with `f - f²/2` split at its high 32 bits and
`1/ln 10` and `log10 2` in two parts each.  `k_log.h` states an error below one unit in the last
place for the natural logarithm, and `e_log10.c` states none for `log10`.  Each constant is
written as the bit pattern that fdlibm's source gives beside its decimal value.  The dialect has no
floating-point flags, and the expressions that fdlibm evaluates only for their flags keep their
values: `-two54/vzero` is `-two54/0` and `(x - x)/zero` is `(x - x)/0`.  fdlibm's signed high word
`hx` and its signed `k` are words here: a comparison of `hx` with a positive bound also tests its
sign bit, and `k` is two's complement, converted to a double as `Log.logCore` converts its `k`.
`Log2Accuracy.lean` checks the results against a reference computed with Lean's integers.

The notices of the ported files follow verbatim, as their licenses require.

`e_log10.c` and `k_log.h`:

    ====================================================
    Copyright (C) 1993 by Sun Microsystems, Inc. All rights reserved.

    Developed at SunSoft, a Sun Microsystems, Inc. business.
    Permission to use, copy, modify, and distribute this
    software is freely granted, provided that this notice
    is preserved.
    ====================================================
-/

namespace Verified.Examples.Log10

/-- `k_log.h`'s `k_log1p`: `log (1 + f) - f + f²/2` for `1 + f` in about `[√2/2, √2]`, as
`s (f²/2 + R)` with `s = f/(2 + f)` and `R` the polynomial in `s`. -/
def kLog1p (f : Float) : Float :=
  let Lg1 := Float.ofBits 0x3FE5555555555593  -- 6.666666666666735130e-01
  let Lg2 := Float.ofBits 0x3FD999999997FA04  -- 3.999999999940941908e-01
  let Lg3 := Float.ofBits 0x3FD2492494229359  -- 2.857142874366239149e-01
  let Lg4 := Float.ofBits 0x3FCC71C51D8E78AF  -- 2.222219843214978396e-01
  let Lg5 := Float.ofBits 0x3FC7466496CB03DE  -- 1.818357216161805012e-01
  let Lg6 := Float.ofBits 0x3FC39A09D078C69F  -- 1.531383769920937332e-01
  let Lg7 := Float.ofBits 0x3FC2F112DF3E5244  -- 1.479819860511658591e-01
  let s := f / (2.0 + f)
  let z := s * s
  let w := z * z
  let t1 := w * (Lg2 + w * (Lg4 + w * Lg6))
  let t2 := z * (Lg1 + w * (Lg3 + w * (Lg5 + w * Lg7)))
  let R := t2 + t1
  let hfsq := 0.5 * f * f
  s * (hfsq + R)

/-- fdlibm's `log10`.  `hx` is the high word of `x` and `lx` its low word.  `±0` gives `-∞`, a
value with the sign bit set gives NaN, `+∞` and a NaN without it give `x + x`, and 1 gives `+0`.
A subnormal is scaled by `2 ^ 54`.  `i` adds 1 to `k` when the fraction of `x` reaches that of
`√2`, and the exponent field of `x` becomes that of 1 or `1/2`. -/
def log10 (x : Float) : Float :=
  let two54 := Float.ofBits 0x4350000000000000      -- 1.80143985094819840000e+16
  let ivln10hi := Float.ofBits 0x3FDBCB7B15200000   -- 4.34294481878168880939e-01
  let ivln10lo := Float.ofBits 0x3DBB9438CA9AADD5   -- 2.50829467116452752298e-11
  let log10_2hi := Float.ofBits 0x3FD34413509F6000  -- 3.01029995663611771306e-01
  let log10_2lo := Float.ofBits 0x3D59FEF311F12B36  -- 3.69423907715893078616e-13
  let hx := x.toBits >>> 32
  let lx := x.toBits &&& 0xFFFFFFFF
  let neg := hx >>> 31 == 1
  if (neg || hx < 0x00100000) && ((hx &&& 0x7fffffff) ||| lx) == 0 then -two54 / 0.0
  else if neg then (x - x) / 0.0
  else
    let (x, k) : Float × UInt64 := if hx < 0x00100000 then (x * two54, 0 - 54) else (x, 0)
    let hx := x.toBits >>> 32
    if hx ≥ 0x7ff00000 then x + x
    else if hx == 0x3ff00000 && lx == 0 then 0.0
    else
      let k := k + (hx >>> 20) - 1023
      let hx := hx &&& 0x000fffff
      let i := (hx + 0x95f64) &&& 0x100000
      let x :=
        Float.ofBits (((hx ||| (i ^^^ 0x3ff00000)) <<< 32) ||| (x.toBits &&& 0xFFFFFFFF))
      let k := k + (i >>> 20)
      let y := if k >>> 63 == 1 then -(0 - k).toFloat else k.toFloat
      let f := x - 1.0
      let hfsq := 0.5 * f * f
      let r := kLog1p f
      let hi := Float.ofBits ((f - hfsq).toBits &&& 0xFFFFFFFF00000000)
      let lo := (f - hi) - hfsq + r
      let valHi := hi * ivln10hi
      let y2 := y * log10_2hi
      let valLo := y * log10_2lo + (lo + hi) * ivln10lo + lo * ivln10hi
      let w := y2 + valHi
      let valLo := valLo + ((y2 - w) + valHi)
      valLo + w

verified_compile compiled := [kLog1p, log10]

end Verified.Examples.Log10

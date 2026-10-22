import LeanExe.Dialect.Loop
import LeanExe.Dialect.Build
import LeanExe.Dialect.RepeatWhile
import LeanExe.Dialect.InsertErase
import LeanExe.Dialect.Float32

/-! The thirty-fourth program of the verified compiler: `asin` and `acos`, ported from fdlibm as
FreeBSD's `lib/msun/src` has it at commit `20381bce4b63975494a2f4bc84257f6932e6d379` (`e_asin.c` and
`e_acos.c`, Copyright (C) 1993 by Sun Microsystems, Inc., freely distributable with this notice).
Both use the quotient `w (z) = p (z)/q (z)` of `e_asin.c`, which approximates `(asin √z - √z)/√z`:
`p (z) = z P (z)`, and fdlibm's comment bounds `P/q` within `2 ^ -58.75` of
`(asin √z - √z)/z^(3/2)`, a bound for exact coefficients: the stored `pS0` is `1/6` rounded, which
alone gives about `2 ^ -56.58` (`AsinKernelPoly`).  Below `1/2` in magnitude,
`asin x = x + x w (x²)` and `acos x = π/2 - (x + x w (x²))`.  From `1/2` on, both use
`asin √z = √z + √z w (z)`: `asin |x| = π/2 - 2 asin √z` with `z = (1 - |x|)/2`, `acos x = 2 asin √z`
for positive `x`, and `acos x = π - 2 asin √z` with `z = (1 + x)/2` for negative `x`.  Where the
result needs it, `√z` is split into its high 32 bits `f` and the correction `(z - f²)/(√z + f)`, and
`π/2` comes in two parts.  fdlibm states no error bound for either function.  Each constant is
written as the bit pattern that fdlibm's source gives beside its decimal value, and `1.0e+300` as
the bits of that decimal.  The dialect has no floating-point flags, and the expressions that fdlibm
evaluates only for their flags keep their values: the guard `huge + x > 1` stays.  fdlibm computes
`p` and `q` in each branch, and here `asinRatio` computes `p/q` with the same operations.  fdlibm's
signed high word `hx` is a word, so its sign is its top bit.  `AsinAccuracy.lean` checks the results
against a reference computed with Lean's integers.

The notices of the ported files follow verbatim, as their licenses require.

`e_asin.c` and `e_acos.c`:

    ====================================================
    Copyright (C) 1993 by Sun Microsystems, Inc. All rights reserved.

    Developed at SunSoft, a Sun Microsystems, Inc. business.
    Permission to use, copy, modify, and distribute this
    software is freely granted, provided that this notice
    is preserved.
    ====================================================
-/

namespace Library.Numerics.Float64.Asin

/-- `p (t)/q (t)`, fdlibm's rational approximation of `(asin √t - √t)/√t`. -/
def asinRatio (t : Float) : Float :=
  let pS0 := Float.ofBits 0x3FC5555555555555  --  1.66666666666666657415e-01
  let pS1 := Float.ofBits 0xBFD4D61203EB6F7D  -- -3.25565818622400915405e-01
  let pS2 := Float.ofBits 0x3FC9C1550E884455  --  2.01212532134862925881e-01
  let pS3 := Float.ofBits 0xBFA48228B5688F3B  -- -4.00555345006794114027e-02
  let pS4 := Float.ofBits 0x3F49EFE07501B288  --  7.91534994289814532176e-04
  let pS5 := Float.ofBits 0x3F023DE10DFDF709  --  3.47933107596021167570e-05
  let qS1 := Float.ofBits 0xC0033A271C8A2D4B  -- -2.40339491173441421878e+00
  let qS2 := Float.ofBits 0x40002AE59C598AC8  --  2.02094576023350569471e+00
  let qS3 := Float.ofBits 0xBFE6066C1B8D0159  -- -6.88283971605453293030e-01
  let qS4 := Float.ofBits 0x3FB3B8C5B12E9282  --  7.70381505559019352791e-02
  let p := t * (pS0 + t * (pS1 + t * (pS2 + t * (pS3 + t * (pS4 + t * pS5)))))
  let q := 1.0 + t * (qS1 + t * (qS2 + t * (qS3 + t * qS4)))
  p / q

/-- fdlibm's `asin`.  `ix` is the high word of `|x|` and `lx` the low word of `x`.  `±1` gives
`±π/2`, and a magnitude above 1 or a NaN gives NaN.  Above `0.975` in magnitude the result is
`π/2 - 2 (s + s w)`, and from `1/2` to `0.975` it is formed around `π/4` with the split `√z`. -/
def asin (x : Float) : Float :=
  let huge := Float.ofBits 0x7E37E43C8800759C     --  1.0e+300
  let pio2_hi := Float.ofBits 0x3FF921FB54442D18  --  1.57079632679489655800e+00
  let pio2_lo := Float.ofBits 0x3C91A62633145C07  --  6.12323399573676603587e-17
  let pio4_hi := Float.ofBits 0x3FE921FB54442D18  --  7.85398163397448278999e-01
  let hx := x.toBits >>> 32
  let ix := hx &&& 0x7fffffff
  let lx := x.toBits &&& 0xFFFFFFFF
  if ix ≥ 0x3ff00000 then
    if ((ix - 0x3ff00000) ||| lx) == 0 then x * pio2_hi + x * pio2_lo else (x - x) / (x - x)
  else if ix < 0x3fe00000 then
    if ix < 0x3e500000 && huge + x > 1.0 then x
    else x + x * asinRatio (x * x)
  else
    let t := (1.0 - x.abs) * 0.5
    let r := asinRatio t
    let s := t.sqrt
    let t :=
      if ix ≥ 0x3FEF3333 then pio2_hi - (2.0 * (s + s * r) - pio2_lo)
      else
        let w := Float.ofBits (s.toBits &&& 0xFFFFFFFF00000000)
        let c := (t - w * w) / (s + w)
        let p := 2.0 * s * r - (pio2_lo - 2.0 * c)
        let q := pio4_hi - 2.0 * w
        pio4_hi - (p - q)
    if hx >>> 31 == 0 then t else -t

/-- fdlibm's `acos`.  `ix` is the high word of `|x|` and `lx` the low word of `x`.  1 gives 0, -1
gives `π`, and a magnitude above 1 or a NaN gives NaN.  Below `2 ^ -57` in magnitude the result
is `π/2` rounded. -/
def acos (x : Float) : Float :=
  let pi := Float.ofBits 0x400921FB54442D18       --  3.14159265358979311600e+00
  let pio2_hi := Float.ofBits 0x3FF921FB54442D18  --  1.57079632679489655800e+00
  let pio2_lo := Float.ofBits 0x3C91A62633145C07  --  6.12323399573676603587e-17
  let hx := x.toBits >>> 32
  let ix := hx &&& 0x7fffffff
  let lx := x.toBits &&& 0xFFFFFFFF
  if ix ≥ 0x3ff00000 then
    if ((ix - 0x3ff00000) ||| lx) == 0 then
      if hx >>> 31 == 0 then 0.0 else pi + 2.0 * pio2_lo
    else (x - x) / (x - x)
  else if ix < 0x3fe00000 then
    if ix ≤ 0x3c600000 then pio2_hi + pio2_lo
    else pio2_hi - (x - (pio2_lo - x * asinRatio (x * x)))
  else if hx >>> 31 == 1 then
    let z := (1.0 + x) * 0.5
    let s := z.sqrt
    let w := asinRatio z * s - pio2_lo
    pi - 2.0 * (s + w)
  else
    let z := (1.0 - x) * 0.5
    let s := z.sqrt
    let df := Float.ofBits (s.toBits &&& 0xFFFFFFFF00000000)
    let c := (z - df * df) / (s + df)
    let w := asinRatio z * s + c
    2.0 * (df + w)

end Library.Numerics.Float64.Asin

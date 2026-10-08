import Verified.Reflect.Command

/-! The twenty-ninth program of the verified compiler: `expm1` and `tanh`, ported from fdlibm as
FreeBSD's `lib/msun/src` has it at commit `20381bce4b63975494a2f4bc84257f6932e6d379` (`s_expm1.c`
and `s_tanh.c`, Copyright (C) 1993 by Sun Microsystems, Inc., freely distributable with this
notice).  `expm1` writes `x = k ln 2 + r` with `|r|` at most about `ln 2/2`, using `ln 2` in two
parts and keeping the rounding error of `r` as a correction `c`, approximates `expm1 r` by a
rational function built on a polynomial of degree 5 in `r²`, and scales by `2 ^ k` in the form that
loses the least precision for each range of `k`.  fdlibm states an error below one unit in the
last place for `expm1`.  `tanh` is `x` below `2 ^ -28` in magnitude and otherwise `tanh |x|` with
the sign of `x`, where `tanh |x|` is `-t/(t + 2)` with `t = expm1 (-2|x|)` below 1,
`1 - 2/(t + 2)` with `t = expm1 (2|x|)` below 22, and 1 from 22 on.  fdlibm states no error bound
for `tanh`.  Each constant is written as the bit pattern that fdlibm's
source gives beside its decimal value, and `1.0e+300` and `1.0e-300`, which raise the inexact and
overflow flags, as the bits of those decimals.  The dialect has no floating-point flags, and the
expressions that fdlibm evaluates only for their flags keep their values: `x - ((huge + x) -
(huge + x))` is `x`.  fdlibm's signed `k` is a sign and a magnitude here, since the dialect
converts only between floats and unsigned words.  `TanhAccuracy.lean` checks the results against
references computed with Lean's integers. -/

namespace Verified.Examples.Tanh

/-- fdlibm's `expm1` from `x` in the primary range on, with the correction `c` and `k` as its sign
`neg` and its magnitude `m`.  With `hxs = x²/2`, `r1` approximates `(6/x) (coth (x/2) - 2/x)`,
and `e = hxs · (r1 - t)/(6 - x t)` with `t = 3 - r1 x/2` is the remainder that makes
`x - (x e - hxs)` equal `expm1 x`.  For `k ≠ 0` the result is
`2 ^ k (x - (x e - c x - c - hxs) + 1) - 1`, in the order fdlibm chooses for each range of `k`. -/
def expm1Kernel (x c : Float) (neg : Bool) (m : UInt64) : Float :=
  let Q1 := Float.ofBits 0xBFA11111111110F4  -- -3.33333333333331316428e-02
  let Q2 := Float.ofBits 0x3F5A01A019FE5585  --  1.58730158725481460165e-03
  let Q3 := Float.ofBits 0xBF14CE199EAADBB7  -- -7.93650757867487942473e-05
  let Q4 := Float.ofBits 0x3ED0CFCA86E65239  --  4.00821782732936239552e-06
  let Q5 := Float.ofBits 0xBE8AFDB76E09C32D  -- -2.01099218183624371326e-07
  let hfx := 0.5 * x
  let hxs := x * hfx
  let r1 := 1.0 + hxs * (Q1 + hxs * (Q2 + hxs * (Q3 + hxs * (Q4 + hxs * Q5))))
  let t := 3.0 - r1 * hfx
  let e := hxs * ((r1 - t) / (6.0 - x * t))
  if m == 0 then x - (x * e - hxs)
  else
    let twopk := Float.ofBits ((if neg then 0x3ff - m else 0x3ff + m) <<< 52)
    let e := x * (e - c) - c
    let e := e - hxs
    if m == 1 then
      if neg then 0.5 * (x - e) - 0.5
      else if x < -0.25 then -2.0 * (e - (x + 0.5))
      else 1.0 + 2.0 * (x - e)
    else if neg || m > 56 then
      let y := 1.0 - (e - x)
      let y := if !neg && m == 1024 then y * 2.0 * Float.ofBits 0x7FE0000000000000
        else y * twopk
      y - 1.0
    else if m < 20 then
      let t := Float.ofBits (((0x3ff00000 : UInt64) - (0x200000 >>> m)) <<< 32)  -- 1 - 2 ^ -k
      let y := t - (e - x)
      y * twopk
    else
      let t := Float.ofBits (((0x3ff : UInt64) - m) <<< 52)  -- 2 ^ -k
      let y := x - (e + t)
      let y := y + 1.0
      y * twopk

/-- fdlibm's `expm1`, `exp x - 1`.  `hx` is the high word of `|x|`, and the thresholds compare
high words.  NaN gives NaN, `∞` gives `∞`, `-∞` gives -1, `x` above fdlibm's `o_threshold`, about
709.78, gives `∞`, and a negative `x` whose high word reaches that of `56 ln 2` gives -1.  When the
high word exceeds that of `ln 2/2`, the reduction subtracts `k ln 2` in two parts, with `k = ±1`
while the high word is below that of `1.5 ln 2`, and otherwise with `k` the truncation of the
rounded `x/ln 2 ± 1/2`, whose sign is that of `x`.  When the high word is below that of
`2 ^ -54`, the result is `x`. -/
def expm1 (x : Float) : Float :=
  let huge := Float.ofBits 0x7E37E43C8800759C    --  1.0e+300
  let tiny := Float.ofBits 0x01A56E1FC2F8F359    --  1.0e-300
  let ln2Hi := Float.ofBits 0x3FE62E42FEE00000   --  6.93147180369123816490e-01
  let ln2Lo := Float.ofBits 0x3DEA39EF35793C76   --  1.90821492927058770002e-10
  let invln2 := Float.ofBits 0x3FF71547652B82FE  --  1.44269504088896338700e+00
  let neg := x.toBits >>> 63 == 1
  let hx := (x.toBits >>> 32) &&& 0x7fffffff
  if hx ≥ 0x7ff00000 then
    if x.toBits &&& 0xFFFFFFFFFFFFF != 0 then x + x else if neg then -1.0 else x
  else if hx ≥ 0x40862E42 && x > Float.ofBits 0x40862E42FEFA39EF then huge * huge
  else if hx ≥ 0x4043687A && neg && x + tiny < 0.0 then tiny - 1.0
  else if hx > 0x3fd62e42 then
    let (hi, lo, m) :=
      if hx < 0x3FF0A2B2 then
        if neg then (x + ln2Hi, -ln2Lo, (1 : UInt64)) else (x - ln2Hi, ln2Lo, (1 : UInt64))
      else if neg then
        let m := (-(invln2 * x - 0.5)).toUInt64
        let t := -m.toFloat
        (x - t * ln2Hi, t * ln2Lo, m)
      else
        let m := (invln2 * x + 0.5).toUInt64
        let t := m.toFloat
        (x - t * ln2Hi, t * ln2Lo, m)
    let y := hi - lo
    expm1Kernel y ((hi - y) - lo) neg m
  else if hx < 0x3c900000 then x - ((huge + x) - (huge + x))
  else expm1Kernel x 0.0 false 0

/-- fdlibm's `tanh`.  `ix` is the high word of `|x|`.  An infinity gives `±1` and NaN gives NaN,
as `1/x ± 1`. -/
def tanh (x : Float) : Float :=
  let ix := (x.toBits >>> 32) &&& 0x7fffffff
  let neg := x.toBits >>> 63 == 1
  if ix ≥ 0x7ff00000 then if neg then 1.0 / x - 1.0 else 1.0 / x + 1.0
  else if ix < 0x3e300000 && Float.ofBits 0x7E37E43C8800759C + x > 1.0 then x
  else
    let z :=
      if ix < 0x40360000 then
        if ix ≥ 0x3ff00000 then
          let t := expm1 (2.0 * x.abs)
          1.0 - 2.0 / (t + 2.0)
        else
          let t := expm1 (-2.0 * x.abs)
          (-t) / (t + 2.0)
      else 1.0 - Float.ofBits 0x01A56E1FC2F8F359
    if neg then -z else z

verified_compile compiled := [expm1Kernel, expm1, tanh]

end Verified.Examples.Tanh

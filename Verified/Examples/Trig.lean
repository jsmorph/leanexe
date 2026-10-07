import Verified.Reflect.Command

/-! The twenty-third program of the verified compiler: `sin` and `cos`, ported from fdlibm as
FreeBSD's `lib/msun/src` has it (`k_sin.c`, `k_cos.c`, `s_sin.c`, `s_cos.c`, and
`e_rem_pio2.c`, Copyright (C) 1993 by Sun Microsystems, Inc., freely distributable with this
notice).  An argument above `π/4` in magnitude is reduced by multiples of `π/2` to `y0 + y1` in
`[-π/4, π/4]`, and the kernels evaluate fdlibm's minimax polynomials there; fdlibm states an error
below one unit in the last place.  Each constant is written as the bit pattern that fdlibm's source
gives beside its decimal value.  Lean's `Float.sin` is `@[extern "sin"]`, the C library's function,
with no definition in Lean, so the compiler's theorem is about these definitions, and the tests
compare them with the C library.

The reduction covers `|x| < 2 ^ 20 · π/2`, by fdlibm's special cases up to `9π/4` and its
three-step Cody–Waite reduction above.  A larger argument gives NaN until the program gains
fdlibm's Payne–Hanek reduction.  The reduction takes `|x|`, by `sin (-x) = -sin x` and
`cos (-x) = cos x`, so its quadrant count is a word; fdlibm reduces `x` itself, with a signed
count. -/

namespace Verified.Examples.Trig

/-- fdlibm's `__kernel_sin`: `sin (x + y)` for `|x| ≤ π/4` with the tail `y`, which `tail` says
is not zero.  The polynomial of degree 13 approximates `sin x / x` within `2 ^ -58`. -/
def kernelSin (x y : Float) (tail : Bool) : Float :=
  let S1 := Float.ofBits 0xBFC5555555555549  -- -1.66666666666666324348e-01
  let S2 := Float.ofBits 0x3F8111111110F8A6  --  8.33333333332248946124e-03
  let S3 := Float.ofBits 0xBF2A01A019C161D5  -- -1.98412698298579493134e-04
  let S4 := Float.ofBits 0x3EC71DE357B1FE7D  --  2.75573137070700676789e-06
  let S5 := Float.ofBits 0xBE5AE5E68A2B9CEB  -- -2.50507602534068634195e-08
  let S6 := Float.ofBits 0x3DE5D93A5ACFD57C  --  1.58969099521155010221e-10
  let z := x * x
  let w := z * z
  let r := S2 + z * (S3 + z * S4) + z * w * (S5 + z * S6)
  let v := z * x
  if tail then x - ((z * (0.5 * y - v * r) - y) - v * S1) else x + v * (S1 + z * r)

/-- fdlibm's `__kernel_cos`: `cos (x + y)` for `|x| ≤ π/4` with the tail `y`.  The polynomial of
degree 14 approximates `cos x` within `2 ^ -58`, and `w + ((1 - w) - hz)` carries the rounding of
`1 - x * x / 2`. -/
def kernelCos (x y : Float) : Float :=
  let C1 := Float.ofBits 0x3FA555555555554C  --  4.16666666666666019037e-02
  let C2 := Float.ofBits 0xBF56C16C16C15177  -- -1.38888888888741095749e-03
  let C3 := Float.ofBits 0x3EFA01A019CB1590  --  2.48015872894767294178e-05
  let C4 := Float.ofBits 0xBE927E4F809C52AD  -- -2.75573143513906633035e-07
  let C5 := Float.ofBits 0x3E21EE9EBDB4B1C4  --  2.08757232129817482790e-09
  let C6 := Float.ofBits 0xBDA8FAE9BE8838D4  -- -1.13596475577881948265e-11
  let z := x * x
  let w := z * z
  let r := z * (C1 + z * (C2 + z * C3)) + w * w * (C4 + z * (C5 + z * C6))
  let hz := 0.5 * z
  let w := 1.0 - hz
  w + (((1.0 - w) - hz) + (z * r - x * y))

/-- `x - k · π/2` as `y0 + y1` for a small multiple `k`, in one step good to 85 bits, as fdlibm's
special cases up to `9π/4` compute it. -/
def remSmall (x k : Float) : Float × Float :=
  let pio2_1 := Float.ofBits 0x3FF921FB54400000   -- first 33 bits of π/2
  let pio2_1t := Float.ofBits 0x3DD0B4611A626331  -- π/2 - pio2_1
  let z := x - k * pio2_1
  let y0 := z - k * pio2_1t
  (y0, (z - y0) - k * pio2_1t)

/-- fdlibm's medium case of `__ieee754_rem_pio2`, for `0 < x < 2 ^ 20 · π/2` with high word `ix`:
the count `n` of `π/2`, the nearest integer to `x · 2/π`, and `x - n · π/2` as `y0 + y1`.  `π/2`
is subtracted in pieces of 33 bits, so that each product with `n` is exact, in one step good to 85
bits, a second when the first cancels more than 16 bits, good to 118, and a third when the second
cancels more than 49, good to 151. -/
def remMedium (x : Float) (ix : UInt64) : UInt64 × Float × Float :=
  let invpio2 := Float.ofBits 0x3FE45F306DC9C883  -- 53 bits of 2/π
  let pio2_1 := Float.ofBits 0x3FF921FB54400000   -- first 33 bits of π/2
  let pio2_1t := Float.ofBits 0x3DD0B4611A626331  -- π/2 - pio2_1
  let pio2_2 := Float.ofBits 0x3DD0B4611A600000   -- second 33 bits of π/2
  let pio2_2t := Float.ofBits 0x3BA3198A2E037073  -- π/2 - (pio2_1 + pio2_2)
  let pio2_3 := Float.ofBits 0x3BA3198A2E000000   -- third 33 bits of π/2
  let pio2_3t := Float.ofBits 0x397B839A252049C1  -- π/2 - (pio2_1 + pio2_2 + pio2_3)
  -- fdlibm's `rnint`: adding and subtracting 1.5 · 2 ^ 52 rounds to the nearest integer.
  let fn := x * invpio2 + 6755399441055744.0 - 6755399441055744.0
  let n := fn.toUInt64
  let j := ix >>> 20
  let r := x - fn * pio2_1
  let w := fn * pio2_1t
  let y0 := r - w
  if ((y0.toBits >>> 52) &&& 0x7ff) + 16 < j then
    let t := r
    let w := fn * pio2_2
    let r := t - w
    let w := fn * pio2_2t - ((t - r) - w)
    let y0 := r - w
    if ((y0.toBits >>> 52) &&& 0x7ff) + 49 < j then
      let t := r
      let w := fn * pio2_3
      let r := t - w
      let w := fn * pio2_3t - ((t - r) - w)
      let y0 := r - w
      (n, y0, (r - y0) - w)
    else (n, y0, (r - y0) - w)
  else (n, y0, (r - y0) - w)

/-- fdlibm's `__ieee754_rem_pio2` for `π/4 < x`: the count `n` of `π/2` and `x - n · π/2` as
`y0 + y1` in `[-π/4, π/4]`.  Up to `9π/4` the count is fixed by the high word, except near
`π/2`, `π`, `3π/2`, and `2π`, where the subtraction cancels and the medium case runs.  An argument
of `2 ^ 20 · π/2` or more gives NaN. -/
def remPio2 (x : Float) : UInt64 × Float × Float :=
  let ix := x.toBits >>> 32
  if ix ≤ 0x400f6a7a then
    if ix &&& 0xfffff == 0x921fb then remMedium x ix
    else if ix ≤ 0x4002d97c then (1, remSmall x 1.0)
    else (2, remSmall x 2.0)
  else if ix ≤ 0x401c463b then
    if ix ≤ 0x4015fdbc then
      if ix == 0x4012d97c then remMedium x ix else (3, remSmall x 3.0)
    else if ix == 0x401921fb then remMedium x ix else (4, remSmall x 4.0)
  else if ix < 0x413921fb then remMedium x ix
  else (0, Float.ofBits 0x7FF8000000000000, Float.ofBits 0x7FF8000000000000)

/-- `sin x`, as fdlibm's `sin`: the kernel on `[-π/4, π/4]`, `x` itself below `2 ^ -26`, NaN for
an infinity or NaN, and otherwise the kernel of the quadrant of the reduced `|x|`, negated for a
negative `x`. -/
def sin (x : Float) : Float :=
  let ix := (x.toBits >>> 32) &&& 0x7fffffff
  if ix ≤ 0x3fe921fb then
    if ix < 0x3e500000 then x else kernelSin x 0.0 false
  else if 0x7ff00000 ≤ ix then x - x
  else
    let (n, y0, y1) := remPio2 x.abs
    let q := n &&& 3
    let s := if q == 0 then kernelSin y0 y1 true
      else if q == 1 then kernelCos y0 y1
      else if q == 2 then -kernelSin y0 y1 true
      else -kernelCos y0 y1
    if x < 0.0 then -s else s

/-- `cos x`, as fdlibm's `cos`: the kernel on `[-π/4, π/4]`, 1 below `2 ^ -27 · √2`, NaN for an
infinity or NaN, and otherwise the kernel of the quadrant of the reduced `|x|`. -/
def cos (x : Float) : Float :=
  let ix := (x.toBits >>> 32) &&& 0x7fffffff
  if ix ≤ 0x3fe921fb then
    if ix < 0x3e46a09e then 1.0 else kernelCos x 0.0
  else if 0x7ff00000 ≤ ix then x - x
  else
    let (n, y0, y1) := remPio2 x.abs
    let q := n &&& 3
    if q == 0 then kernelCos y0 y1
    else if q == 1 then -kernelSin y0 y1 true
    else if q == 2 then -kernelCos y0 y1
    else kernelSin y0 y1 true

verified_compile compiled := [kernelSin, kernelCos, remSmall, remMedium, remPio2, sin, cos]

end Verified.Examples.Trig

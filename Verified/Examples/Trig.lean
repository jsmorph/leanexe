import Verified.Reflect.Command

/-! The twenty-third program of the verified compiler: `sin` and `cos`, ported from fdlibm as
FreeBSD's `lib/msun/src` has it (`k_sin.c`, `k_cos.c`, `s_sin.c`, `s_cos.c`, and
`e_rem_pio2.c`, Copyright (C) 1993 by Sun Microsystems, Inc., freely distributable with this
notice).  An argument above `π/4` in magnitude is reduced by multiples of `π/2` to `y0 + y1` in
`[-π/4, π/4]`, and the kernels evaluate fdlibm's minimax polynomials there.  fdlibm states an error
below one unit in the last place.  Each constant is written as the bit pattern that fdlibm's source
gives beside its decimal value.  Lean's `Float.sin` is `@[extern "sin"]`, the C library's function,
with no definition in Lean, so the compiler's theorem is about these definitions.

The reduction is fdlibm's special cases up to `9π/4` and its three-step Cody–Waite reduction
below `2 ^ 20 · π/2`, and above that a Payne–Hanek reduction in word arithmetic, which reads the
bits of `2/π` and `π/2` from constant tables, so that no call allocates.  The module holds the
tables in data segments: `sinWith` and `cosWith` take them as borrowed array parameters, and `sin`
and `cos` pass them, as exported entries whose theorem assumes the tables at their addresses.  The
reduction takes `|x|`, by
`sin (-x) = -sin x` and `cos (-x) = cos x`, so its quadrant count is a word, where fdlibm reduces
`x` itself with a signed count.  `TrigAccuracy.lean` checks, in native Lean, the words of `2/π` and
`π/2` and the results against a reference computed with Lean's integers. -/

namespace Verified.Examples.Trig

/-- fdlibm's `__kernel_sin`: `sin (x + y)` for `|x| ≤ π/4` with the tail `y`, which `tail` says
is not zero.  The odd polynomial of degree 13 approximates `sin x`: its quotient by `x`, of degree
12, is within `2 ^ -58` of `sin x / x`. -/
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

/-- `π/2 · 2 ^ 127`, truncated to 128 bits: the high word and the low word.  The module holds the
table in a data segment, and `TrigAccuracy.lean` compares it with `π` computed from Machin's
formula. -/
def halfPi : Array UInt64 := #[0xC90FDAA22168C234, 0xC4C6628B80DC1CD1]

/-- The binary digits of `2/π` in words, `2/π = Σ k, invPi[k] · 2 ^ (-64 k)`: word 0 is the
integer part, 0, and words 1 to 19, 1216 bits, are fdlibm's table `ipio2` (`k_rem_pio2.c`)
regrouped from 24-bit chunks.  The module holds the table in a data segment, and
`TrigAccuracy.lean` compares it with `2/π` computed from Machin's formula. -/
def invPi : Array UInt64 :=
  #[0, 0xA2F9836E4E441529, 0xFC2757D1F534DDC0, 0xDB6295993C439041, 0xFE5163ABDEBBC561,
    0xB7246E3A424DD2E0, 0x06492EEA09D1921C, 0xFE1DEB1CB129A73E, 0xE88235F52EBB4484,
    0xE99C7026B45F7E41, 0x3991D639835339F4, 0x9C845F8BBDF9283B, 0x1FF897FFDE05980F,
    0xEF2F118B5A0A6D1F, 0x6D367ECF27CB09B7, 0x4F463F669E5FEA2D, 0x7527BAC7EBE5F17B,
    0x3D0739F78A5292EA, 0x6BFB5FB11F8D5D08, 0x56033046FC7B6BAB]

/-- The 128-bit product of two words, as its high and low words, from the products of their
32-bit halves. -/
def mul64 (a b : UInt64) : UInt64 × UInt64 :=
  let a1 := a >>> 32
  let a0 := a &&& 0xFFFFFFFF
  let b1 := b >>> 32
  let b0 := b &&& 0xFFFFFFFF
  let p00 := a0 * b0
  let p01 := a0 * b1
  let p10 := a1 * b0
  let mid := (p00 >>> 32) + (p01 &&& 0xFFFFFFFF) + (p10 &&& 0xFFFFFFFF)
  (a1 * b1 + (p01 >>> 32) + (p10 >>> 32) + (mid >>> 32), a * b)

/-- The number of leading zero bits of a word, 64 for 0, by halving the range. -/
def clz64 (x : UInt64) : UInt64 :=
  if x == 0 then 64
  else
    let (n1, x1) := if x >>> 32 == 0 then ((32 : UInt64), x <<< 32) else (0, x)
    let (n2, x2) := if x1 >>> 48 == 0 then (n1 + 16, x1 <<< 16) else (n1, x1)
    let (n3, x3) := if x2 >>> 56 == 0 then (n2 + 8, x2 <<< 8) else (n2, x2)
    let (n4, x4) := if x3 >>> 60 == 0 then (n3 + 4, x3 <<< 4) else (n3, x3)
    let (n5, x5) := if x4 >>> 62 == 0 then (n4 + 2, x4 <<< 2) else (n4, x4)
    if x5 >>> 63 == 0 then n5 + 1 else n5

/-- The 64 bits of `2/π` that start `s` bits into word `d` of `inv`, `s < 64`. -/
def window (inv : Array UInt64) (d s : UInt64) : UInt64 :=
  if s == 0 then inv[d.toNat]!
  else (inv[d.toNat]! <<< s) ||| (inv[(d + 1).toNat]! >>> (64 - s))

/-- The top 128 bits of the product of the 128-bit numbers `a1 : a0` and `b1 : b0`. -/
def mulTop (a1 a0 b1 b0 : UInt64) : UInt64 × UInt64 :=
  let (p11h, p11l) := mul64 a1 b1
  let (p10h, p10l) := mul64 a1 b0
  let (p01h, p01l) := mul64 a0 b1
  let (p00h, _) := mul64 a0 b0
  let s1 := p00h + p10l
  let k1 := if s1 < p00h then (1 : UInt64) else 0
  let w1 := s1 + p01l
  let k2 := if w1 < s1 then (1 : UInt64) else 0
  let s2 := p11l + p10h
  let k3 := if s2 < p11l then (1 : UInt64) else 0
  let s3 := s2 + p01h
  let k4 := if s3 < s2 then (1 : UInt64) else 0
  let w2 := s3 + (k1 + k2)
  let k5 := if w2 < s3 then (1 : UInt64) else 0
  (p11h + k3 + k4 + k5, w2)

/-- The top 128 bits of the 192-bit `a2 : a1 : a0` shifted left by `lz < 192`. -/
def shiftTop (a2 a1 a0 lz : UInt64) : UInt64 × UInt64 :=
  let (x2, x1, x0) := if 128 ≤ lz then (a0, (0 : UInt64), (0 : UInt64))
    else if 64 ≤ lz then (a1, a0, 0) else (a2, a1, a0)
  let s := lz &&& 63
  if s == 0 then (x2, x1)
  else ((x2 <<< s) ||| (x1 >>> (64 - s)), (x1 <<< s) ||| (x0 >>> (64 - s)))

/-- Payne–Hanek reduction, for `2 ^ 20 · π/2 ≤ x` finite, in word arithmetic as Go's
`math.trigReduce` does it after K. C. Ng, "Argument Reduction for Huge Arguments: Good to the Last
Bit", 1992: the count `n` of `π/2` and `x - n · π/2` as `y0 + y1`.  With `x = m · 2 ^ e`, the bits
of `2/π` before bit `e - 1` contribute multiples of 4 to `x · 2/π`, so the low 192 bits of
`m · z`, for the 192-bit window `z` of `2/π` from bit `e - 1` on, are `x · 2/π` modulo 4 with 190
bits of fraction, exact to `2 ^ -137` since the window omits less than `2 ^ -190` per unit of
`m < 2 ^ 53`.  The fraction is rounded to the nearer quadrant and shifted to its leading bit.
That bit is the `2 ^ -62` bit or a higher one, and the double closest to a multiple of `π/2` gives
the lowest.  The shifted fraction is multiplied by `π/2` as a 128-bit number, and the top 106 bits
of the product become `y0 + y1` by an exact two-sum. -/
def remLarge (inv half : Array UInt64) (x : Float) : UInt64 × Float × Float :=
  let b := x.toBits
  let m := (b &&& 0xFFFFFFFFFFFFF) ||| 0x10000000000000
  -- The window starts at bit `e - 1`, `e = exponent - 1075`, which is bit `e + 62` from the
  -- start of word 0.
  let g := ((b >>> 52) &&& 0x7FF) - 1013
  let d := g >>> 6
  let s := g &&& 63
  let (h2, l2) := mul64 (window inv (d + 2) s) m
  let (h1, l1) := mul64 (window inv (d + 1) s) m
  let w1 := h2 + l1
  let w2 := h1 + window inv d s * m + (if w1 < h2 then 1 else 0)
  let q := w2 >>> 62
  let f2 := w2 &&& 0x3FFFFFFFFFFFFFFF
  -- A fraction of one half or more rounds up to the next quadrant: its magnitude is the
  -- 190-bit negation.
  let up := f2 >>> 61 == 1
  let (a2, a1, a0) := if up then
      ((0 - f2 - (if w1 != 0 || l2 != 0 then 1 else 0)) &&& 0x3FFFFFFFFFFFFFFF,
        0 - w1 - (if l2 != 0 then 1 else 0), 0 - l2)
    else (f2, w1, l2)
  let lz := if a2 != 0 then clz64 a2 else if a1 != 0 then 64 + clz64 a1 else 128 + clz64 a0
  let (t1, t0) := shiftTop a2 a1 a0 lz
  let (u1, u0) := mulTop t1 t0 half[(0 : UInt64).toNat]! half[(1 : UInt64).toNat]!
  -- The remainder is `(u1 : u0) · 2 ^ (-125 - lz)`, with its leading bit at `p = 64 + k`.
  let k := if u1 >>> 63 == 1 then (63 : UInt64) else 62
  let hi := u1 >>> (k - 52)
  let lo := ((u1 <<< (105 - k)) ||| (u0 >>> (k - 41))) &&& 0x1FFFFFFFFFFFFF
  let a := hi.toFloat * Float.ofBits ((k + 910 - lz) <<< 52)
  let c := lo.toFloat * Float.ofBits ((k + 857 - lz) <<< 52)
  let y0 := a + c
  let y1 := c - (y0 - a)
  if up then (q + 1, -y0, -y1) else (q, y0, y1)

/-- fdlibm's `__ieee754_rem_pio2` for `π/4 < x`: the count `n` of `π/2` and `x - n · π/2` as
`y0 + y1` in `[-π/4, π/4]`.  Up to `9π/4` the count is fixed by the high word, except near
`π/2`, `π`, `3π/2`, and `2π`, where the subtraction cancels and the medium case runs, and from
`2 ^ 20 · π/2` on the Payne–Hanek reduction runs. -/
def remPio2 (inv half : Array UInt64) (x : Float) : UInt64 × Float × Float :=
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
  else remLarge inv half x

/-- `sin x`, as fdlibm's `sin`: the kernel on `[-π/4, π/4]`, `x` itself below `2 ^ -26`, NaN for
an infinity or NaN, and otherwise the kernel of the quadrant of the reduced `|x|`, negated for a
negative `x`, with the tables `inv` and `half` of `2/π` and `π/2`. -/
def sinWith (inv half : Array UInt64) (x : Float) : Float :=
  let ix := (x.toBits >>> 32) &&& 0x7fffffff
  if ix ≤ 0x3fe921fb then
    if ix < 0x3e500000 then x else kernelSin x 0.0 false
  else if 0x7ff00000 ≤ ix then x - x
  else
    let (n, y0, y1) := remPio2 inv half x.abs
    let q := n &&& 3
    let s := if q == 0 then kernelSin y0 y1 true
      else if q == 1 then kernelCos y0 y1
      else if q == 2 then -kernelSin y0 y1 true
      else -kernelCos y0 y1
    if x < 0.0 then -s else s

/-- `cos x`, as fdlibm's `cos`: the kernel on `[-π/4, π/4]`, 1 below `2 ^ -27 · √2`, NaN for an
infinity or NaN, and otherwise the kernel of the quadrant of the reduced `|x|`, with the tables
`inv` and `half` of `2/π` and `π/2`. -/
def cosWith (inv half : Array UInt64) (x : Float) : Float :=
  let ix := (x.toBits >>> 32) &&& 0x7fffffff
  if ix ≤ 0x3fe921fb then
    if ix < 0x3e46a09e then 1.0 else kernelCos x 0.0
  else if 0x7ff00000 ≤ ix then x - x
  else
    let (n, y0, y1) := remPio2 inv half x.abs
    let q := n &&& 3
    if q == 0 then kernelCos y0 y1
    else if q == 1 then -kernelSin y0 y1 true
    else if q == 2 then -kernelCos y0 y1
    else kernelSin y0 y1 true

/-- `sin x`, from the tables `invPi` and `halfPi`. -/
def sin (x : Float) : Float := sinWith invPi halfPi x

/-- `cos x`, from the tables `invPi` and `halfPi`. -/
def cos (x : Float) : Float := cosWith invPi halfPi x

verified_compile compiled := [kernelSin, kernelCos, remSmall, remMedium, mul64, clz64, window,
  mulTop, shiftTop, remLarge, remPio2, sinWith, cosWith, sin, cos]

end Verified.Examples.Trig

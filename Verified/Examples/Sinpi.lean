import Verified.Examples.Tan

/-! The forty-fourth program of the verified compiler: `sinpi`, `cospi`, and `tanpi`, the sine,
cosine, and tangent of `π x`, ported from FreeBSD's `lib/msun/src` at commit
`20381bce4b63975494a2f4bc84257f6932e6d379` (`s_sinpi.c`, `s_cospi.c`, `s_tanpi.c`, `k_sinpi.h`, and
`k_cospi.h`, Copyright (c) 2017, 2023 Steven G. Kargl, BSD-2-Clause).  Below `2 ^ -29` in magnitude
`sinpi` and `tanpi` give `π x` from `x` split at its high 32 bits and scaled by `2 ^ 53`, and
`cospi` gives 1.  Below 1, the functions reflect `|x|` into `[0, 1/4]` and call kernels that form
`π r` as `hi + lo`, from `r` split at single precision and `π` in two parts, and pass it to
fdlibm's kernels: `Trig.kernelSin`, `Trig.kernelCos`, and `Tan.kernelTan`, which the module lists,
so that the reflector compiles those Lean definitions into this module.  From 1 to `2 ^ 52`, the
functions subtract the integer part of `|x|` and change the sign for an odd one, and from `2 ^ 52`
on the arguments are integers, which give `±0`, `±1`, or `±0` by parity.  Kargl states no error
bound.  The constants `pi_hi` and `pi_lo` are written as the bit patterns that the sources give
beside their decimal values.  The dialect has no single precision: `toSingle` rounds the 52-bit
fraction of `x` to 23 bits, ties to even, which is `(float) x` for zero and for every `x` whose
single-precision value is normal, among them every argument of the kernels, from `2 ^ -54` to
`1/2`.  The integer part of `|x|` is fdlibm's `FFLOOR`, and its parity comes from `toUInt64`, as
`(uint64_t) x & 1` in `s_tanpi.c`.  `s_sinpi.c` and `s_cospi.c` convert to `uint32_t` after
subtracting `2 ^ 30` from integers above `2 ^ 31`, a conversion that C leaves undefined above
`2 ^ 32`, and the parity of the integer is what they intend.  The dialect has no floating-point
flags: `vzero/vzero` is `0/0`, and `(int) ax == 0` is `ax.toUInt64 == 0`, true where it is
evaluated.  fdlibm's high words are words, and the sign of `x` is its top bit.
`SinpiAccuracy.lean` checks the results against references computed with Lean's integers. -/

namespace Verified.Examples.Sinpi

/-- `(float) x` back in double precision, for `x` zero or with a normal single-precision value:
the low 29 bits of the fraction rounded away, ties to even, with any carry into the exponent. -/
def toSingle (x : Float) : Float :=
  let b := x.toBits
  let low := b &&& 0x1FFFFFFF
  let base := b - low
  if low > 0x10000000 || (low == 0x10000000 && base &&& 0x20000000 != 0) then
    Float.ofBits (base + 0x20000000)
  else Float.ofBits base

/-- The start of `k_sinpi.h`, `k_cospi.h`, and `s_tanpi.c`'s `__kernel_tanpi`: `π x` as `hi + lo`
from `hi = (float) x`, `lo = x - hi`, `π` as `pi_hi + pi_lo`, and `_2sumF`. -/
def piProduct (x : Float) : Float × Float :=
  let pi_hi := Float.ofBits 0x400921FB58000000  --  3.1415926814079285e+00
  let pi_lo := Float.ofBits 0xBE5DDE973DCB3B3A  -- -2.7818135228334233e-08
  let hi := toSingle x
  let lo := x - hi
  let lo := lo * (pi_lo + pi_hi) + hi * pi_lo
  let hi := hi * pi_hi
  let w := hi + lo
  (w, (hi - w) + lo)

/-- `k_sinpi.h`'s `__kernel_sinpi`: `sin (π x)` for `x` in `[0, 1/4]`. -/
def kernelSinpi (x : Float) : Float :=
  let (hi, lo) := piProduct x
  Trig.kernelSin hi lo true

/-- `k_cospi.h`'s `__kernel_cospi`: `cos (π x)` for `x` in `[0, 1/4]`. -/
def kernelCospi (x : Float) : Float :=
  let (hi, lo) := piProduct x
  Trig.kernelCos hi lo

/-- `s_tanpi.c`'s `__kernel_tanpi`: `tan (π x)` for `x` in `[0, 1/2)`, from `tan` below `1/4` and
`1/tan (π (1/2 - x))` above, and 1 at `1/4`. -/
def kernelTanpi (x : Float) : Float :=
  if x < 0.25 then
    let (hi, lo) := piProduct x
    Tan.kernelTan hi lo false
  else if x > 0.25 then
    let (hi, lo) := piProduct (0.5 - x); -Tan.kernelTan hi lo true
  else 1.0

/-- `π x` for `0 < |x| < 2 ^ -29` with high word `hx`, as `s_sinpi.c` and `s_tanpi.c` compute it:
`x` scaled by `2 ^ 53` and split at its high 32 bits, so that subnormal inputs lose no bits. -/
def piTiny (x : Float) (hx : UInt64) : Float :=
  let pi_hi := Float.ofBits 0x400921FB58000000  --  3.1415926814079285e+00
  let pi_lo := Float.ofBits 0xBE5DDE973DCB3B3A  -- -2.7818135228334233e-08
  let hi := Float.ofBits (hx <<< 32) * Float.ofBits 0x4340000000000000  -- 0x1p53
  let lo := x * Float.ofBits 0x4340000000000000 - hi
  let s := (pi_lo + pi_hi) * lo + pi_lo * hi + pi_hi * hi
  s * Float.ofBits 0x3CA0000000000000  -- 0x1p-53

/-- `math_private.h`'s `FFLOOR` for `1 ≤ |x| < 2 ^ 52` with the words `ix` and `lx` of `|x|`: the
integer part of `|x|` and `j0`, its unbiased exponent. -/
def ffloor (ix lx : UInt64) : Float × UInt64 :=
  let j0 := ((ix >>> 20) &&& 0x7ff) - 0x3ff
  if j0 < 20 then
    (Float.ofBits ((ix &&& ((0xFFFFFFFF : UInt64) ^^^ ((0x000fffff : UInt64) >>> j0))) <<< 32), j0)
  else
    (Float.ofBits ((ix <<< 32) |||
      (lx &&& ((0xFFFFFFFF : UInt64) ^^^ ((0xffffffff : UInt64) >>> (j0 - 20))))), j0)

/-- Whether the integer `fl` below `2 ^ 52`, the integer part from `ffloor` with exponent `j0`, is
odd, as `s_sinpi.c` and `s_cospi.c` test it after subtracting `2 ^ 30` above `2 ^ 30`. -/
def oddPart (fl : Float) (j0 : UInt64) : Bool :=
  let fl := if j0 > 30 then fl - 1073741824.0 else fl
  fl.toUInt64 &&& 1 == 1

/-- `s_sinpi.c`'s `sinpi`.  `hx` and `lx` are the words of `x`, `ix` the high word of `|x|`, and
`ax` is `|x|`.  An integer gives `±0` with the sign of `x`, and an infinity or NaN gives NaN. -/
def sinpi (x : Float) : Float :=
  let hx := x.toBits >>> 32
  let lx := x.toBits &&& 0xFFFFFFFF
  let ix := hx &&& 0x7fffffff
  let ax := Float.ofBits ((ix <<< 32) ||| lx)
  let neg := hx &&& 0x80000000 != 0
  if ix < 0x3ff00000 then
    if ix < 0x3e200000 then
      if x == 0.0 then x else piTiny x hx
    else
      let s := if ix < 0x3fd00000 then kernelSinpi ax
        else if ix < 0x3fe00000 then kernelCospi (0.5 - ax)
        else if ix < 0x3fe80000 then kernelCospi (ax - 0.5)
        else kernelSinpi (1.0 - ax)
      if neg then -s else s
  else if ix < 0x43300000 then
    let (fl, j0) := ffloor ix lx
    let ax := ax - fl
    let ix := ax.toBits >>> 32
    let s :=
      if ix == 0 then 0.0
      else
        let s := if ix < 0x3fd00000 then kernelSinpi ax
          else if ix < 0x3fe00000 then kernelCospi (0.5 - ax)
          else if ix < 0x3fe80000 then kernelCospi (ax - 0.5)
          else kernelSinpi (1.0 - ax)
        if oddPart fl j0 then -s else s
    if neg then -s else s
  else if ix ≥ 0x7ff00000 then 0.0 / 0.0
  else if neg then -0.0 else 0.0

/-- `s_cospi.c`'s `cospi`.  `ix` and `lx` are the words of `ax = |x|`.  An integer plus `1/2` gives
`+0`, and an infinity or NaN gives NaN.  From `2 ^ 52` on the parity of the integer gives `±1`. -/
def cospi (x : Float) : Float :=
  let hx := x.toBits >>> 32
  let lx := x.toBits &&& 0xFFFFFFFF
  let ix := hx &&& 0x7fffffff
  let ax := Float.ofBits ((ix <<< 32) ||| lx)
  if ix < 0x3ff00000 then
    if ix < 0x3fd00000 then
      if ix < 0x3e200000 && ax.toUInt64 == 0 then 1.0 else kernelCospi ax
    else if ix < 0x3fe00000 then kernelSinpi (0.5 - ax)
    else if ix < 0x3fe80000 then
      if ax == 0.5 then 0.0 else -kernelSinpi (ax - 0.5)
    else -kernelCospi (1.0 - ax)
  else if ix < 0x43300000 then
    let (fl, j0) := ffloor ix lx
    let ax := ax - fl
    let ix := ax.toBits >>> 32
    if ix ≥ 0x3fe00000 && ix < 0x3fe80000 && ax == 0.5 then 0.0
    else
      let c := if ix < 0x3fd00000 then (if ix == 0 then 1.0 else kernelCospi ax)
        else if ix < 0x3fe00000 then kernelSinpi (0.5 - ax)
        else if ix < 0x3fe80000 then -kernelSinpi (ax - 0.5)
        else -kernelCospi (1.0 - ax)
      if oddPart fl j0 then -c else c
  else if ix ≥ 0x7ff00000 then 0.0 / 0.0
  else if ix < 0x43400000 then if lx &&& 1 != 0 then -1.0 else 1.0
  else 1.0

/-- `s_tanpi.c`'s `tanpi`.  An integer gives `±0`, with the sign of `x` for an even integer and the
other sign for an odd one, an integer plus `1/2` gives `±∞` by the same rule, and an infinity or
NaN gives NaN. -/
def tanpi (x : Float) : Float :=
  let hx := x.toBits >>> 32
  let lx := x.toBits &&& 0xFFFFFFFF
  let ix := hx &&& 0x7fffffff
  let ax := Float.ofBits ((ix <<< 32) ||| lx)
  let neg := hx &&& 0x80000000 != 0
  if ix < 0x3ff00000 then
    if ix < 0x3e200000 then
      if x == 0.0 then x else piTiny x hx
    else
      let t := if ix < 0x3fe00000 then kernelTanpi ax
        else if ax == 0.5 then 1.0 / 0.0
        else -kernelTanpi (1.0 - ax)
      if neg then -t else t
  else if ix < 0x43300000 then
    let fl := (ffloor ix lx).1
    let odd := if fl.toUInt64 &&& 1 == 1 then -1.0 else 1.0
    let ax := ax - fl
    let ix := ax.toBits >>> 32
    let t := if ix < 0x3fe00000 then
        if ix == 0 then (if odd < 0.0 then -0.0 else 0.0) else kernelTanpi ax
      else if ax == 0.5 then odd / 0.0
      else -kernelTanpi (1.0 - ax)
    if neg then -t else t
  else if ix ≥ 0x7ff00000 then 0.0 / 0.0
  else
    let t := if ix ≥ 0x43400000 then 0.0 else if lx &&& 1 != 0 then -0.0 else 0.0
    if neg then -t else t

verified_compile compiled := [Trig.kernelSin, Trig.kernelCos, Tan.kernelTan, toSingle, piProduct,
  kernelSinpi, kernelCospi, kernelTanpi, piTiny, ffloor, oddPart, sinpi, cospi, tanpi]

end Verified.Examples.Sinpi

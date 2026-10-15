import Verified.Examples.Trig

/-! The thirty-fifth program of the verified compiler: `tan`, ported from fdlibm as FreeBSD's
`lib/msun/src` has it at commit `20381bce4b63975494a2f4bc84257f6932e6d379` (`s_tan.c`, Copyright
(C) 1993, and `k_tan.c`, Copyright 2004, by Sun Microsystems, Inc., freely distributable with this
notice).  The argument reduction is the one of `Trig.lean`: the module lists `Trig.remPio2` and
the functions it calls, so that the reflector compiles those Lean definitions again into this
module, and `tan` passes the tables `Trig.invPi` and `Trig.halfPi`.  The kernel evaluates
`tan (y0 + y1)` as an odd polynomial of degree 27 in `y0` plus the first-order term `(1 + y0²) y1`.
fdlibm bounds the polynomial's quotient by `y0` within `2 ^ -59.2` of `tan y0 / y0` on
`[0, 0.67434]`.  From
`0.6744` on in magnitude it evaluates the polynomial at `π/4 - |y0 + y1|` and uses
`tan (π/4 - y) = (1 - tan y)/(1 + tan y)`.  An odd quadrant count gives `-1/tan`, computed with
the high 32 bits of the quotient and its correction.  fdlibm states that the result is nearly
rounded.  Each constant is written as the bit pattern that fdlibm's source gives beside its
decimal value.  The dialect has no floating-point flags, and the expressions that fdlibm evaluates
only for their flags keep their values: the guard `(int) x == 0` is `x.toUInt64 == 0`, true for
every `x` below `2 ^ -27` in magnitude that it guards, since both truncations give 0.  fdlibm's
kernel flag `iy = ±1` is the Boolean `odd`, its signed high word is a word, and
`(double)(1 - ((hx >> 30) & 2))` is the sign of `x` as `±1`.  The reduction takes `|x|`, as in
`Trig.sinWith`, and the result is negated for a negative `x`.  fdlibm reduces `x` itself, and its
reduction and kernel are odd in every rounding, so the negation gives fdlibm's result for the same
reduction.  From `2 ^ 20 · π/2` on, `Trig.remPio2` is the Payne–Hanek reduction of `Trig.lean` in
place of fdlibm's `__kernel_rem_pio2`.  `TanAccuracy.lean` checks the results against a reference
computed with Lean's integers.

The notices of the ported files follow verbatim, as their licenses require.

`s_tan.c`:

    ====================================================
    Copyright (C) 1993 by Sun Microsystems, Inc. All rights reserved.

    Developed at SunPro, a Sun Microsystems, Inc. business.
    Permission to use, copy, modify, and distribute this
    software is freely granted, provided that this notice
    is preserved.
    ====================================================

`k_tan.c`:

    ====================================================
    Copyright 2004 Sun Microsystems, Inc.  All Rights Reserved.

    Permission to use, copy, modify, and distribute this
    software is freely granted, provided that this notice
    is preserved.
    ====================================================
-/

namespace Verified.Examples.Tan

/-- fdlibm's `__kernel_tan`: `tan (x + y)` for `|x| ≤ π/4` with the tail `y`, or `-1/tan (x + y)`
when `odd`.  `ix` is the high word of `|x|`. -/
def kernelTan (x y : Float) (odd : Bool) : Float :=
  let T0 := Float.ofBits 0x3FD5555555555563   --  3.33333333333334091986e-01
  let T1 := Float.ofBits 0x3FC111111110FE7A   --  1.33333333333201242699e-01
  let T2 := Float.ofBits 0x3FABA1BA1BB341FE   --  5.39682539762260521377e-02
  let T3 := Float.ofBits 0x3F9664F48406D637   --  2.18694882948595424599e-02
  let T4 := Float.ofBits 0x3F8226E3E96E8493   --  8.86323982359930005737e-03
  let T5 := Float.ofBits 0x3F6D6D22C9560328   --  3.59207910759131235356e-03
  let T6 := Float.ofBits 0x3F57DBC8FEE08315   --  1.45620945432529025516e-03
  let T7 := Float.ofBits 0x3F4344D8F2F26501   --  5.88041240820264096874e-04
  let T8 := Float.ofBits 0x3F3026F71A8D1068   --  2.46463134818469906812e-04
  let T9 := Float.ofBits 0x3F147E88A03792A6   --  7.81794442939557092300e-05
  let T10 := Float.ofBits 0x3F12B80F32F0A7E9  --  7.14072491382608190305e-05
  let T11 := Float.ofBits 0xBEF375CBDB605373  -- -1.85586374855275456654e-05
  let T12 := Float.ofBits 0x3EFB2A7074BF7AD4  --  2.59073051863633712884e-05
  let pio4 := Float.ofBits 0x3FE921FB54442D18    --  7.85398163397448278999e-01
  let pio4lo := Float.ofBits 0x3C81A62633145C07  --  3.06161699786838301793e-17
  let hx := x.toBits >>> 32
  let ix := hx &&& 0x7fffffff
  let big : Bool := ix ≥ 0x3FE59428
  let (x, y) :=
    if big then
      let (x, y) := if hx >>> 31 == 1 then (-x, -y) else (x, y)
      (pio4 - x + (pio4lo - y), 0.0)
    else (x, y)
  let z := x * x
  let w := z * z
  let r := T1 + w * (T3 + w * (T5 + w * (T7 + w * (T9 + w * T11))))
  let v := z * (T2 + w * (T4 + w * (T6 + w * (T8 + w * (T10 + w * T12)))))
  let s := z * x
  let r := y + z * (s * (r + v) + y)
  let r := r + T0 * s
  let w := x + r
  if big then
    let v := if odd then -1.0 else 1.0
    let sign := if hx >>> 31 == 1 then -1.0 else 1.0
    sign * (v - 2.0 * (x - (w * w / (w + v) - r)))
  else if !odd then w
  else
    let z := Float.ofBits (w.toBits &&& 0xFFFFFFFF00000000)
    let v := r - (z - x)
    let a := -1.0 / w
    let t := Float.ofBits (a.toBits &&& 0xFFFFFFFF00000000)
    let s := 1.0 + t * z
    t + a * (s + t * v)

/-- `tan x`, as fdlibm's `tan`: the kernel on `[-π/4, π/4]`, `x` itself below `2 ^ -27`, NaN for
an infinity or NaN, and otherwise the kernel of the reduced `|x|`, with `odd` for an odd quadrant
count, negated for a negative `x`, with the tables `inv` and `half` of `2/π` and `π/2`. -/
def tanWith (inv half : Array UInt64) (x : Float) : Float :=
  let ix := (x.toBits >>> 32) &&& 0x7fffffff
  if ix ≤ 0x3fe921fb then
    if ix < 0x3e400000 && x.toUInt64 == 0 then x else kernelTan x 0.0 false
  else if 0x7ff00000 ≤ ix then x - x
  else
    let (n, y0, y1) := Trig.remPio2 inv half x.abs
    let t := kernelTan y0 y1 (n &&& 1 == 1)
    if x < 0.0 then -t else t

/-- `tan x`, from the tables `Trig.invPi` and `Trig.halfPi`. -/
def tan (x : Float) : Float := tanWith Trig.invPi Trig.halfPi x

verified_compile compiled := [Trig.remSmall, Trig.remMedium, Trig.mul64, Trig.clz64, Trig.window,
  Trig.mulTop, Trig.shiftTop, Trig.remLarge, Trig.remPio2, kernelTan, tanWith, tan]

end Verified.Examples.Tan

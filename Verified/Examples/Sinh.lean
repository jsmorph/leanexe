import Verified.Examples.Exp
import Verified.Examples.Tanh

/-! The thirty-sixth program of the verified compiler: `sinh` and `cosh`, ported from fdlibm as
FreeBSD's `lib/msun/src` has it at commit `20381bce4b63975494a2f4bc84257f6932e6d379` (`e_sinh.c`
and `e_cosh.c`, Copyright (C) 1993 by Sun Microsystems, Inc., freely distributable with this
notice), with the helpers `__frexp_exp` and `__ldexp_exp` from `k_exp.c` (Copyright (c) 2011 David
Schultz, SPDX-License-Identifier: BSD-2-Clause).  Below 22 in magnitude, `sinh` is
`(E + E/(E + 1))/2` with `E = expm1 |x|`, written as `E - E²/(E + 1)` plus `E` below 1, and `cosh`
is `1 + E²/(2 (1 + E))` below `ln 2/2` and `(e + 1/e)/2` with `e = exp |x|` above.  From 22 to
fdlibm's bound near `ln (DBL_MAX)` both are `exp |x|/2`, and up to the overflow threshold they are
`exp (|x| - 1799 ln 2) · 2 ^ 1798`, which `__ldexp_exp` forms without an intermediate overflow.
fdlibm states no error bound for either function.  The functions call the Lean definitions of the
earlier ports, which the module lists, so that the reflector compiles them into this module:
`Tanh.expm1`, fdlibm's `expm1` as fdlibm calls it, and `Exp.expWith` with the table
`Exp.expTable`, Arm's `exp`, where fdlibm calls its own `e_exp.c`.  Both bound the error of their
`exp` below one unit in the last place, and their results may differ in the last bit.  `sinh` and
`cosh` pass `Exp.expTable` to `sinhWith` and `coshWith`.  Each constant is written as the bit
pattern of its value: `1.0e+307`, `1.0e+300`, and `k_exp.c`'s `kln2 = 1246.97177782734161156`, the
double nearest `1799 ln 2`.  The dialect has no floating-point flags, and the expressions that
fdlibm evaluates only for their flags keep their values: the guard `shuge + x > 1` stays.  The
signed exponents of `k_exp.c` are two's complement words, and its 32-bit high words are the top
halves of the 64-bit words.  `SinhAccuracy.lean` checks the results against a reference computed
with Lean's integers. -/

namespace Verified.Examples.Sinh

/-- `k_exp.c`'s `__frexp_exp`: `exp x` for `ln (DBL_MAX) ≤ x < 1454.91` as `y · 2 ^ expt` with
`2 ^ 1023 ≤ y < 2 ^ 1024`, from `exp (x - 1799 ln 2)` with its exponent field set to 2046.  The
exponent `expt` is a two's complement word. -/
def frexpExp (tab : Array UInt64) (x : Float) : Float × UInt64 :=
  let kln2 := Float.ofBits 0x40937BE319BA0DA4  -- 1246.97177782734161156
  let expX := Exp.expWith tab (x - kln2)
  let hx := expX.toBits >>> 32
  let expt := (hx >>> 20) - (0x3ff + 1023 : UInt64) + 1799
  (Float.ofBits ((((hx &&& (0xfffff : UInt64)) ||| ((0x3ff + 1023 : UInt64) <<< 20)) <<< 32) |||
    (expX.toBits &&& 0xFFFFFFFF)), expt)

/-- `k_exp.c`'s `__ldexp_exp`: `exp x · 2 ^ expt` for `x` from `ln (DBL_MAX)` to fdlibm's overflow
thresholds, with `expt` a two's complement word, `-1` from `sinh` and `cosh`. -/
def ldexpExp (tab : Array UInt64) (x : Float) (expt : UInt64) : Float :=
  let (expX, exExpt) := frexpExp tab x
  let expt := expt + exExpt
  expX * Float.ofBits ((((0x3ff + expt) <<< 20) &&& 0xFFFFFFFF) <<< 32)

/-- fdlibm's `sinh` with the table `tab` of `Exp.expWith`.  `jx` is the high word of `x` and `ix`
that of `|x|`.  An infinity or NaN gives `x + x`, and from the overflow threshold on the result is
`x · 1.0e+307`, which overflows. -/
def sinhWith (tab : Array UInt64) (x : Float) : Float :=
  let shuge := Float.ofBits 0x7FAC7B1F3CAC7433  -- 1.0e+307
  let jx := x.toBits >>> 32
  let ix := jx &&& 0x7fffffff
  if ix ≥ 0x7ff00000 then x + x
  else
    let h := if jx >>> 31 == 1 then -0.5 else 0.5
    if ix < 0x40360000 then
      if ix < 0x3e300000 && shuge + x > 1.0 then x
      else
        let t := Tanh.expm1 x.abs
        if ix < 0x3ff00000 then h * (2.0 * t - t * t / (t + 1.0)) else h * (t + t / (t + 1.0))
    else if ix < 0x40862E42 then h * Exp.expWith tab x.abs
    else if ix ≤ 0x408633CE then h * 2.0 * ldexpExp tab x.abs (0 - 1)
    else x * shuge

/-- fdlibm's `cosh` with the table `tab` of `Exp.expWith`.  `ix` is the high word of `|x|`.  An
infinity or NaN gives `x · x`, and from the overflow threshold on the result is
`1.0e+300 · 1.0e+300`, which overflows. -/
def coshWith (tab : Array UInt64) (x : Float) : Float :=
  let huge := Float.ofBits 0x7E37E43C8800759C  -- 1.0e+300
  let ix := (x.toBits >>> 32) &&& 0x7fffffff
  if ix ≥ 0x7ff00000 then x * x
  else if ix < 0x3fd62e43 then
    let t := Tanh.expm1 x.abs
    let w := 1.0 + t
    if ix < 0x3c800000 then w else 1.0 + (t * t) / (w + w)
  else if ix < 0x40360000 then
    let t := Exp.expWith tab x.abs
    0.5 * t + 0.5 / t
  else if ix < 0x40862E42 then 0.5 * Exp.expWith tab x.abs
  else if ix ≤ 0x408633CE then ldexpExp tab x.abs (0 - 1)
  else huge * huge

/-- `sinh x`, with the table `Exp.expTable`. -/
def sinh (x : Float) : Float := sinhWith Exp.expTable x

/-- `cosh x`, with the table `Exp.expTable`. -/
def cosh (x : Float) : Float := coshWith Exp.expTable x

verified_compile compiled := [Exp.specialCase, Exp.expCore, Exp.expWith, Tanh.expm1Kernel,
  Tanh.expm1, frexpExp, ldexpExp, sinhWith, coshWith, sinh, cosh]

end Verified.Examples.Sinh

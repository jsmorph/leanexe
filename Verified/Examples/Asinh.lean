import Verified.Examples.Log
import Verified.Examples.Log1p

/-! The thirty-seventh program of the verified compiler: `asinh`, `acosh`, and `atanh`, ported
from fdlibm as FreeBSD's `lib/msun/src` has it at commit `20381bce4b63975494a2f4bc84257f6932e6d379`
(`s_asinh.c`, `e_acosh.c`, and `e_atanh.c`, Copyright (C) 1993 by Sun Microsystems, Inc., freely
distributable with this notice).  `asinh` is `sign x · log (|x| + √(x² + 1))`, computed as `x`
below `2 ^ -28`, as `log1p (|x| + x²/(1 + √(1 + x²)))` below 2, as
`log (2 |x| + 1/(√(x² + 1) + |x|))` below `2 ^ 28`, and as `log |x| + ln 2` above.  `acosh` is
`log (x + √(x² - 1))`, computed as `log1p (t + √(2 t + t²))` with `t = x - 1` below 2, as
`log (2 x - 1/(x + √(x² - 1)))` below `2 ^ 28`, and as `log x + ln 2` above, with NaN below 1 and
0 at 1.  `atanh` is `log1p (2 |x| + 2 x²/(1 - |x|))/2` below `1/2` in magnitude and
`log1p (2 |x|/(1 - |x|))/2` from there to 1, with the sign of `x`, `±∞` at `±1`, and NaN beyond.
fdlibm states no error bound for any of them.  The functions call the Lean definitions of the
earlier ports, which the module lists, so that the reflector compiles them into this module:
`Log1p.log1p`, fdlibm's `log1p` as fdlibm calls it, and `Log.logWith` with the tables
`Log.logTable` and `Log.logTable2`, Arm's `log`, where fdlibm calls its own `e_log.c`.  fdlibm
bounds the error of its `log` below one unit in the last place and Arm that of its `log` by about
0.52 units, and their results may differ in the last bit.  `asinh` and `acosh` pass the tables to
`asinhWith` and `acoshWith`, and `atanh` needs none.  Each constant is written as the bit pattern
that fdlibm's source gives beside its decimal value, and `1.0e+300` as the bits of that decimal.
The dialect has no floating-point flags, and the expressions that fdlibm evaluates only for their
flags keep their values: the guards `huge + x > 1` and `huge + x > 0` stay, and `x/zero` is
`x/0`.  fdlibm's signed high word `hx` is a word, so a comparison of `hx` with a positive bound
also tests its sign bit.  `AsinhAccuracy.lean` checks the results against references computed
with Lean's integers. -/

namespace Verified.Examples.Asinh

/-- fdlibm's `asinh` with the tables `tab` and `tab2` of `Log.logWith`.  `ix` is the high word of
`|x|`.  An infinity or NaN gives `x + x`. -/
def asinhWith (tab tab2 : Array UInt64) (x : Float) : Float :=
  let ln2 := Float.ofBits 0x3FE62E42FEFA39EF   -- 6.93147180559945286227e-01
  let huge := Float.ofBits 0x7E37E43C8800759C  -- 1.0e+300
  let hx := x.toBits >>> 32
  let ix := hx &&& 0x7fffffff
  if ix ≥ 0x7ff00000 then x + x
  else if ix < 0x3e300000 && huge + x > 1.0 then x
  else
    let w :=
      if ix > 0x41b00000 then Log.logWith tab tab2 x.abs + ln2
      else if ix > 0x40000000 then
        let t := x.abs
        Log.logWith tab tab2 (2.0 * t + 1.0 / ((x * x + 1.0).sqrt + t))
      else
        let t := x * x
        Log1p.log1p (x.abs + t / (1.0 + (1.0 + t).sqrt))
    if hx >>> 31 == 0 then w else -w

/-- fdlibm's `acosh` with the tables `tab` and `tab2` of `Log.logWith`.  `hx` is the high word of
`x` and `lx` its low word: a negative `x` or one below 1 gives NaN, an infinity or NaN `x + x`. -/
def acoshWith (tab tab2 : Array UInt64) (x : Float) : Float :=
  let ln2 := Float.ofBits 0x3FE62E42FEFA39EF   -- 6.93147180559945286227e-01
  let hx := x.toBits >>> 32
  let lx := x.toBits &&& 0xFFFFFFFF
  if hx >>> 31 == 1 || hx < 0x3ff00000 then (x - x) / (x - x)
  else if hx ≥ 0x41b00000 then
    if hx ≥ 0x7ff00000 then x + x else Log.logWith tab tab2 x + ln2
  else if ((hx - 0x3ff00000) ||| lx) == 0 then 0.0
  else if hx > 0x40000000 then
    let t := x * x
    Log.logWith tab tab2 (2.0 * x - 1.0 / (x + (t - 1.0).sqrt))
  else
    let t := x - 1.0
    Log1p.log1p (t + (2.0 * t + t * t).sqrt)

/-- fdlibm's `atanh`.  `ix` is the high word of `|x|` and `lx` the low word of `x`, and the NaN
test is fdlibm's: `(lx | -lx) >> 31` is 1 when the low word is not 0.  The result is computed at
`|x|`, which `SET_HIGH_WORD` forms, and takes the sign of `x`. -/
def atanh (x : Float) : Float :=
  let huge := Float.ofBits 0x7E37E43C8800759C  -- 1.0e+300
  let hx := x.toBits >>> 32
  let lx := x.toBits &&& 0xFFFFFFFF
  let ix := hx &&& 0x7fffffff
  if (ix ||| ((lx ||| ((0 - lx) &&& 0xFFFFFFFF)) >>> 31)) > 0x3ff00000 then (x - x) / (x - x)
  else if ix == 0x3ff00000 then x / 0.0
  else if ix < 0x3e300000 && huge + x > 0.0 then x
  else
    let x := Float.ofBits ((ix <<< 32) ||| lx)
    let t :=
      if ix < 0x3fe00000 then
        let t := x + x
        0.5 * Log1p.log1p (t + t * x / (1.0 - x))
      else 0.5 * Log1p.log1p ((x + x) / (1.0 - x))
    if hx >>> 31 == 0 then t else -t

/-- `asinh x`, with the tables `Log.logTable` and `Log.logTable2`. -/
def asinh (x : Float) : Float := asinhWith Log.logTable Log.logTable2 x

/-- `acosh x`, with the tables `Log.logTable` and `Log.logTable2`. -/
def acosh (x : Float) : Float := acoshWith Log.logTable Log.logTable2 x

verified_compile compiled := [Log.logNear1, Log.logCore, Log.logWith, Log1p.log1pTail, Log1p.log1p,
  asinhWith, acoshWith, atanh, asinh, acosh]

end Verified.Examples.Asinh
